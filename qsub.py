#!/usr/bin/env python

# Copyright (c) 2008 Blair Bethwaite
#
# Permission is hereby granted, free of charge, to any person
# obtaining a copy of this software and associated documentation
# files (the "Software"), to deal in the Software without
# restriction, including without limitation the rights to use,
# copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the
# Software is furnished to do so, subject to the following
# conditions:
#
# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
# OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
# HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
# WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
# FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
# OTHER DEALINGS IN THE SOFTWARE.

__doc__=\
"""This script is meant as a transparent drop in between clients of qsub and
the real qsub binary for Sun Grid Engine 6.1. It's purpose is to add options
to a submission based on information that SGE does not currently consider, thus
making it possible for complexes and limits to be requested implicitly, which
currently does not have direct support in SGE. It also modifies the submission
environment to satisfy user access lists attached to queues or projects, i.e.
changes the primary group of the parent process so that SGE recognises
membership - for some reason SGE does not consider supplementary groups.

Specifically this script:
1. Looks up the users group memberships and maps any arguments configured below.
2. Parses requests for specific queues into complex or limit requests, thus
effectively creating virtual queues.
3. Checks the new qsub arguments for queue requests and makes sure the users
primary group matches any acl on the requested queue - if possible. This is
achieved using the standard *nix newgrp command as a subprocess."""

import sys, os, os.path, stat, pwd, grp, time
import subprocess, commands, select, fcntl
import re, logging

## Set the location of the real qsub binary here.
#
qsub_real = '/opt/sge-6.2u4/bin/lx24-amd64/qsub.real'

## Add argument mappings for groups here.
#    Empty args have no effect.
#    It is not necessary to provide a mapping for every group.
#
# e.g.:
# group_arg_map = {
# 'MESSAGE-Lab':['-P messagelab'],
# 'Monash':[],
# 'PRAGMA':[],
# }
group_arg_map = {
}

## Define _Python_ regular expressions here which match queue names and define
#    groupings that capture option values needed to be passed to qsub.
#    Each virtual queue regex should be the first element in a list with
#    subsequent elements defining the qsub option that matches each named
#    group in the regex. Most matches will probably only define one option,
#    though this is not necessarily the case.
#    You can define subpatterns and reuse them in multiple virtual queue
#    definitions.
#    The r prefix in some of the examples below denotes a python raw string,
#    which is not subject to regular python string formatting rules.
#    The matching will be case _insensitive_, however!, case will still be
#    captured by the grouping and so passed to qsub - the upshot of this is
#    that SGE units (e.g. memory) which are case sensitive can be passed
#    through.
#    Each regex will be tried for any queue specification and results appended
#    to qsub arguments, so it is possible define a virtual queue syntax that
#    specifies multiple options very consisely.
#    Note that you should explicitly match the whole queue name
#
#    Comment your regexes liberally!!
#
VQ_SEPARATOR = ';?'
# match octal, hex, or decimal integers
RE_INT = '([-+]?(0[xX][\dA-Fa-f]+|0[0-7]*|\d+))'
# this matches the time type format, i.e. a single integer value indicating
# seconds or three decimal values seperated by ':' indicating hrs:mins:secs
RE_SGE_TIME = '(%s(:[0-9]{0,2}:[0-9]{0,2})?)' % RE_INT
RE_SGE_MEM  = '(%s[kKmMgG])' % RE_INT
RE_INT_RANGE = '(%s(-%s)?)' % (RE_INT, RE_INT)
RE_LOCAL_ALPHA_STRING = '(\w+)'

virtual_queues = {
# virtual memory limit
'mem(?P<n>%s)' % RE_SGE_MEM
:['-l h_vmem=\g<n>'],
# wall time limit 
'wall(?P<n>%s)' % RE_SGE_TIME
:['-l h_rt=\g<n>'],
# job needs a parallel environment, e.g.: pe=smp:8, pe=openmpi:4-16
'pe=(?P<pe>[_a-z]+(%s)?):(?P<nm>%s)' % (RE_INT,RE_INT_RANGE)
:['-pe \g<pe> \g<nm>'],
# route job to hostgroup
'quads'
:["-q *@@quads"],
'duals'
:["-q *@@duals"],
# add context/metadata information to the job
# Careful - this regex will greedy match, so should appear last in the vq
'c=(?P<comment>%s)' % RE_LOCAL_ALPHA_STRING
:['-ac comment=\g<comment>'],
'\[(?P<comment>%s)\]' % RE_LOCAL_ALPHA_STRING
:['-ac \g<comment>'],
'matlab'
:['-l matlab=1 -soft -l matlab_running=TRUE']
}

## SGE qconf commands for resolving ACLs
#
qconf_get_queue = '/opt/sge-6.2u4/bin/lx24-amd64/qconf -sq %s'
qconf_get_userlist = '/opt/sge-6.2u4/bin/lx24-amd64/qconf -su %s'
qconf_get_project = '/opt/sge-6.2u4/bin/lx24-amd64/qconf -sprj %s'

# Acknowledgement:
# http://rightfootin.blogspot.com/2006/09/more-on-python-flatten.html
def flatten(l, ltypes=(list, tuple)):
    i = 0
    while i < len(l):
        while isinstance(l[i], ltypes):
            if not l[i]:
                l.pop(i)
                if not len(l):
                    break
            else:
                l[i:i+1] = list(l[i])
        i += 1
    return l

def fs(l):
    l = flatten(l)
    i = 0
    while i < len(l):
        if len(l[i].split()) > 1: # contains whitespace
            l[i] = l[i].split()
        i += 1
    return flatten(l)

# Either add, remove, or edit, option in args
# remove indicates whether the option should be removed - if arg
# matches the options argument it is also removed.
# add indicates whether the option should be added to the existing args.
# if add is False and the option is already in args it is edited in place,
# otherwise it is added
def add_del_ed_opt(opt, arg, args, remove=False, add=False):
    logging.debug("add_del_ed_opt start: %s" % args)
    # removing an option and possibly it's argument
    if remove and (opt in args):
        logging.debug("%s == %s ?" % (arg, args[args.index(opt)+1]))
        if arg == args[args.index(opt)+1]:
            logging.debug("opt and arg")
            # +2 below because end of slice is an exclusive bound
            del args[args.index(opt):args.index(opt)+2]
        else:
            logging.debug("opt")
            del args[args.index(opt)]
    # adding and option and possibly it's argument
    elif add or (opt not in args):
        args = args + opt
        if arg:
            args = args + arg
    # editing an options argument
    elif opt in args:
        args[args.index(opt)+1] = arg
    logging.debug("add_del_ed_opt end: %s" % args)

def get_group_args(groups):
    new_args = []
    logging.debug("adding group arguments")
    for group in groups:
        if group_arg_map.has_key(group):
            logging.debug("added (%s) for group %s" %\
                (group_arg_map[group], group))
            new_args += group_arg_map[group]
    return fs(new_args)

def resolve_virt_queues(queue):
    new_args = []
    logging.debug("resolving virtual queue arguments for queue: %s" % queue)
    # add separator to each vq
    for vq in virtual_queues.keys():
        try:
            virtual_queues[vq+VQ_SEPARATOR] = virtual_queues.pop(vq)
        except Exception,e:
            logging.warn("couldn't add vq separator to %s, error: %s" % (e,vq))
            continue
    # use re search and get values from named groupings in the first match
    for vq in virtual_queues.keys():
        try:
            regex = re.compile(vq, re.IGNORECASE)
        except Exception,e:
            logging.warn("couldn't compile regex: %s, error: %s" % (vq,e))
            continue
        match = regex.search(queue)
        if match:
            logging.debug("got vq match on %s - matched: %s" % (vq,match.group()))
            try:
                i = 0
                for template in virtual_queues[vq]:
                    arg = match.expand(template)
                    logging.debug("match expanded to argument: %s" % arg)
                    new_args += [arg]
                    i+=1
            except Exception,e:
                logging.error("error building vq args: %s" % e)
    return fs(new_args)

def extract_queue(args):
    return _queue(args,remove=True)
def get_queue(args):
    queue = _queue(args)[0]
    logging.debug("queue: %s requested" % queue)
    return queue
def _queue(args,remove=False):
    # find the queue that was requested and return a tuple containing
    # the queue and the argument list minus the queue request
    if '-q' in args:
        logging.debug("_queue found queue specifier")
        queue = args[args.index('-q')+1]
        logging.debug(queue)
        if ',' in queue:
            logging.warn("can't process queue request as virtual queue "\
                "because it contains multiple queues")
            return (None, args)
        if not remove:
            return (queue, args)
        # del args[args.index('-q'):args.index('-q')+2]
        add_del_ed_opt('-q', args[args.index('-q')+1], args, remove=True)
        return (queue, args)
    # return (None,args) if no queue or error
    return (None, args)

# take output of qconf -s* (show) and parse into dict for programmatic access
def qconf_parse(output):
    output = output.splitlines()
    r = re.compile(r'[,\s]') # match whitespace or coma
    output = [r.split(line) for line in output]
    # now we have a list of lists, but it may contain empty strings
    for line in output:
        while '' in line:
            line.remove('')
    # turn into dict and return
    return dict([(line[0],line[1:]) for line in output])

def resolve_queue_access(queue, user, groups, args):
    (s,o) = commands.getstatusoutput(qconf_get_queue % queue)
    if s != 0:
        logging.error("Couldn't run qconf: %s" % o)
    else:
        q = qconf_parse(o)
        # look for allowed users and projects
        logging.debug("qconf for %s has user_lists: %s, projects: %s"\
            % (queue,q['user_lists'],q['projects']))
        if q['user_lists'][0] != 'NONE':
            # find first user_list the calling user is in, if any
            for l in q['user_lists']:
                (s,o) = commands.getstatusoutput(qconf_get_userlist % l)
                assert s == 0 # this would be an error in sge config
                u = qconf_parse(o)
                logging.debug("user_list %s: %s" % (l,u['entries']))
                # check that this user isn't already directly in the list
                if user in u['entries']:
                    return
                for entry in u['entries']:
                    if entry[0] == '@' and (entry[1:] in groups.keys()):
                        logging.debug("group: %s of userset: %s satisfies "\
                            "queue: %s" % (entry[1:],l,queue))
                        #os.setgid(groups[entry[1:]])
                        return entry[1:]
        # no luck in users, perhaps projects (this will only work if
        # allow user list was empty because it is exclusive.
        # we also need to check whether there was already a project with
        # access to this queue specified and if so attempt to satisfy the acl
        # of that project rather than just the first satisfiable acl we find
        elif q['projects'][0] != 'NONE':
            # need extra vars as we have to look at all acls in all projects
            rq_prj,new_prj,new_group = None,None,None
            user_in_prj = False
            # check whether a project was already specified
            if '-P' in args:
                rq_prj = args[args.index('-P')+1]
                logging.debug("got project:%s, and queue:%s request"%\
                    (rq_prj,queue))
            for prj in q['projects']:
                (s,o) = commands.getstatusoutput(qconf_get_project % prj)
                assert s == 0 # this would an error in sge config
                acl = qconf_parse(o)['acl']
                logging.debug("project %s: %s" % (prj,acl))
                for l in acl:
                    (s,o) = commands.getstatusoutput(qconf_get_userlist % l)
                    assert s == 0
                    u = qconf_parse(o)
                    logging.debug("user_list %s: %s" % (l,u['entries']))
                    for entry in u['entries']:
                        if user == entry:
                            user_in_prj = True
                            new_prj = prj
                            logging.debug("user in acl satisfying project:%s"%\
                                new_prj)
                            if rq_prj == new_prj:
                                # don't need to do anything
                                return
                        elif entry[0] == '@' and entry[:1] in groups.keys():
                            user_in_prj = False
                            new_prj = prj
                            new_group = entry[:1]
                            logging.debug("found group:%s membership "\
                                "satisfying project:%s" % \
                                (new_group,new_prj))
                            if rq_prj == new_prj:
                                # change group to satisfy project
                                #os.setgid(groups[new_group])
                                return new_group
            # we've looked at all the projects attached to the queue.
            # if there was already a project specified and it's attached
            # to the queue (and the user is a member) then we didn't need
            # to do anything, except maybe change group.
            # the final complication to resolve is if we found a project
            # which will satisfy the queue request but there was already
            # a project specified which did not satisfy the queue request - 
            # in this case we'll override the previous project to satisfy the
            # queue
            if rq_prj and new_prj:
                # we're going to change requested project so warn
                logging.warn("couldn't satisfy queue:%s request with "\
                    "existing project:%s specification but found project"\
                    " that does, existing project will be overriden"%\
                    (queue,rq_prj))
            if new_prj:
                add_del_ed_opt('-P', new_prj, args)
                if not user_in_prj:
                    # found a project satisfying the queue but need to change
                    # group first for membership
                    #os.setgid(groups[new_group])
                    return new_group

def parse_job_script(cmd_ln_args):
    # we need to find the job script being passed to qsub.
    # unfortunately SGE doesn't use standard GNU format command line options
    # so they cannot be parsed in the standard fashion.
    # qsub flags are prefixed with a '-' and might have arguments, which could
    # be paths in some cases. the qsub cmd line has the format:
    # qsub [ options ] [ command | -- [ command_args ]]
    # so we are looking for the first argument that is a path to an existing
    # file but does not follow one of the flags that take a path argument.
    qsub_path_flags = ['-i','-e','-o','-S']
    job_script_path = None
    # find script file in args and open:
    for arg in cmd_ln_args:
        if (not arg[0] == '-') and os.path.isfile(arg):
            if cmd_ln_args[cmd_ln_args.index(arg)-1] not in qsub_path_flags:
                job_script_path = arg
    try:
        job_file = open(job_script_path)
    except IOError,e:
        logging.error("couldn't open SGE job script: %s, error :%s"%\
            (job_script_path,e))
        raise
    # parse qsub flags from job script:
    if '-C' in cmd_ln_args:
        prefix = cmd_ln_args[cmd_ln_args.index('-C')+1]
    else:
        prefix = r'#$'
    file_options = []
    for line in job_file:
        if line.startswith(prefix):
            # this is an option/flag line and should contain a single switch
            # or a switch and argument
            options = line[len(prefix):].split() # remove the prefix, break on ws
            file_options += options
    logging.debug("parsed job script file, found options: %s" % file_options)
    job_file.close()
    return (job_script_path, prefix, file_options)

# if the a virtual queue request is contained in the job script we need
# to remove it prior to passing on to qsub_real, as it won't know about that
# queue.
# we'll add some metadata indicating this job was affected by a virtq request
# and how it resolved
def rm_q_job_script(js_path, js_prefix):
    try:
        fr = open(js_path,'r')
        lines = fr.readlines()
        fr.close()
        logging.debug("read job script:\n%s\nremoving queue..." % lines)
        # attempt to backup job script prior to alteration
        try:
            backup_path = js_path + '.bkup%s' % time.time()
            fb = open(backup_path,'w')
            fb.writelines(lines)
            fb.close()
        except IOError,e:
            logging.warn("error occured attempting to backup job script: %s"%e)
        edit = False
        qre = re.compile(r'-q\s+\S+')
        i = 0
        while i < len(lines):
            if lines[i].startswith(js_prefix) and qre.search(lines[i]):
                lines[i] = qre.sub('',lines[i])
                edit = True
            i += 1
        if edit:
            fw = open(js_path,'w')
            fw.writelines(lines)
            logging.debug("wrote:\n%s\n back to job script" % lines)
            # make sure internal buffers are flushed
            fw.flush()
            # and file has made it to disk
            os.fsync(fw)
            fw.close()
        # altered script written back, now remove backup
        try:
            if os.path.isfile(backup_path):
                os.remove(backup_path)
        except IOError,e:
            logging.warn("errored occured during backup job script removal: %s"%e)
            
    except IOError,e:
        logging.error("couldn't open SGE job script: %s, error :%s"%(js_path,e))
        raise

def error_exit(msg):
    logging.error(msg)
    print >>sys.stderr, msg
    sys.exit(1)

# if we're not setuid then os.setgid will have failed, now we try falling
# back to the *nix newgrp command.
def qsub_child(new_grp,new_args):
    logging.debug("launching qsub_real via newgrp %s" % new_grp)
    timeout = 20
    PIPE = subprocess.PIPE
    try:
        child = subprocess.Popen(['/usr/bin/newgrp',new_grp],stdin=PIPE,\
            stdout=PIPE,stderr=PIPE,bufsize=0,env=os.environ)
        if child.poll() != None: # make sure child is running
            logging.error("child finished unexpectedly, can't change group!")
            return False
        cin,cout,cerr = child.stdin,child.stdout,child.stderr
        # make cout,cerr non-blocking
        for f in (cout,cerr):
            flags = fcntl.fcntl(f, fcntl.F_GETFL)
            fcntl.fcntl(f, fcntl.F_SETFL, flags|os.O_NONBLOCK)
        _,wrs,_ = select.select([],[cin],[],timeout) # ready for input?
        if wrs:
            cmd = qsub_real
            new_args = flatten(new_args)
            for arg in new_args:
                cmd = cmd + ' ' + arg
            cin.write(cmd+'\n')
            #logging.debug("wrote to child, command: %s" % cmd)
        else:
            logging.error("child not ready for input")
            return False
        rds,_,_ = select.select([cout],[],[],timeout) # output ready?
        if not rds: # maybe error?
            rds,_,_ = select.select([cerr],[],[],1) # error ready?
            if not rds:
                error_exit("IPC error (qsub return code unavailble), "\
                    "submission status unavailable, no stderr")
            else:
                # there is some stderr to read (and pass on)
                while rds:
                    line = cerr.readline()
                    os.write(sys.stderr.fileno(), line)
                    rds,_,_ = select.select([cerr],[],[],timeout)
        else:
            # read and echo qsub output
            while rds:
                line = cout.readline()
                logging.debug("qsub output: %s" % line)
                os.write(sys.stdout.fileno(),line)
                rds,_,_ = select.select([cout],[],[],timeout)
        # get qsub return code
        _,wrs,_ = select.select([],[cin],[],1) # ready for input?
        if wrs:
            cin.write('echo $?\n')
        else:
            error_exit("IPC error (qsub return code unavailble), "\
                "job may have been submitted, no wrs")
        rds,_,_ = select.select([cout],[],[],timeout) # output ready?
        if rds:
            line = cout.readline()
            retcode = int(line)
            logging.info("qsub exited: %d" % retcode)
            sys.exit(retcode)
        else: # don't bother checking cerr, we have to fail anyway
            error_exit("IPC error (qsub return code unavailble), "\
                "submission status unavailable, no rds")
    except IOError,e:
        error_exit("IPC error (caught exception: %s), "\
            "submission status unavailable" % e)        
def init():
    user = pwd.getpwuid(os.getuid())[0]
    logfile = '/tmp/qsub-%s.log' % user
    logging.basicConfig(level=logging.DEBUG,
        format='%(asctime)s %(levelname)s: %(message)s',
        filename=logfile,
        filemode='a')
    # make sure log is writable by all if it has just been created
    os.chmod(logfile,stat.S_IRUSR|stat.S_IWUSR|stat.S_IRGRP|\
                             stat.S_IWGRP|stat.S_IROTH|stat.S_IWOTH)
    logging.debug("qsub wrapper started...")

if __name__=='__main__':
    try:
        init()
        # copy by value to leave argv in place
        cl_args = list(sys.argv[1:])
        name = sys.argv[0]
        js_path, js_prefix, js_opts = parse_job_script(cl_args)
        logging.debug("cmd line args: %s\njob script options: %s"\
            % (cl_args,js_opts))
        logging.debug("configuration: group argument mapping: %s , "\
            "virtual queues: %s" %\
            (group_arg_map, virtual_queues))
        user = pwd.getpwuid(os.getuid())[0]
        groups = dict([(grp.getgrgid(gid)[0],grp.getgrgid(gid)[2])\
            for gid in os.getgroups()])
        logging.debug("user: %s, groups: %s" % (user,groups))
    
        #1
        grp_opts = get_group_args(groups)
        #2
        queue = None
        if get_queue(cl_args): # cmd line options override embedded
            # nb. '-q qname' is removed by extract_queue
            (queue,cl_args) = extract_queue(cl_args)
        elif get_queue(js_opts):
            queue = get_queue(js_opts)
        logging.debug("queue: %s" % queue)
        if queue:
            vq_opts = resolve_virt_queues(queue)
            if vq_opts: # there was a vq match
                # add some metadata to the job context re virtq
                context = "virtq=%s,virtq_resolution=\"" % queue
                for opt in vq_opts:
                    context += "%s " % opt
                context = [ "-ac", context + "\"" ]
                new_args = grp_opts + vq_opts + context + cl_args
                # check whether there is a new queue request after vqs
                if get_queue(new_args):
                    queue = get_queue(new_args)
                else:
                    queue = None
                rm_q_job_script(js_path, js_prefix)
            else: # no vq match so pass on original request
                new_args = grp_opts + sys.argv[1:]
        else:
            new_args = grp_opts + sys.argv[1:]
        #3
        new_grp = None
        if queue:
            logging.debug("resolving queue access...")
            try:
                new_grp = resolve_queue_access(queue, user, groups, new_args)
                if new_grp:
                    try:
                        os.setgid(groups[new_grp])
                        new_grp = None
                    except OSError:
                        pass
            except Exception, e:
                # Can get an error here when queue is actually a host group
                # e.g., "*@@quads" as this returns info for every matching
                # host
                logging.exception("exception resolving queue access: %s" % e)
        
        logging.debug("new argument list: %s" % new_args)
        if new_grp: # change group with newgrp
            qsub_child(new_grp,new_args) # remove executable name
        else:
            os.execvp(qsub_real,flatten([name]+new_args))
    except StandardError,e:
        if len(sys.argv) > 1:
            print >>sys.stderr, "Error in qsub wrapper: %s" % e
        os.execvp(qsub_real,sys.argv)
