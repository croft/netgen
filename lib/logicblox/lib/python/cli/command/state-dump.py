"""
Copyright 2013 LogicBlox, Inc.

All rights reserved.

Redistribution and use in source and binary forms, with or 
without modification, are permitted provided that the following 
conditions are met:

Redistributions of source code must retain the above copyright 
notice, this list of conditions and the following disclaimer.

Redistributions in binary form must reproduce the above copyright 
notice, this list of conditions and the following disclaimer 
in the documentation and/or other materials provided with the 
distribution.

Neither the name of LogicBlox nor the names of its contributors 
may be used to endorse or promote products derived from this 
software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS 
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT 
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS 
"""

import os
import shutil
import stat
import tarfile
import datetime
import logging
import cli

# default error message (may change)
ERROR_MSG = 'WARNING: psutil python module is not installed. Please install and set PYTHONPATH if needed.'
HAVE_PSUTIL = False
try:
    import psutil
    HAVE_PSUTIL = True
except ImportError:
    pass

if HAVE_PSUTIL:
    import state_dump

def add_commands(parser, subparsers):
    """

        Add this command to the main parser.
    """
    subparser = subparsers.add_parser('state-dump', help='dump whole server state' + (' (requires psutil python module, not installed)' if not HAVE_PSUTIL else ''))
    subparser.add_argument(
            'directory',
            metavar='dir',
            nargs='?',
            default='status',
            help='the directory to dump the server state into',
            )
    subparser.add_argument(
            '--full-journal',
            action='store_true',
            help='whether to dump the full journal state',
            )
    subparser.add_argument(
            '--log-level',
            dest='log_level',
            default='INFO',
            choices=[level for level in logging._levelNames.iterkeys() if isinstance(level, basestring)],
            help='the logging level',
            )
    subparser.set_defaults(func=(main if HAVE_PSUTIL else no_psutil))

def chmod_r(path, mode):
    st = os.stat(path)
    os.chmod(path, mode | stat.S_IMODE(st.st_mode))
    if stat.S_ISDIR(st.st_mode):
        [ chmod_r('%s/%s' % (path,entry), mode) for entry in os.listdir(path) ]

def main(args):
    logging.basicConfig(level=logging._levelNames[args.log_level])

    if os.geteuid() != 0:
        raise Exception("State dump needs to be run as root!")

    dirname = '%s-%s' % (args.directory,datetime.datetime.utcnow().strftime("%Y%m%d-%H%M%S"))
    shutil.rmtree(dirname, True)
    os.mkdir(dirname)
    state_dump.check_lb_status(dirname)
    state_dump.collect_procinfo(dirname)
    state_dump.collect_sysinfo(dirname, full_journal=args.full_journal)
    state_dump.collect_meminfo(dirname)
    state_dump.collect_netinfo(dirname)
    state_dump.collect_userinfo(dirname)
    chmod_r(dirname, stat.S_IRUSR | stat.S_IRGRP | stat.S_IROTH)
    logging.info("Tarring up results")
    with tarfile.open('%s.tar.bz2' % (dirname), 'w:bz2') as tarball:
        tarball.add(dirname, recursive=True)
    shutil.rmtree(dirname, True)

def no_psutil(args):
    raise cli.lb_exception.LBServerOff(ERROR_MSG)
