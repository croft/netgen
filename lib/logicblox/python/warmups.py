#!/usr/bin/env python

import sys
import os
import time
import argparse
import subprocess
import tempfile
import generate_warmup_from_config
import shutil

sys.path.insert(0, '%s/lib/python' % os.environ.get('LOGICBLOX_HOME'))
sys.path.insert(0, '%s/lib/python' % os.environ.get('LB_WEBSERVER_HOME'))

import lb.web.service


def my_check_call(command):
    if command is not None:
        print 'Run command: %s\n' % command
        subprocess.check_call('time ' + command, shell=True)


def call_rule_warmup(lb_web_client, path):
    print "info: running warmup", path
    sys.stdout.flush()

    with open(path, "r") as istream:
        req = istream.read()

    begin = time.time()
    res = lb_web_client.call_json(req)
    end = time.time()
    dur = end - begin

    simplename = os.path.splitext(os.path.basename(path))[0]
    # This is used by the benchmarks. Do not change the format.
    print "#REPORT#", "warmup-%s" % ','.join(map(str, [simplename, begin, end, dur]))
    sys.stdout.flush()


def warmup_rules(measure_service_uri):
    client = lb.web.service.Client("localhost", 55183, measure_service_uri)
    warmupmsg_dir = tempfile.mkdtemp()
    rule_warmup_file = os.path.join(warmupmsg_dir, 'measure_rules.json')

    has_error = False
    generate_warmup_from_config.generate_warmup_msgs('src/config', warmupmsg_dir)
    try:
        call_rule_warmup(client, rule_warmup_file)
    except Exception as e:
        has_error = e
    finally:
        shutil.rmtree(warmupmsg_dir)

    if has_error:
        print e
        exit(1)


def main(argv=None):
    parser = argparse.ArgumentParser(description='Warmup rules and views')
    parser.add_argument(
        'app_prefix',
        help='prefix for services for an application (portion of url after the hostname and port)')
    parser.add_argument('--workbook')
    args = parser.parse_args()

    if args.workbook:
        app_prefix = '%s/workbook-%s' % (args.app_prefix, args.workbook)
    else:
        app_prefix = args.app_prefix

    measure_service_uri = "/" + app_prefix + "/measure"

    warmup_rules(measure_service_uri)

if __name__ == '__main__':
    main()
