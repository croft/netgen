#!/usr/bin/env python

import sys
import json
import csv
import os
import StringIO
import argparse
import uuid

sys.path.insert(0, '%s/lib/python' % os.environ.get('LOGICBLOX_HOME'))
sys.path.insert(0, '%s/lib/python' % os.environ.get('LB_WEBSERVER_HOME'))

import lb.web.service
import dbcommands.lb_command

import clean_csvs
import generate_schema_from_config


def lb_add_block(ws, name, logic):
    """Execute given inactive block, returning nothing.

    Caution: this command will only work locally, because it uses
    ConnectBlox directly.

    @param ws: Workspace in which to execute
    @param block: Inactive block to execute
    @return the result of the connectblox command
    """
    cmd = dbcommands.lb_command.AddBlockCommand(name, ws, logic=logic)
    result = cmd.run()
    return result


def find_new_metrics(metrics, existing_metrics):
    return filter(lambda m: m not in existing_metrics, metrics)


def read_metrics(filename):
    with open(filename) as f:
        clean_text = clean_csvs.remove_blank_lines(clean_csvs.remove_comments(f.read()))
        csv_reader = csv.DictReader(StringIO.StringIO(clean_text))
        return [m['Measure'] for m in csv_reader]


def fetch_model():
    client = lb.web.service.Client('localhost', 55183, '/target-ap/measure')
    resp = json.loads(client.call_json(json.dumps({"model_request": {}})))
    return resp['model']


def get_metrics(model):
    return [m['name'] for m in model['metric']]


def install_metrics(new_metrics, config_dir, workspace):
    generate_schema_from_config.make_measure_declarations(
        config_dir, '.', measures_to_process=new_metrics)

    with open('./measures.logic') as f:
        logic = f.read()
        lb_add_block(workspace, uuid.uuid1().hex, logic)


def add_metrics(config_dir, workspace):
    metrics = read_metrics(os.path.join(config_dir, 'Measures.csv'))
    model = fetch_model()

    new_metrics = find_new_metrics(metrics, get_metrics(model))
    print 'Adding metrics ', new_metrics
    install_metrics(new_metrics, config_dir, workspace)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('config_dir')
    parser.add_argument('workspace')
    args = parser.parse_args()

    add_metrics(args.config_dir, args.workspace)
