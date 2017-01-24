import os
import sys
import getopt
import csv
import tempfile
import json
import itertools
from clean_csvs import remove_blank_lines
from clean_csvs import remove_comments

def generate_warmup_msgs(config_dir, msg_dir):

    temp_config_dir = tempfile.mkdtemp()
    for csvfile in ['Measures.csv', 'Intersections.csv']:
        with open(os.path.join(config_dir, csvfile), 'r') as orig, open(os.path.join(temp_config_dir, csvfile), 'w') as dest:
            dest.write(remove_blank_lines(remove_comments(orig.read())))

    # Read Measures.csv and make a base metric expr for each to install 
    with open(temp_config_dir + "/Measures.csv", 'rb') as f:
        reader = csv.DictReader(f)
        measures = filter(lambda r: not r["PercentBase"], reader)
        measure_exprs = [warmup_msg(measure) for measure in measures]

    query = { 'install_request' : { 'measure_expr': measure_exprs  } }

    if not os.path.exists(msg_dir):
        os.makedirs(msg_dir)    
    msg_filename = msg_dir + "/measure_rules.json"
    msg_file = open(msg_filename, 'w')
    msg_file.write(json.dumps(query))
    msg_file.close()

def warmup_msg(measure):
    return { 
        'kind' : 'METRIC',
        'metric' : { 'name' : measure["Measure"] }
    }

def main(argv=None):
    if argv is None:
        argv = sys.argv
    try:
        opts, args = getopt.getopt(argv[1:], "h", ["help"])
    except getopt.error, msg:
        print msg
        print "for help use --help"
        sys.exit(2)
    for o, a in opts:
        if o in ("-h", "--help"):
            print "py generate_warmup_from_config.py CONFIG_DIR MSG_DIR"
            print "CONFIG_DIR: directory containing configuration csv's"
            print "MSG_DIR: directory to place generated warmup requests"
            sys.exit(0)

    config_dir = args[0]
    msg_dir = args[1]

    generate_warmup_msgs(config_dir, msg_dir)

if __name__ == '__main__': main()
