import sys
import os
import time
import argparse

sys.path.insert(0, '%s/lib/python' % os.environ.get('LOGICBLOX_HOME'))
sys.path.insert(0, '%s/lib/python' % os.environ.get('LB_WEBSERVER_HOME'))

import lb.web.service


def read_files(filenames):
    reqs = []
    for filename in filenames:
        with open(filename, "r") as istream:
            reqs.append(istream.read())

    return '{"config": [%s]}' % ','.join(reqs)


def call_client(lb_web_client, filenames):
    print "info: loading %s" % ','.join(filenames)
    sys.stdout.flush()

    req = read_files(filenames)

    begin = time.time()
    res = lb_web_client.call_json(req)
    end = time.time()
    dur = end - begin

    simplename = os.path.splitext(os.path.basename(lb_web_client.path))[0]
    # This is used by the benchmarks. Do not change the format.
    print "#REPORT#", str(simplename) + "," + str(begin) + "," + str(end) + "," + str(dur)
    sys.stdout.flush()


def load(path,file_names):
    client = lb.web.service.Client("localhost", 55183, path)
    call_client(client, file_names)

def import_views(viewpath, project, workbook):
    views = []
    
    for root, path, files in os.walk(os.path.join(os.getcwd(), viewpath)):
        for fname in files:
            if (not fname.startswith(".")) and fname.endswith(".json"):
                views.append(os.path.join(root, fname))
    if not workbook:
        load("/" + project + "/views", views)
    else:
        try:
            load("/" + project + "/" + "workbook-" + workbook + "/views", views)
        except lb.web.service.HttpClientError:
            print("Error: Workbook ID '" + workbook + "' not found!")
            return;

def main(argv=None):
    parser = argparse.ArgumentParser(description='Load Sheets, Canvases, Actions, and Navtree')
    parser.add_argument('project', metavar='PROJECT', type=str, help='Project name to use in web service calls.')
    parser.add_argument('--workbook', type=str, default="", help='Workbook ID to use in web service calls.')
    parser.add_argument('--canvas-only', action='store_true', default=False, help='Add canvas configuration only')
    parser.add_argument('--sheets-only', action='store_true', default=False, help='Add sheets configuration only')
    parser.add_argument('--actions-only', action='store_true', default=False, help='Add actions configuration only')
    parser.add_argument('--nav-only', action='store_true', default=False, help='Add navigation trees configuration only')
    parser.add_argument('--sheets-path', default='src/config/sheets/')
    parser.add_argument('--canvas-path', default='src/config/canvas/')
    parser.add_argument('--nav-path', default='src/config/navigation/')
    parser.add_argument('--actions-path', default='src/config/actions/')
    
    args = parser.parse_args()

    load_all = not ( args.canvas_only or args.sheets_only or args.actions_only or args.nav_only )

    project = args.project
    workbook = args.workbook
    navtrees = []
    actions = []

    if load_all or args.sheets_only:
        import_views(args.sheets_path, project, workbook)

    if load_all or args.canvas_only:
        import_views(args.canvas_path, project, workbook)
        
    if load_all or args.nav_only:
        navPath = args.nav_path
        for root, path, files in os.walk(os.path.join(os.getcwd(), navPath)):
            for fname in files:
                if (not fname.startswith(".")) and fname.endswith(".json"):
                    navtrees.append(os.path.join(root, fname))
        if not workbook:
            load("/" + project + "/navtree-batch", navtrees)
        else:
            try:
                load("/" + project + "/" + "workbook-" + workbook + "/navtree", navtrees)
            except lb.web.service.HttpClientError:
                print("Error: Workbook ID '" + workbook + "' not found!")
                return;

    if load_all or args.actions_only:
        actPath = args.actions_path
        for root, path, files in os.walk(os.path.join(os.getcwd(), actPath)):
            for fname in files:
                if (not fname.startswith(".")) and fname.endswith(".json"):
                    actions.append(os.path.join(root, fname))
        if not workbook:
            load("/" + project + "/actions-batch", actions)
        else:
            try:
                load("/" + project + "/" + "workbook-" + workbook + "/actions", actions)
            except lb.web.service.HttpClientError:
                print("Error: Workbook ID '" + workbook + "' not found!")
                return;

if __name__ == '__main__':
    main()
