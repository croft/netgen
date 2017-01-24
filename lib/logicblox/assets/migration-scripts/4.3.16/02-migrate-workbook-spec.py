import sys,os,json,exceptions
folder = sys.argv[1]

for dirpath,dirnames,filenames in os.walk(folder):
    for f in filenames:
        candidate = os.path.join(dirpath,f)
        with open(candidate) as open_candidate:
            maybe_json = open_candidate.read()
        workbook = None
        try:
            workbook = json.loads(maybe_json)
        except:
            # not a json file, do nothing
            continue
        #if this is true we check whether this json is a workbook spec
        #which needs to be patched
        if workbook is not None:
            if 'olap_model' in workbook:
                om = workbook['olap_model']
                if 'measures' in om:
                    measures= om['measures']
                    del workbook['olap_model']['measures']
                    workbook['olap_model']['measure_access'] ={'measures':measures}
                    print "migrating %s"%candidate
                    with open(candidate,'w') as open_candidate:
                        open_candidate.write(json.dumps(workbook,indent=2))
            
