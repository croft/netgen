import os
import tempfile
from lbconfig.api import *

layerblox_path=os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))


#simplistic entry point to enable generation of the assembly spec
#takes a shell command which produces the spec on stdout and the file to store the spec in
def generate_assembly(assembly,call):
    emit_clean_file(assembly)
    subprocess.call( '%s > %s'%(call,assembly), shell=True)
    

#produces  
#    -rules to generate lb projects with layerblox
#    -rules to compile those
def assembly(assembly,deps):
    
    rule( output = '$(gen)',
          input = [ assembly],
      commands = [ 'LAYERBLOX_HOME=$(layerblox) $(layerblox)/bin/layerblox generator %s'%assembly ],
      description = 'Generating libraries from layered assembly spec'
    )

    config_file = tempfile.mkstemp(dir = "/tmp")[1]

    path = "%s/bin/layerblox" % layerblox_path
    print "path to layerblox: %s" %path
    ret = subprocess.Popen([path,"configurehelper",assembly,config_file],
                                         stdout=subprocess.PIPE).communicate()
    print ret[0]
    print ret[1]

    #declare the expected libraries
    with open(config_file) as f:
        for line in f:
            words=line.strip().split(',')
            if(len(words)>=2):
                lb_library( name= words[0], srcdir = words[1], deps = deps, generated=True)
    #add rules for dependencies
    with open(config_file) as f:
        for line in f:
            words=line.strip().split(',')
            if(len(words)>=2):
                rule(output = core.g_projects.get(words[0]).summary_file,input=['$(gen)'])
                for dep in words[2:]:
                    rule(
                        output = core.g_projects.get(words[0]).summary_file,
                        input = [core.g_projects.get(dep).summary_file,'$(gen)'])
    os.remove(config_file)
                
#
# PURE EVIL we need to reparse the arguments 
#
def get_cl_arg(arg):
    import sys
    for raw in sys.argv:
        if raw.startswith('--with-'):
            if raw.split('=')[0][7:]==arg:
                return  raw.split('=')[1]
    return None
