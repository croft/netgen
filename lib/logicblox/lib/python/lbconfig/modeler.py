from api import *

'''
lb-config support for building modeler projects

The idea is that projects can configure modeler builds simply by
calling `lbconfig.configure(app-prefix)`.

The resulting make file with then contain targets that can be used to build
up modeler applications. Some targets:

    - view-warmup: generates view warmup queries
    - rule-warmup: generates rule warmup queries
    - warmup-rules: submits rule warmup queries
    - warmup-views: submits view warmup queries

These targets all have a dependency to the modeler sources, so they will
automatically copy over any necessary library or script from the $LB_MODELER_HOME.
'''

# directories where we can find modeler assets and scripts
_default_js_scripts_src_dir = '$(modelerjs)/lib/js'
_default_assets_src_dir = '$(modelerjs)/assets'
_default_js_lib_src_dir = os.path.join(_default_assets_src_dir, 'js')
_default_python_dir = '$(modelerjs)/python'

# directories to where we will copy javascript assets and scripts
_default_js_scripts_dest_dir = 'scripts/js'
_default_js_lib_dest_dir = 'node_modules'

rule_warmup_query_dir = '$(build)/srcgen/rule-warmup'
view_warmup_query_dir = '$(build)/srcgen/view-warmup'

variable('view_query_dir', view_warmup_query_dir)

def configure(app_prefix, app_base_dir='.',
              js_lib_src_dir=_default_js_lib_src_dir,
              js_lib_dest_dir=_default_js_lib_dest_dir,
              assets_dir=_default_assets_src_dir,
              js_scripts_dest_dir=_default_js_scripts_dest_dir,
              js_scripts_src_dir=_default_js_scripts_src_dir,
              python_dir=_default_python_dir):
    '''This is the main configuration target that will configure modeler
    for applications.

    For applications using the platform build, it is not necessary to provide
    paramter values different from the default values.

    @param app_prefix
        The application prefix, e.g., 'your-app'
    @param js_lib_dir
        The directory containing modeler javascript libraries
    @param js_scripts_dir
        The directory containing modeler javascript scripts
    @param python_dir
        The directory containing modeler python scripts
    '''

    assets(assets_dir=assets_dir)
    js_scripts(js_scripts_src_dir=js_scripts_src_dir, js_scripts_dest_dir=js_scripts_dest_dir)
    js_libraries(js_lib_src_dir=js_lib_src_dir, js_lib_dest_dir=js_lib_dest_dir)
    rule_warmup_queries(app_base_dir=app_base_dir, python_dir=python_dir)
    view_warmup_queries(app_prefix, app_base_dir,
                        js_lib_dest_dir=js_lib_dest_dir, js_scripts_dest_dir=js_scripts_dest_dir)
    rule_warmup(app_prefix,
                js_lib_dest_dir=js_lib_dest_dir, js_scripts_dest_dir=js_scripts_dest_dir)
    view_warmup(app_prefix,
                js_lib_dest_dir=js_lib_dest_dir, js_scripts_dest_dir=js_scripts_dest_dir)


def js_libraries(js_lib_src_dir=_default_js_lib_src_dir, js_lib_dest_dir=_default_js_lib_dest_dir):
    '''Copies modeler js libraries to the project dir

    @param js_lib_dir
        The directory from which we will copy the modeler javascript libraries,
        e.g. logicblox.js, logicbloxtestutils.js, from.
    '''

    files = ['logicbloxtestutils.js']
    for f in files:
        _copy_file(f, js_lib_src_dir, js_lib_dest_dir)


def js_scripts(js_scripts_src_dir=_default_js_scripts_src_dir, js_scripts_dest_dir=_default_js_scripts_dest_dir):
    '''Copies modeler js scripts to the project dir

    @param js_scripts_dir
        The directory from which we will copy the modeler javascript scripts,
        e.g. submitqueries.js, generateviewwarmupqueries.js, from.
    '''

    files = ['submitqueries.js',
             'generateviewwarmupqueries.js']

    for f in files:
        _copy_file(f, js_scripts_src_dir, js_scripts_dest_dir)


def assets(assets_dir=_default_assets_src_dir):
    '''Copies modeler html assets to the project dir

    @param assets_dir
        The directory from which we will copy the modeler assets from.
    '''
    rule(output=['frontend/js/logicblox.js'],
         input=[os.path.join(assets_dir, 'js', 'logicblox.js')],
         commands=['mkdir -p frontend',
                   'cp -R %s/* frontend' % assets_dir,
                   'chmod -R a+w frontend'],
         # we needs this to by phony because we can't rely on the date
         # of the assets being newer than in the project's source files
         phony=True)

    rule(
        output='all',
        input=['frontend/js/logicblox.js'])

    install_dir('frontend', 'static')

    rule(
        output='frontend',
        input=['frontend/js/logicblox.js'])


def rule_warmup_queries(app_base_dir, python_dir=_default_python_dir):
    '''Creates 'rule-queries' target that will create a query to
    warm up rules in $(build)/srcgen/rule-warmup/measure_rules.json

    @param python_dir
        The directory containing the modeler python scripts'''

    rule(
        output=[os.path.join(rule_warmup_query_dir, 'measure_rules.json'), 'rule-queries'],
        input='',
        commands=[
            'mkdir -p %s' % rule_warmup_query_dir,
            'python %s/generate_warmup_from_config.py %s/src/config $(build)/srcgen/rule-warmup' % (python_dir, app_base_dir)])

    install_dir(rule_warmup_query_dir, 'build/srcgen/rule-warmup')


def view_warmup_queries(app_prefix, app_base_dir,
                        js_scripts_dest_dir=_default_js_scripts_dest_dir,
                        js_lib_dest_dir=_default_js_lib_dest_dir):
    '''Creates a 'view-queries' target that will create query files
    to warmup up views. Files will be added to $(build)/srcgen/view-warmup

    @param app_prefix
        The application prefix, e.g., 'your-app'
    '''

    variable('canvas_dir', '%s/src/config/canvas' % app_base_dir)

    generate_script = os.path.join(js_scripts_dest_dir, 'generateviewwarmupqueries.js')
    rule(
        output='view-queries',
        input=[
            generate_script,
            os.path.join(js_lib_dest_dir, 'logicbloxtestutils.js')],
        commands=[
            'mkdir -p $(view_query_dir)',
            'node %s --app-prefix %s --config-dir $(canvas_dir) $(view_query_dir)' % (generate_script, app_prefix)])

    install_dir(view_warmup_query_dir, 'build/srcgen/view-warmup')


def view_warmup(app_prefix,
                js_scripts_dest_dir=_default_js_scripts_dest_dir,
                js_lib_dest_dir=_default_js_lib_dest_dir):
    '''Creates a 'warmup-views' target that will submit view queries to
    warmup the workspace

    @param app_prefix
        The application prefix, e.g., 'your-app'
    '''

    viewwarmup_script = os.path.join(js_scripts_dest_dir, 'submitqueries.js')
    rule(
        output='warmup-views',
        input=[
            os.path.join(js_lib_dest_dir, 'logicbloxtestutils.js'),
            viewwarmup_script],
        commands=['node %s --fail-on-error --app-prefix %s $(view_query_dir)' % (
            viewwarmup_script, app_prefix)],
        phony=True)

    
def rule_warmup(app_prefix,
                js_scripts_dest_dir=_default_js_scripts_dest_dir,
                js_lib_dest_dir=_default_js_lib_dest_dir):
    '''Creates a 'warmup-rules' target that will submit queries to
    warmup the rules in a workspace

    @param app_prefix
        The application prefix, e.g., 'your-app'
    '''

    viewwarmup_script = os.path.join(js_scripts_dest_dir, 'submitqueries.js')
    rule(
        output='warmup-rules',
        input=[
            os.path.join(js_lib_dest_dir, 'logicbloxtestutils.js'),
            viewwarmup_script],
        commands=['node %s --fail-on-error --app-prefix %s $(build)/srcgen/rule-warmup' % (
            viewwarmup_script, app_prefix)],
        phony=True)


def _copy_file(filename, src_dir, dest_dir):
    src_file = os.path.join(src_dir, filename)
    dest_file = os.path.join(dest_dir, filename)
    # we need to use our own copy target because
    # we need to create the directory too
    rule(output=dest_file,
         input=[src_file],
         commands=[
             'mkdir -p %s' % dest_dir,
             'cp %s %s' % (src_file, dest_dir)])
    rule(output='all', input=[dest_file])
    emit_clean_file(dest_file)
