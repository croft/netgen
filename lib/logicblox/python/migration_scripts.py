import subprocess
import os

LOGICBLOX_HOME = os.environ.get('LOGICBLOX_HOME')
migration_script_folder = '%s/assets/migration-scripts' % LOGICBLOX_HOME


def run_shell(s):
    return subprocess.check_output(
        s, shell=True)


def _4_3_13():
    return run_shell('node %s/4.3.13/convert-sliceValueMeasure.js src/config/sheets' % migration_script_folder)


def _4_3_16():
    run_shell('/usr/bin/env python  %s/4.3.16/02-migrate-workbook-spec.py src/config/workbooks' % migration_script_folder)
    return run_shell('node %s/4.3.16/migrate-sheets.js src/config/sheets' % migration_script_folder)
