import sys
import logging
import tempfile
import subprocess
from google.protobuf import text_format

def execute_blocking(spec, output):
    """
    Execute a batch specification, and write the resulting batch
    specification to given file.

    Arguments:
    spec   -- protobuf batch specification
    output -- file-like object to write batch specification to

    Raises a RuntimeError if execution failed.
    """
    input_file = tempfile.NamedTemporaryFile()
    input_file.write(text_format.MessageToString(spec))
    input_file.flush()

    if output == sys.stdout:
        cmd = ['lb', 'web-client',  'batch', '-i', input_file.name]
    else:
        cmd = ['lb', 'web-client',  'batch', '-i', input_file.name, '-o', output.name]

    try:
        _execute(cmd)
    finally:
        input_file.close()
    return

def export_delim(url, output = None, timeout = None):
    """
    Execute lb web-client export-delim

    Arguments:
    url     -- url of delimited-file service
    output  -- file path or S3 URI
    timeout -- timeout in seconds

    Raises a RuntimeError if execution failed.
    """
    args = []
    if timeout is not None:
        args.extend(['--timeout', str(timeout)])
    if output != None:
        args.extend(['-o', output])
    _execute(['lb', 'web-client',  'export', url] + args)
    return

def import_delim(url, input = None, full = False, timeout = None, compress = True, input_compressed = True):
    """
    Execute lb web-client import-delim

    Arguments:
    url              -- url of delimited-file service
    input            -- file path or S3 URI
    timeout          -- timeout in seconds
    input_compressed -- is the input already compressed?
    compress         -- compress the input while sending data to the server

    Raises a RuntimeError if execution failed.
    """
    args = []
    if full:
        args.append('--full')
    if timeout is not None:
        args.extend(['--timeout', str(timeout)])
    # TODO handle all combinations of input_compressed and compress
    # once web-client supports this.
    if not input_compressed and not compress:
        args.extend(['--no-compression'])
    if input != None:
        args.extend(['-i', input])
    _execute(['lb', 'web-client',  'import', url] + args)
    return

def _execute(cmd):
    exitcode = subprocess.call(cmd)
    if exitcode == 1:
        raise RuntimeError('failed: ' + str(cmd))

# TODO add a read method
def write(spec, output):
    """
    Write a protobuf batch specification to an output file.

    Arguments:
    spec   -- protobuf batch specification
    output -- file-like object to write batch specification to
    """
    text_format.PrintMessage(spec, output)
