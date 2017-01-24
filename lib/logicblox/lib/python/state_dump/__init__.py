import subprocess
import psutil
import threading
import os
import shutil
import pwd
import logging
import traceback

THREAD_WAIT_SECONDS = 20

def _preexec():
    try:
        userinfo = pwd.getpwnam("logicblox")
        os.setgid(userinfo.pw_gid)
        os.setuid(userinfo.pw_uid)
        os.environ['HOME'] = userinfo.pw_dir
        os.environ['USER'] = userinfo.pw_name
    except:
        pass

def _check_cmd(cmd, name, shell=False):
    def check_cmd_fun(dirname):
        with open('%s/%s-output.log' % (dirname, name), 'w') as outfile:
            try:
                logging.info("Checking %s status" % (name))
                res = subprocess.call(cmd, stdout=outfile, stderr=outfile, preexec_fn=_preexec, shell=shell)
            except:
                logging.error("Could not run %s" % (name))
                logging.debug("Exception info: %s" % (traceback.format_exc()))
                with open('%s/%s-status.log' % (dirname, name), 'w') as outfile:
                    outfile.write("FAIL")
                raise
        with open('%s/%s-status.log' % (dirname, name), 'w') as outfile:
            if res == 0:
                outfile.write("OK")
            else:
                outfile.write("FAIL")
    return (check_cmd_fun, name)

def check_lb_status(dirname):
    threads = []
    for (fn,name) in [
            _check_cmd(["lb", "compiler-server", "status"], "lb-compiler"),
            _check_cmd(["lb", "pager", "status"], "lb-pager"),
            _check_cmd(["lb", "server", "status"], "lb-server"),
            _check_cmd(["lb", "web-server", "status"], "lb-webserver"),
            _check_cmd("lb workspaces | xargs lb status --all --debug", "lb-status-all-debug", shell=True)
            ]:
        thread = threading.Thread(target=fn, args=(dirname,), name=name)
        thread.daemon = True # Don't let these threads hold up an exit
        thread.start()
        threads.append(thread)
    for thread in threads:
        logging.info("Waiting for check of %s to complete" % (thread.name))
        thread.join(THREAD_WAIT_SECONDS)
        if thread.isAlive():
            logging.warning("Check of %s did not complete within %i seconds" % (thread.name, THREAD_WAIT_SECONDS))

def _pretty(val, indent=0):
    res = []
    if isinstance(val, dict):
        res.append('\t' * indent + '{\n')
        for key, value in val.iteritems():
            res.append('\t' * (indent+1) + '%s: \n' % (str(key)))
            res.extend(_pretty(value, indent+2))
            res.append(', # end of %s\n' % (str(key)))
        res.append('\n' + '\t' * indent + '}')
    elif isinstance(val, list):
        res.append('\t' * indent + '[\n')
        for value in val:
            res.extend(_pretty(value, indent+1))
            res.append(',\n')
        res.append('\t' * indent + ']')
    elif isinstance(val, tuple) and hasattr(val, "_asdict"):
        res.extend(_pretty(val._asdict(), indent))
    else:
        res.append('\t' * indent + str(val))
    return res

def collect_procinfo(dirname):
    logging.info("Collecting process info")
    for process in psutil.process_iter():
        logging.info("Collecting info for process %i" % (process.pid))
        pid_dir = '%s/%i' % (dirname, process.pid)
        os.mkdir(pid_dir)
        try:
            with open('%s/procinfo' % (pid_dir), 'w') as outfile:
                    outfile.write(''.join(_pretty(process.as_dict())))

            proc_dir = '/proc/%i' % (process.pid)
            def copy_from_proc(path):
                shutil.copy('%s/%s' % (proc_dir,path), '%s/%s' % (pid_dir,path))
            copy_from_proc('environ')
            copy_from_proc('limits')
            copy_from_proc('status')
            copy_from_proc('stat')
            copy_from_proc('statm')
            copy_from_proc('smaps')
            copy_from_proc('maps')
            if "java" in process.name():
                logging.info("Running jstack on process %i" % (process.pid))
                with open('%s/jstack' % (pid_dir), 'w') as outfile:
                    subprocess.call(['jstack', '%i' % (process.pid)], stdout=outfile, stderr=outfile)
            if any([substr in " ".join(process.cmdline()) for substr in [
                "lb",
                "java"
                ]]):
                logging.info("Running pstack on process %i" % (process.pid))
                with open('%s/pstack' % (pid_dir), 'w') as outfile:
                    subprocess.call(['pstack', '%i' % (process.pid)], stdout=outfile, stderr=outfile)
        except:
            logging.error("Collecting info for process %i failed, maybe process exited?" % (process.pid))
            logging.debug("Exception info: %s" % (traceback.format_exc()))


def collect_sysinfo(dirname, full_journal=False):
    logging.info("Collecting system info")
    def copy_from_proc(path):
        shutil.copy('/proc/%s' % (path), '%s/%s' % (dirname,path))
    logging.info("Collecting system-wide proc files")
    copy_from_proc('cpuinfo')
    copy_from_proc('meminfo')
    copy_from_proc('slabinfo')
    copy_from_proc('swaps')
    copy_from_proc('locks')
    copy_from_proc('uptime')
    copy_from_proc('version')
    logging.info("Collecting dmesg buffer")
    with open('%s/dmesg' % (dirname), 'w') as outfile:
        subprocess.call(['dmesg', '-T'], stdout=outfile, stderr=outfile)
    journal_args = [ 'journalctl', '--utc']
    if not full_journal:
        journal_args.append('--since=-1 week')
    logging.info("Collecting systemd journal")
    with open('%s/journal' % (dirname), 'w') as outfile:
        subprocess.call(journal_args, stdout=outfile, stderr=outfile)
    logging.info("Collecting ipc facility info")
    with open('%s/ipcs' % (dirname), 'w') as outfile:
        subprocess.call(['ipcs', '-a'], stdout=outfile, stderr=outfile)
        subprocess.call(['ipcs', '-p'], stdout=outfile, stderr=outfile)
    logging.info("Collecting top info")
    with open('%s/top.out' % (dirname), 'w') as outfile:
        subprocess.call(['top', '-b', '-n', '1'], stdout=outfile, stderr=outfile)
    logging.info("Collecting free disk space info")
    with open('%s/df' % (dirname), 'w') as outfile:
        subprocess.call(['df', '-T'], stdout=outfile, stderr=outfile)
    logging.info("Collecting free disk inode info")
    with open('%s/df-inode' % (dirname), 'w') as outfile:
        subprocess.call(['df', '-i'], stdout=outfile, stderr=outfile)
    logging.info("Collecting free shmem space info")
    with open('%s/strace-df-devshm' % (dirname), 'w') as outfile:
        subprocess.call(['strace', 'df', '/dev/shm'], stdout=outfile, stderr=outfile)
    logging.info("Collecting free shmem inode info")
    with open('%s/strace-df-devshm-inode' % (dirname), 'w') as outfile:
        subprocess.call(['strace', 'df', '-i', '/dev/shm'], stdout=outfile, stderr=outfile)
    logging.info("Collecting shmem usage info")
    with open('%s/du-devshm' % (dirname), 'w') as outfile:
        subprocess.call(['du', '/dev/shm'], stdout=outfile, stderr=outfile)
    logging.info("Collecting shmem directory contents")
    with open('%s/ls-devshm' % (dirname), 'w') as outfile:
        subprocess.call(['ls', '-AlR', '/dev/shm'], stdout=outfile, stderr=outfile)
    logging.info("Collecting open file info")
    with open('%s/lsof' % (dirname), 'w') as outfile:
        subprocess.call(['lsof', '-n'], stdout=outfile, stderr=outfile)
    logging.info("Collecting crontab info")
    with open('%s/crontab' % (dirname), 'w') as outfile:
        subprocess.call(['crontab', '-l'], stdout=outfile, stderr=outfile)
    if os.getenv('CRONLOG') is not None:
        try:
            logging.info("Trying to copy the cron log")
            shutil.copy('%s' % (os.getenv('CRONLOG')), '%s/cron.log' % (dirname))
        except:
            logging.error("Problem collecting the cron log")
            logging.debug("Exception info: %s" % (traceback.format_exc()))

    logging.info("Collecting CPU usage percentage")
    with open('%s/cpu-usage-percent' % (dirname), 'w') as outfile:
        outfile.write(''.join(_pretty(psutil.cpu_percent(percpu=True))))
    logging.info("Collecting CPU usage times")
    with open('%s/cpu-times' % (dirname), 'w') as outfile:
        outfile.write(''.join(_pretty(psutil.cpu_times(percpu=True))))

    logging.info("Collecting disk I/O counters")
    with open('%s/disk-io-counters' % (dirname), 'w') as outfile:
        try:
            outfile.write(''.join(_pretty(psutil.disk_io_counters(perdisk=True))))
        except RuntimeError:
            pass

    logging.info("Collecting systemd service status")
    with open('%s/systemctl' % (dirname), 'w') as outfile:
        subprocess.call(['systemctl'], stdout=outfile, stderr=outfile)

    logging.info("Collecting core dumps")
    with open('%s/coredumps' % (dirname), 'w') as outfile:
        try:
            for coredump in os.listdir('/disk0/coredumps'):
                outfile.write('%s\n' % (coredump))
        except:
            pass

def collect_meminfo(dirname):
    logging.info("Collecting memory info")
    logging.info("Collecting virtual memory info")
    with open('%s/virtual_memory' % (dirname), 'w') as outfile:
        outfile.write(''.join(_pretty(psutil.virtual_memory())))
    logging.info("Collecting swap memory info")
    with open('%s/swap_memory' % (dirname), 'w') as outfile:
        outfile.write(''.join(_pretty(psutil.swap_memory())))

def collect_netinfo(dirname):
    logging.info("Collecting network info")
    logging.info("Collecting network I/O counters")
    with open('%s/network-io-counters' % (dirname), 'w') as outfile:
        outfile.write(''.join(_pretty(psutil.network_io_counters(pernic=True))))
    logging.info("Collecting netstat information")
    with open('%s/netstat' % (dirname), 'w') as outfile:
        subprocess.call(['netstat', '-tulpn'], stdout=outfile, stderr=outfile)

def collect_userinfo(dirname):
    logging.info("Collecting user information")
    with open('%s/users' % (dirname), 'w') as outfile:
        outfile.write(''.join(_pretty(psutil.get_users())))
