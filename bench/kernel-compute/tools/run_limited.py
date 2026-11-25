"""Run a command under /usr/bin/time -v with a wall-clock limit and a resident-memory limit.

usage: python3 -I run_limited.py TIMEOUT_SECONDS MEM_MIB LOGFILE -- COMMAND...

The command's stdout and stderr go to LOGFILE. One line is printed on stdout:
    STATUS<TAB>EXIT<TAB>WALL_SECONDS<TAB>PEAK_RSS_MIB
STATUS is `exited` (EXIT is the command's exit status), `timeout` or `oom`. The memory
limit is enforced by sampling the resident set of the whole process group every 50 ms
and killing it above the limit; `ulimit -v` is not used, because checkers that reserve
address space up front (gruszka does) cannot start under it.
"""
import os, re, signal, subprocess, sys, tempfile, time


def group_rss_kib(pgid):
    total = 0
    for pid in os.listdir("/proc"):
        if not pid.isdigit():
            continue
        try:
            if os.getpgid(int(pid)) != pgid:
                continue
            with open(f"/proc/{pid}/statm") as f:
                total += int(f.read().split()[1]) * (os.sysconf("SC_PAGE_SIZE") // 1024)
        except (OSError, ValueError):
            pass
    return total


def main():
    timeout, mem_mib, log = float(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    cmd = sys.argv[5:]
    with tempfile.NamedTemporaryFile("r", prefix="time-", delete=True) as tf, open(log, "wb") as lf:
        t0 = time.monotonic()
        p = subprocess.Popen(["/usr/bin/time", "-v", "-o", tf.name] + cmd, stdout=lf, stderr=lf,
                             start_new_session=True)
        status = "exited"
        peak = 0
        while p.poll() is None:
            peak = max(peak, group_rss_kib(p.pid))
            if time.monotonic() - t0 > timeout:
                status = "timeout"
            elif peak > mem_mib * 1024:
                status = "oom"
            if status != "exited":
                os.killpg(p.pid, signal.SIGKILL)
                p.wait()
                break
            time.sleep(0.05)
        wall = time.monotonic() - t0
        report = tf.read()
    m = re.search(r"Maximum resident set size \(kbytes\): (\d+)", report)
    if m:
        peak = max(peak, int(m.group(1)))
    m = re.search(r"Elapsed \(wall clock\) time.*: (?:(\d+):)?(\d+):([\d.]+)$", report, re.M)
    if m and status == "exited":
        wall = int(m.group(1) or 0) * 3600 + int(m.group(2)) * 60 + float(m.group(3))
    code = p.returncode if status == "exited" else ""
    print(f"{status}\t{code}\t{wall:.2f}\t{peak / 1024:.0f}")


main()
