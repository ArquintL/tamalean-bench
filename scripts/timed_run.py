#!/usr/bin/env python3
"""Run one command with a wall-clock limit and write how it went as JSON.

  python3 -I scripts/timed_run.py --limit SECONDS --json OUT --stdout F --stderr F -- CMD ...

The command runs in its own process group; when the limit is reached the whole group (Tamarin,
its Maude processes and its oracle) is terminated.  The JSON has the wall-clock time, the exit
code, whether the limit was reached, and the peak memory of the command's processes.  The
scripts start it through the machine's build-slot lock, so the time waiting for a slot is not
counted.
"""

import argparse
import json
import os
import resource
import signal
import subprocess
import sys
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=float, required=True)
    ap.add_argument("--json", required=True)
    ap.add_argument("--stdout", required=True)
    ap.add_argument("--stderr", required=True)
    ap.add_argument("--cwd")
    ap.add_argument("cmd", nargs=argparse.REMAINDER)
    a = ap.parse_args()
    cmd = a.cmd[1:] if a.cmd and a.cmd[0] == "--" else a.cmd
    with open(a.stdout, "wb") as out, open(a.stderr, "wb") as err:
        t0 = time.monotonic()
        p = subprocess.Popen(cmd, stdout=out, stderr=err, cwd=a.cwd, start_new_session=True)
        timed_out = False
        try:
            rc = p.wait(timeout=a.limit)
        except subprocess.TimeoutExpired:
            timed_out = True
            for sig in (signal.SIGTERM, signal.SIGKILL):
                try:
                    os.killpg(p.pid, sig)
                except ProcessLookupError:
                    break
                try:
                    p.wait(timeout=10)
                    break
                except subprocess.TimeoutExpired:
                    continue
            rc = p.returncode
        wall = time.monotonic() - t0
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    res = {"wall_s": round(wall, 3), "exit": rc, "timed_out": timed_out, "limit_s": a.limit,
           # ru_maxrss is in bytes on macOS and in kilobytes on Linux
           "max_rss_mb": round(ru.ru_maxrss / (1 << 20) if sys.platform == "darwin"
                               else ru.ru_maxrss / 1024, 1),
           "user_s": round(ru.ru_utime, 3), "sys_s": round(ru.ru_stime, 3)}
    with open(a.json, "w") as f:
        json.dump(res, f)


if __name__ == "__main__":
    main()
