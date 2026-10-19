#!/usr/bin/env python3
"""Bring every derived file up to date with the results, before committing them.

In order: the proofs' trees and counts (extract_proofs.py), Tamarin's warnings from the output
kept under runs/ (run_tamarin.py --reparse), the Lean outcomes and rejection reasons
(run_lean.py --reclassify), every SOURCE.txt (gen_sources.py), results/summary.md
(summarize.py), and the checks (validate.py).  It runs no tool on a model.

  python3 -I scripts/refresh.py
"""

import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
STEPS = [
    ["extract_proofs.py"],
    ["run_tamarin.py", "--reparse"],
    ["run_lean.py", "--reclassify"],
    ["gen_sources.py"],
    ["summarize.py"],
    ["validate.py"],
]


def main():
    for step in STEPS:
        r = subprocess.run([sys.executable, "-I", os.path.join(HERE, step[0])] + step[1:])
        if r.returncode:
            sys.exit(f"{' '.join(step)} failed")


if __name__ == "__main__":
    main()
