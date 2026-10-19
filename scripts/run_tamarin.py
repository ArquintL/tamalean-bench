#!/usr/bin/env python3
"""Run Tamarin on the benchmark's models, one lemma at a time, and record the results.

For each model, in the model's directory (so that its oracle's relative path resolves):

1. Tamarin loads the model without proving anything: this lists its lemmas and prints its
   wellformedness and derivation warnings.
2. Each lemma is proved on its own: `tamarin-prover +RTS -N4 -M8G -RTS <the model's flags>
   --prove=<lemma> --output=proofs/<id>/<lemma>.spthy <model>`, within the lemma limit (600 s by
   default) and what is left of the model limit (1800 s by default).
3. results/tamarin/<id>.json records, per lemma, the verdict, the steps, the wall-clock and
   processing times, the limit, the flags, the oracle, the versions, the host and the date; the
   proofs are copied to the backup directory (bench.local.toml `proof_backup`, or the
   environment variable BENCH_PROOF_BACKUP).

A lemma or model that reaches its limit is listed in results/tamarin/long-runs.txt, for a later
run with more time.  results/tamarin/progress.txt logs every finished model.

Every Tamarin process starts through the machine's build-slot lock when BENCH_LOCK names it
(`zsh <path>/lakelock.sh`), so that it never overlaps an exclusive timing run.

  python3 -I scripts/run_tamarin.py --plan               # print the order the models run in
  python3 -I scripts/run_tamarin.py --jobs 2             # run everything not run yet, in order
  python3 -I scripts/run_tamarin.py --only emv/ --rerun  # run these again
"""

import argparse
import concurrent.futures as cf
import datetime as dt
import hashlib
import json
import os
import platform
import re
import shlex
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # -I leaves the script's dir out
import benchlib  # noqa: E402
import extract_proofs  # noqa: E402

TAMARIN = os.environ.get("BENCH_TAMARIN", "tamarin-prover")
RTS_N = 4
RTS_M = "8G"
LOCK = os.environ.get("BENCH_LOCK", "")  # e.g. "zsh /path/to/lakelock.sh"
PRINT_LOCK = threading.Lock()

# The papers the benchmark runs first, in this order.
GROUPS = [
    ("EMV", {"sp21-emv", "usenix21-brandmixup", "usenix23-authfailure", "fm24-c8"}),
    ("Tamigloo and Diodon", {"sp23-tamigloo", "sp26-diodon"}),
    ("SecureDrop", {"eprint26-securedrop", "msc-maier-securedrop"}),
    ("iMessage PQ3", {"usenix25-pq3"}),
    ("AKMA+, PURE, One For All", {"usenix25-akmaplus", "usenix24-pure", "csf25-oneforall"}),
    ("USENIX Security 2025", {"usenix25-moreisless", "usenix25-bletracking", "usenix25-wghybrid"}),
]
TAMARIN_SOURCES = {"tamarin-prover@1.10.0", "tamarin-prover@develop"}

# Lemmas not run, per model: (id, predicate on the lemma name) -> reason.  For iMessage PQ3 the
# authors prove only the lemmas named Auto_* automatically (prove-auto.sh); the others they proved
# interactively (their stored proofs are in the repository's proofs/), and
# Expensive_Auto_RkSecretCompromiseKemSS took them 8 hours and 100 GB (prove-expensive.sh).
def lemma_filter(model_id, name):
    if model_id == "pq3/model":
        if name.startswith("Auto_"):
            return None
        if name.startswith("Expensive_Auto_"):
            return ("long", "not run here: the authors' prove-expensive.sh proves it automatically "
                            "in about 8 hours with 100 GB")
        return ("skip", "not run: the authors prove it interactively (stored proof in the "
                        "repository's proofs/); only the Auto_* lemmas are proved automatically")
    return None


def log(msg):
    with PRINT_LOCK:
        print(f"[{dt.datetime.now().strftime('%H:%M:%S')}] {msg}", flush=True)


# --------------------------------------------------------------------------------------------
# The environment
# --------------------------------------------------------------------------------------------

def host_description():
    if sys.platform == "darwin":
        def sysctl(k):
            return subprocess.run(["sysctl", "-n", k], capture_output=True, text=True).stdout.strip()
        cpu = sysctl("machdep.cpu.brand_string")
        cores = sysctl("hw.ncpu")
        mem = int(sysctl("hw.memsize") or 0) // (1 << 30)
        osv = subprocess.run(["sw_vers", "-productVersion"], capture_output=True,
                             text=True).stdout.strip()
        return f"{cpu}, {cores} cores, {mem} GB, macOS {osv}"
    return f"{platform.processor() or platform.machine()}, {os.cpu_count()} cores, {platform.system()}"


def versions():
    out = subprocess.run([TAMARIN, "--version"], capture_output=True, text=True)
    text = out.stdout + out.stderr
    tv = re.search(r"tamarin-prover (\S+?),", text)
    mv = re.search(r"Maude version (\S+)", text) or re.search(r"checking version: (\S+?)\.", text)
    return (tv.group(1) if tv else "?"), (mv.group(1) if mv else "?")


def load_average():
    try:
        return round(os.getloadavg()[0], 1)
    except OSError:
        return None


# --------------------------------------------------------------------------------------------
# Oracles
# --------------------------------------------------------------------------------------------

def python_version(exe):
    try:
        out = subprocess.run([exe, "-c", "import sys; print('%d.%d.%d' % sys.version_info[:3])"],
                             capture_output=True, text=True, timeout=30)
        return out.stdout.strip()
    except Exception:
        return None


def is_python2(text):
    """True when the oracle is not Python 3 syntax (it is compiled, never run, to find out)."""
    import warnings
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            compile(text, "<oracle>", "exec")
        return False
    except SyntaxError:
        return True
    except ValueError:
        return False


def plan_oracles(s, x, rundir, cfg):
    """How each oracle of the model is run here.  Tamarin runs an oracle directly, by its
    shebang line.  Where that interpreter does not exist on this machine (a Python 2 oracle names
    /usr/bin/python), an oracle that the command line names is replaced by a wrapper that runs
    the same file with an interpreter of the same language; `env python` and `env python2` are
    resolved by a directory put first on PATH.  Returns (extra PATH dir or None, a map from the
    --oraclename value to the wrapper, notes)."""
    shim = rundir / "bin"
    replace, notes, shims = {}, [], {}
    py2 = cfg.get("python2")
    py3 = shutil.which("python3")
    home = benchlib.model_home(s, x)
    for f in x["files"]:
        if f["role"] != "oracle":
            continue
        path = home / f["dest"]
        text = path.read_text(encoding="utf-8", errors="replace")
        first = text.splitlines()[0] if text else ""
        if not first.startswith("#!"):
            notes.append(f"{f['dest']}: no interpreter line")
            continue
        parts = first[2:].split()
        prog = parts[1] if parts and parts[0].endswith("/env") and len(parts) > 1 else (parts[0] if parts else "")
        lang2 = is_python2(text) if "python" in prog or path.suffix == ".py" else False
        if "python" in prog:
            want = py2 if (lang2 or prog.endswith("python2")) else py3
            label = ("Python " + (python_version(want) or "?")) if want else None
        else:
            want, label = None, None
        if parts and parts[0].endswith("/env"):
            if shutil.which(prog) and not (prog == "python" and lang2) and prog != "python2":
                continue
            if not want:
                notes.append(f"{f['dest']}: needs {prog}, which is not installed")
                continue
            shims[prog] = want
            notes.append(f"{f['dest']}: `env {prog}` runs {label}"
                         + (" (the oracle is written for Python 2)" if lang2 else ""))
        else:
            if os.path.exists(prog) and os.access(prog, os.X_OK) and not (lang2 and "python3" in prog):
                continue
            if not want:
                notes.append(f"{f['dest']}: its interpreter {prog} does not exist here")
                continue
            dest_rel = os.path.relpath(path, benchlib.workdir(s, x))
            wrapper = rundir / "oracle" / f["dest"].replace("/", "__")
            wrapper.parent.mkdir(parents=True, exist_ok=True)
            wrapper.write_text(f"#!/bin/sh\nexec {shlex.quote(want)} {shlex.quote(str(path))} \"$@\"\n")
            os.chmod(wrapper, 0o755)
            replace[dest_rel] = str(wrapper)
            notes.append(f"{f['dest']}: its interpreter line names {prog}, which this machine "
                         f"lacks; the same file runs with {label}"
                         + (" (it is written for Python 2)" if lang2 else ""))
    if shims:
        shim.mkdir(parents=True, exist_ok=True)
        for name, exe in shims.items():
            p = shim / name
            if p.exists() or p.is_symlink():
                p.unlink()
            os.symlink(exe, p)
    return (str(shim) if shims else None), replace, notes


def effective_args(x, replace):
    out = []
    for a in x.get("tamarin_args", []):
        if a.startswith("--oraclename="):
            name = a.split("=", 1)[1]
            for k, v in replace.items():
                if os.path.normpath(k) == os.path.normpath(name):
                    a = f"--oraclename={v}"
        out.append(a)
    return out


def guidance(x):
    """The setting the run belongs to: Tamarin with a model-specific ranking (an oracle, a
    heuristic or a tactic the model or its authors give) or with no guidance."""
    if any(f["role"] == "oracle" for f in x["files"]):
        return "a ranking"
    if any(a.startswith("--heuristic") for a in x.get("tamarin_args", [])):
        return "a ranking"
    if x.get("heuristic") or x.get("tactics") or x.get("lemma_heuristics"):
        return "a ranking"
    return "no guidance"


# --------------------------------------------------------------------------------------------
# Running Tamarin
# --------------------------------------------------------------------------------------------

def run_timed(cmd, cwd, limit, rundir, tag, env):
    """Run `cmd` in `cwd` within `limit` seconds, through the lock when one is configured."""
    out, err, js = rundir / f"{tag}.out", rundir / f"{tag}.err", rundir / f"{tag}.json"
    for p in (out, err, js):
        if p.exists():
            p.unlink()
    timed = [sys.executable, "-I", str(Path(__file__).with_name("timed_run.py")),
             "--limit", str(limit), "--json", str(js), "--stdout", str(out), "--stderr", str(err),
             "--"] + cmd
    full = shlex.split(LOCK) + timed if LOCK else timed
    t0 = time.monotonic()
    p = subprocess.run(full, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    waited = time.monotonic() - t0
    if not js.exists():
        raise RuntimeError(f"{tag}: no timing record; the runner said: {p.stdout.decode()[-2000:]}")
    res = json.loads(js.read_text())
    res["lock_wait_s"] = round(max(0.0, waited - res["wall_s"]), 1)
    res["stdout"] = out.read_text(encoding="utf-8", errors="replace")
    res["stderr"] = err.read_text(encoding="utf-8", errors="replace")
    return res


SUMMARY_RE = re.compile(
    r"^\s*(?:(?P<side>LHS|RHS)\s*:\s*)?(?P<name>[A-Za-z0-9_]+)\s*\((?P<kind>all-traces|exists-trace)\):\s*"
    r"(?P<rest>.*?)\s*$")
DIFF_RE = re.compile(r"^\s*DiffLemma:\s*(?P<name>[A-Za-z0-9_]+)\s*:\s*(?P<rest>.*?)\s*$")


def parse_summary(stdout):
    """The lemmas of Tamarin's summary, with their verdicts, and the processing time."""
    i = stdout.rfind("summary of summaries:")
    part = stdout[i:] if i >= 0 else ""
    lemmas = []
    for line in part.splitlines():
        m = SUMMARY_RE.match(line)
        kind = None
        if m:
            kind = m.group("kind")
        else:
            m = DIFF_RE.match(line)
            if m:
                kind = "diff"
        if not m:
            continue
        rest = m.group("rest")
        steps = re.search(r"\((\d+) steps?\)", rest)
        if rest.startswith("verified"):
            verdict = "verified"
        elif rest.startswith("falsified"):
            verdict = "falsified"
        elif rest.startswith("analysis incomplete"):
            verdict = "incomplete"
        else:
            verdict = rest.split("(")[0].strip() or "unknown"
        lemmas.append({"name": m.group("name"), "kind": kind,
                       "side": m.groupdict().get("side"), "verdict": verdict,
                       "steps": int(steps.group(1)) if steps else None, "summary": rest})
    pt = re.search(r"processing time:\s*([\d.]+)s", part)
    return lemmas, (float(pt.group(1)) if pt else None), bool(part)


def parse_warnings(stdout, stderr):
    """Tamarin's wellformedness and derivation-check warnings: one line per failed check
    (`<check>: <first lines of its explanation>`), and any other line starting with WARNING."""
    warns = []
    for m in re.finditer(r"WARNING: the following wellformedness checks failed!(.*?)\*/", stdout, re.S):
        lines = m.group(1).splitlines()
        i = 0
        while i < len(lines):
            if i + 1 < len(lines) and lines[i].strip() and set(lines[i + 1].strip()) == {"="}:
                head = lines[i].strip()
                body = []
                j = i + 2
                while j < len(lines) and not (j + 1 < len(lines) and lines[j].strip()
                                              and set(lines[j + 1].strip()) == {"="}):
                    if lines[j].strip():
                        body.append(lines[j].strip())
                    j += 1
                w = f"{head}: {' '.join(body[:3])}"[:400]
                if w not in warns:
                    warns.append(w)
                i = j
            else:
                i += 1
    for ln in (stdout + "\n" + stderr).splitlines():
        t = ln.strip()
        if t.startswith("WARNING") and "wellformedness check" not in t and t not in warns:
            warns.append(t[:300])
    return warns[:40]


def load_error(res):
    text = (res["stderr"] + "\n" + res["stdout"]).strip().splitlines()
    tail = [ln for ln in text if ln.strip()][-12:]
    return " | ".join(tail)[-1500:]


def run_model(s, x, a, meta, cfg):
    mid = x["id"]
    wd = benchlib.workdir(s, x)
    model_file = benchlib.model_path(s, x)
    if not model_file.exists():
        log(f"{mid}: the model file is missing (run scripts/fetch_models.py)")
        return None
    rundir = benchlib.RUNS / "tamarin" / benchlib.id_to_filename(mid)
    rundir.mkdir(parents=True, exist_ok=True)
    proofdir = benchlib.PROOFS / mid
    proofdir.mkdir(parents=True, exist_ok=True)
    shim, replace, onotes = plan_oracles(s, x, rundir, cfg)
    env = dict(os.environ)
    if shim:
        env["PATH"] = shim + os.pathsep + env.get("PATH", "")
    env.update(x.get("tamarin_env", {}))
    args = effective_args(x, replace)
    rts = ["+RTS", f"-N{RTS_N}", f"-M{RTS_M}", "-RTS"]
    base = [TAMARIN] + rts + args
    budget = float(a.model_limit)
    result = {
        "id": mid, "tool": "tamarin", "setting": guidance(x),
        "tamarin_version": meta["tamarin"], "maude_version": meta["maude"],
        "rts": " ".join(rts), "parallel_runs": a.jobs, "host": meta["host"],
        "date": dt.date.today().isoformat(),
        "flags": x.get("tamarin_args", []), "env": x.get("tamarin_env", {}),
        "flags_basis": x.get("tamarin_args_basis", ""),
        "oracle": [f["dest"] for f in x["files"] if f["role"] == "oracle"] or None,
        "oracle_notes": onotes,
        "limits": {"lemma_s": a.lemma_limit, "model_s": a.model_limit},
        "load": {}, "lemmas": [], "warnings": [], "notes": [],
    }
    log(f"{mid}: load")
    res = run_timed(base + [model_file.name], wd, min(a.lemma_limit, budget), rundir, "load", env)
    budget -= res["wall_s"]
    lemmas, ptime, has_summary = parse_summary(res["stdout"])
    result["load"] = {"wall_s": res["wall_s"], "processing_s": ptime, "exit": res["exit"],
                      "lock_wait_s": res["lock_wait_s"], "max_rss_mb": res["max_rss_mb"]}
    result["warnings"] = parse_warnings(res["stdout"], res["stderr"])
    if res["timed_out"]:
        result["load"]["status"] = "timeout"
        result["load"]["message"] = (f"loading the model (its wellformedness and derivation "
                                     f"checks) did not finish within {min(a.lemma_limit, a.model_limit)} s")
        result["status"] = "load limit reached"
    elif not has_summary:
        result["load"]["status"] = "error"
        result["load"]["message"] = load_error(res)
        result["status"] = "not loaded"
    else:
        result["load"]["status"] = "ok"
    names = []
    for lem in lemmas:
        if lem["name"] not in names:
            names.append(lem["name"])
    kinds = {}
    for lem in lemmas:
        kinds.setdefault(lem["name"], []).append(lem)
    total = res["wall_s"]
    if result["load"]["status"] == "ok":
        for name in names:
            filt = lemma_filter(mid, name)
            for lem in kinds[name]:
                entry = {"name": name, "kind": lem["kind"], "side": lem["side"]}
                if filt:
                    entry.update(verdict="not run", reason=filt[1], long_run=filt[0] == "long")
                    result["lemmas"].append(entry)
            if filt:
                continue
            limit = min(float(a.lemma_limit), budget)
            if limit < 1:
                for lem in kinds[name]:
                    result["lemmas"].append({"name": name, "kind": lem["kind"], "side": lem["side"],
                                             "verdict": "not run",
                                             "reason": "the model limit was reached first",
                                             "long_run": True})
                continue
            out = proofdir / f"{name}.spthy"
            if out.exists():
                out.unlink()
            log(f"{mid}: {name} (limit {limit:.0f} s)")
            r = run_timed(base + [f"--prove={name}", f"--output={out}", model_file.name], wd, limit,
                          rundir, f"lemma-{name}", env)
            budget -= r["wall_s"]
            total += r["wall_s"]
            got, ptime, has = parse_summary(r["stdout"])
            for w in parse_warnings(r["stdout"], r["stderr"]):
                if w not in result["warnings"]:
                    result["warnings"].append(w)
            mine = [g for g in got if g["name"] == name]
            for lem in (mine or kinds[name]):
                e = {"name": name, "kind": lem["kind"], "side": lem.get("side"),
                     "wall_s": r["wall_s"], "processing_s": ptime, "limit_s": round(limit, 1),
                     "max_rss_mb": r["max_rss_mb"], "lock_wait_s": r["lock_wait_s"],
                     "load_avg": load_average()}
                if r["timed_out"]:
                    e.update(verdict="timeout", steps=None, long_run=True)
                elif not has or not mine:
                    msg = load_error(r)
                    mem = "heap overflow" in (r["stderr"] + r["stdout"]).lower()
                    e.update(verdict="memory limit" if mem else "error", steps=None,
                             message=msg, long_run=mem)
                else:
                    e.update(verdict=lem["verdict"], steps=lem["steps"], summary=lem["summary"])
                if out.exists() and not r["timed_out"]:
                    e["proof"] = f"proofs/{mid}/{name}.spthy"
                result["lemmas"].append(e)
        hit = any(l["verdict"] in ("timeout", "memory limit")
                  or l.get("reason") == "the model limit was reached first"
                  for l in result["lemmas"])
        result["status"] = "limit reached" if hit else "complete"
    result["total_wall_s"] = round(total, 2)
    if not names and result["load"]["status"] == "ok":
        result["notes"].append("Tamarin lists no lemma for this model")
    benchlib.write_json(benchlib.results_path("tamarin", mid), result)
    try:  # the counts of each proof, and its tree under proofs/
        extract_proofs.process_result(mid)
    except Exception as e:
        log(f"{mid}: reading the proofs failed: {e!r}")
    benchlib.backup_proofs(mid)
    progress(result)
    return result


def counts(result):
    c = {}
    for l in result.get("lemmas", []):
        c[l["verdict"]] = c.get(l["verdict"], 0) + 1
    return c


def progress(result):
    line = (f"{dt.datetime.now().strftime('%Y-%m-%d %H:%M')}  {result['id']}  "
            f"{result.get('status', '?')}  "
            + ", ".join(f"{v} {k}" for k, v in sorted(counts(result).items()))
            + f"  ({result.get('total_wall_s', 0):.0f} s)")
    with PRINT_LOCK:
        p = benchlib.RESULTS / "tamarin" / "progress.txt"
        p.parent.mkdir(parents=True, exist_ok=True)
        with open(p, "a", encoding="utf-8") as f:
            f.write(line + "\n")
    log(line)
    write_long_runs()


def write_long_runs():
    """results/tamarin/long-runs.txt: every lemma or model that reached its limit here."""
    lines = []
    for p in sorted((benchlib.RESULTS / "tamarin").rglob("*.json")):
        r = json.loads(p.read_text(encoding="utf-8"))
        flags = " ".join(r.get("flags", []))
        if r.get("load", {}).get("status") == "timeout":
            lines.append(f"{r['id']}\t*\tloading the model did not finish within "
                         f"{min(r['limits']['lemma_s'], r['limits']['model_s'])} s\t{flags}")
        seen = set()
        for l in r.get("lemmas", []):
            if not l.get("long_run") or l["name"] in seen:
                continue
            seen.add(l["name"])
            why = {"timeout": f"reached the lemma limit ({l.get('limit_s')} s)",
                   "memory limit": f"reached the memory limit ({r.get('rts')})"}.get(
                l["verdict"], l.get("reason", l["verdict"]))
            lines.append(f"{r['id']}\t{l['name']}\t{why}\t{flags}")
    header = ["# Lemmas and models that reached a limit of scripts/run_tamarin.py here, for a run",
              "# with more time or memory.  Columns: model id, lemma (* = the whole model), why,",
              "# the model's Tamarin flags.  Regenerated after every model."]
    with PRINT_LOCK:
        (benchlib.RESULTS / "tamarin" / "long-runs.txt").write_text(
            "\n".join(header + lines) + "\n", encoding="utf-8")


# --------------------------------------------------------------------------------------------
# The order
# --------------------------------------------------------------------------------------------

def plan(m):
    """The models in the order they run: the named papers' groups, then one model of every
    directory of Tamarin's own examples, then the rest; by size within a group."""
    order, used = [], set()
    models = list(benchlib.iter_models(m))
    for name, papers in GROUPS:
        grp = [(s, x) for s, x in models if set(x.get("paper", [])) & papers and x["id"] not in used]
        grp.sort(key=lambda t: t[1].get("bytes", 0))
        for s, x in grp:
            used.add(x["id"])
            order.append((name, s, x))
    by_dir = {}
    for s, x in models:
        if s["id"] in TAMARIN_SOURCES and x["id"] not in used:
            by_dir.setdefault((s["id"], os.path.dirname(x["path"])), []).append((s, x))
    sample = []
    for key in sorted(by_dir):
        cands = by_dir[key]
        cands.sort(key=lambda t: hashlib.sha256(t[1]["id"].encode()).hexdigest())
        sample.append(cands[0])
    sample.sort(key=lambda t: t[1].get("bytes", 0))
    for s, x in sample:
        used.add(x["id"])
        order.append(("Tamarin examples, one per directory", s, x))
    rest = [(s, x) for s, x in models if x["id"] not in used]
    rest.sort(key=lambda t: t[1].get("bytes", 0))
    for s, x in rest:
        order.append(("the rest", s, x))
    return order


def reparse():
    for p in sorted((benchlib.RESULTS / "tamarin").rglob("*.json")):
        r = json.loads(p.read_text(encoding="utf-8"))
        rundir = benchlib.RUNS / "tamarin" / benchlib.id_to_filename(r["id"])
        if not rundir.exists():
            continue
        warns = []
        for out in sorted(rundir.glob("*.out")):
            err = out.with_suffix(".err")
            for w in parse_warnings(out.read_text(errors="replace"),
                                    err.read_text(errors="replace") if err.exists() else ""):
                if w not in warns:
                    warns.append(w)
        r["warnings"] = warns
        benchlib.write_json(p, r)


def main():
    global RTS_M
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--only", action="append", help="only ids starting with this (repeatable)")
    ap.add_argument("--group", help="only the models of the plan group whose name starts with this")
    ap.add_argument("--lemma-limit", type=int, default=600)
    ap.add_argument("--model-limit", type=int, default=1800)
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--memory", default=RTS_M, help="GHC heap limit per Tamarin process (+RTS -M)")
    ap.add_argument("--rerun", action="store_true", help="run models that already have a result")
    ap.add_argument("--max-models", type=int)
    ap.add_argument("--plan", action="store_true", help="print the order and exit")
    ap.add_argument("--reparse", action="store_true",
                    help="recompute the warnings of every result from the output kept in runs/")
    a = ap.parse_args()
    RTS_M = a.memory
    if a.reparse:
        reparse()
        return
    m = benchlib.load_manifest()
    order = plan(m)
    if a.only:
        order = [t for t in order if any(t[2]["id"].startswith(o) for o in a.only)]
    if a.group:
        order = [t for t in order if t[0].startswith(a.group)]
    if not a.rerun:
        order = [t for t in order if not benchlib.results_path("tamarin", t[2]["id"]).exists()]
    if a.max_models:
        order = order[:a.max_models]
    if a.plan:
        for g, s, x in order:
            print(f"{g}\t{x['id']}\t{' '.join(x.get('tamarin_args', []))}")
        print(f"{len(order)} models", file=sys.stderr)
        return
    tv, mv = versions()
    meta = {"tamarin": tv, "maude": mv, "host": host_description()}
    cfg = benchlib.local_config()
    log(f"Tamarin {tv}, Maude {mv}, {meta['host']}; {len(order)} models; lock: {LOCK or 'none'}")
    with cf.ThreadPoolExecutor(max_workers=a.jobs) as ex:
        futs = {ex.submit(run_model, s, x, a, meta, cfg): x["id"] for _, s, x in order}
        for f in cf.as_completed(futs):
            try:
                f.result()
            except Exception as e:  # one model's failure does not stop the others
                log(f"{futs[f]}: runner error: {e!r}")
    write_long_runs()


if __name__ == "__main__":
    main()
