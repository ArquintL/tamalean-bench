#!/usr/bin/env python3
"""Run the Lean side: each generated module Bench/<id>.lean on its own, with `lake lean`.

`lake lean` loads Tamalean's precompiled engine, so `certify`'s search runs as native code (plain
`lake env lean` would interpret it).  For each model the runner records, in
results/tamalean/<id>.json, whether Tamalean's reader accepted the model (and its error when it
did not), and per lemma the outcome of `certify` and its time:

* `proved`: the lemma is proved (for an exists-trace lemma: a trace satisfies it), checked by
  Lean's kernel;
* `attack found`: an all-traces lemma is false: certify found a trace that violates it, which
  the kernel checked;
* `no trace`: an exists-trace lemma is false: certify proved that no trace satisfies it;
* `no verdict`: certify stopped without either (the first line of its report is kept);
* `timeout`: the lemma reached its limit;
* `rejected`: the reader rejected the model, so no lemma was stated.

A lemma that runs past the lemma limit (600 s by default) is stopped and the module resumes
after it (`-Dbench.only=…`), as long as the model limit (1800 s) allows.

The times are meant to be measured alone on the machine: start the runner through the build
lock, e.g. `env LAKELOCK_EXCLUSIVE=1 zsh lakelock.sh python3 -I scripts/run_lean.py
--measured-alone`; the runner itself then calls `lake` directly.  On a shared machine, BENCH_LOCK
(e.g. `zsh lakelock.sh`) makes each `lake` call take a build slot of its own instead; the time
spent waiting for the slot and loading the imports is not counted.

  python3 -I scripts/run_lean.py                    # every in-scope model
  python3 -I scripts/run_lean.py --only tamigloo/   # some
  python3 -I scripts/run_lean.py --accepted         # only models the reader accepted last time
"""

import argparse
import datetime as dt
import json
import os
import re
import shlex
import signal
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # -I leaves the script's dir out
import benchlib  # noqa: E402
import gen_lean  # noqa: E402

LAKE = os.environ.get("BENCH_LAKE", "lake")


def scrub(text):
    """The text without this checkout's absolute path (results are committed)."""
    return text.replace(str(benchlib.ROOT) + os.sep, "") if isinstance(text, str) else text


def classify_error(err):
    """The outcome a failed `certify` reports, from its message."""
    first = err.strip().splitlines()[0] if err.strip() else ""
    # Lean prefixes the position: `Bench/x.lean:12:0: error: certify: …`
    body = re.sub(r"^.*?:\d+:\d+:\s*error:\s*", "", first)
    if re.match(r"certify: the lemma is false\b", body):
        return "attack found", body
    if re.match(r"certify: (no trace satisfies the formula|no trace of the full attacker "
                r"satisfies the formula)", body):
        return "no trace", body
    return "no verdict", body


REJECT_PATTERNS = [
    (r"restrictions are not supported", "restrictions"),
    (r"proof-search heuristics and tactics are not supported", "`heuristic:` or `tactic:`"),
    (r"preprocessor directives", "preprocessor (#ifdef, #include)"),
    (r"processes \(SAPIC\) are not supported", "processes (SAPIC+)"),
    (r"observational equivalence", "observational equivalence"),
    (r"predicates are not supported", "predicates"),
    (r"macros are not supported", "macros"),
    (r"`options:` is not supported", "`options:`"),
    (r"`export` is not supported", "`export`"),
    (r"`configuration:` is not supported", "`configuration:`"),
    (r"unsupported builtin `([^`]+)`", "unsupported builtin: {0}"),
    (r"function attributes", "function attributes ([private], [destructor])"),
    (r"equation attributes", "equation attributes ([convergent])"),
    (r"unsupported lemma attribute `([^`]+)`", "lemma attribute: {0}"),
    (r"last\(", "last(#i)"),
    (r"subterm", "the subterm relation"),
    (r"nat sort|natural-numbers|`%", "natural numbers"),
    (r"fresh constant", "fresh constants (~'n')"),
    (r"is not bound", "an unbound variable in a lemma"),
    (r"the reducible function symbol", "a reducible symbol (destructor) in a lemma"),
    (r"refers to the action", "an action no rule has, in a lemma"),
    (r"has arity", "an action used with another arity"),
    (r"`K` takes one argument|`!K` is not an action|only the", "attacker facts in a lemma"),
]


EXTRA_PATTERNS = [
    (r"applies the destructor", "a protocol rule applies a destructor"),
    (r"unterminated public name", "lexer: an unterminated public name (a quote ' in the text)"),
    (r"expected the theory's name, found `\d", "a theory name that starts with a digit"),
    (r"unexpected `([^`]+)`: expected an item", "unsupported item `{0}`"),
]


def rejection_reason(err):
    """The reason the reader gives, as a short label shared by every model with that reason."""
    for pat, label in REJECT_PATTERNS + EXTRA_PATTERNS:
        mm = re.search(pat, err)
        if mm:
            return label.format(*mm.groups()) if mm.groups() else label
    mm = re.search(r"tamarin_theory(?:_file)?: (.*)", err)
    if mm:
        msg = mm.group(1)
        msg = re.sub(r"`[^`]*`", "`…`", msg)          # names differ from model to model
        msg = re.split(r"[;(:]", msg)[0].strip()
        return "frontend: " + msg[:90]
    first = err.strip().splitlines()[0] if err.strip() else "no message"
    return "other: " + re.sub(r"^.*?error:\s*", "", first)[:90]


LOCK = os.environ.get("BENCH_LOCK", "")  # e.g. "zsh /path/to/lakelock.sh": one slot per module


def run_module(module, only, limit_lemma, limit_left, log_path, events_path,
               startup_limit=3600.0):
    """Run `lake lean module` and follow the lines the harness appends to `events_path` (Lake
    passes a module's output on only at its end).  The model's clock starts when the module
    starts reading the model, so that waiting for the build lock or loading the imports is not
    counted; reading the model counts against the model limit, each lemma against the lemma
    limit.  Returns (events, the lemma stopped at its limit or None, the lemma (or "the reader")
    running when the model limit was reached or None, exit code, tail of the output, wall time on
    the model's clock)."""
    cmd = [LAKE, "lean", str(module.relative_to(benchlib.ROOT))]
    if only is not None:
        cmd += ["--", f"-Dbench.only={','.join(only)}"]
    if LOCK:
        cmd = shlex.split(LOCK) + cmd
    if events_path.exists():
        events_path.unlink()
    env = dict(os.environ, BENCH_EVENTS=str(events_path))
    t_start = time.monotonic()
    with open(log_path, "ab") as logf:
        p = subprocess.Popen(cmd, cwd=benchlib.ROOT, stdout=logf, stderr=subprocess.STDOUT,
                             start_new_session=True, env=env)
        events, seen = [], 0
        current, started = None, None
        stopped, model_out = None, False
        t0 = None  # the model's clock
        while True:
            done = p.poll() is not None
            if events_path.exists():
                lines = events_path.read_text(encoding="utf-8", errors="replace").splitlines()
                for s in lines[seen:]:
                    if not s.startswith("BENCH "):
                        continue
                    _, kind, js = s.split(" ", 2)
                    ev = {k: scrub(v) for k, v in json.loads(js).items()}
                    ev["kind"] = kind
                    events.append(ev)
                    if kind == "reading" and t0 is None:
                        t0 = time.monotonic()
                        current, started = "the reader", t0
                    elif kind == "reader":
                        current = None
                    elif kind == "start":
                        current, started = ev["name"], time.monotonic()
                    elif kind == "lemma":
                        current = None
                seen = len(lines)
            if done:
                break
            now = time.monotonic()
            if current and now - started > limit_lemma:
                stopped = current
            if t0 is not None and now - t0 > limit_left:
                model_out = True
            if t0 is None and now - t_start > startup_limit:
                model_out = True
            if stopped or model_out:
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                p.wait()
                break
            time.sleep(0.5)
    end = time.monotonic()
    tail = log_path.read_text(encoding="utf-8", errors="replace").splitlines()[-200:]
    wall = end - (t0 if t0 is not None else t_start)
    return events, stopped, (current if model_out else None), p.returncode, tail, wall


def run_model(s, x, a, host):
    mid = x["id"]
    module = gen_lean.module_path(mid)
    text, lemmas = gen_lean.render(s, x)
    if not module.exists() or module.read_text(encoding="utf-8") != text:
        module.parent.mkdir(parents=True, exist_ok=True)
        module.write_text(text, encoding="utf-8")
    logdir = benchlib.RUNS / "lean"
    logdir.mkdir(parents=True, exist_ok=True)
    log_path = logdir / (benchlib.id_to_filename(mid) + ".log")
    events_path = logdir / (benchlib.id_to_filename(mid) + ".events")
    if log_path.exists():
        log_path.unlink()
    result = {"id": mid, "tool": "tamalean", "setting": "no guidance",
              "tactic": "certify (the model's default sources)",
              "tamalean_commit": a.commit, "lean_toolchain": a.toolchain,
              "host": host, "date": dt.date.today().isoformat(),
              "measured_alone": a.measured_alone,
              "limits": {"lemma_s": a.lemma_limit, "model_s": a.model_limit},
              "reader": {}, "lemmas": []}
    done = {}
    remaining = list(dict.fromkeys(lemmas))
    budget = float(a.model_limit)
    first = True
    total = 0.0
    while True:
        only = (["-"] if a.reader_only else None) if first else remaining
        if not first and not remaining:
            break
        events, stopped, model_cut, rc, tail, wall = run_module(
            module, only, a.lemma_limit, budget, log_path, events_path)
        budget -= wall
        total += wall
        for ev in events:
            if ev["kind"] == "reader":
                result["reader"] = {"ok": ev["ok"], "ms": ev["ms"]}
                if not ev["ok"]:
                    result["reader"]["error"] = ev.get("error", "")
                    result["reader"]["reason"] = rejection_reason(ev.get("error", ""))
            elif ev["kind"] == "lemma":
                e = {"name": ev["name"], "ms": ev["ms"]}
                if ev.get("missing"):
                    e["outcome"] = "rejected" if not result["reader"].get("ok", True) else "no statement"
                    e["message"] = ev.get("error", "")
                elif ev["ok"]:
                    e["outcome"] = "proved"
                else:
                    e["outcome"], e["message"] = classify_error(ev.get("error", ""))
                if ev.get("info"):
                    e["info"] = [i.splitlines()[0][:300] for i in ev["info"]]
                done[ev["name"]] = e
        if first and not result["reader"]:
            # the module stopped before the reader reported: a build or import failure
            result["reader"] = {"ok": False, "error": scrub("\n".join(tail[-30:])[-3000:]),
                                "reason": "the module did not run (see error)"}
        first = False
        if stopped == "the reader":
            result["reader"] = {"ok": False, "reason": "reading the model reached the lemma limit",
                                "error": f"reading the model took more than {a.lemma_limit} s"}
        elif stopped:
            done[stopped] = {"name": stopped, "outcome": "timeout",
                             "ms": int(a.lemma_limit * 1000)}
        if model_cut == "the reader":
            result["reader"] = {"ok": False, "reason": "the reader did not finish within the model limit",
                                "error": f"reading the model took more than {a.model_limit} s"}
        elif model_cut:
            done[model_cut] = {"name": model_cut, "outcome": "timeout", "ms": None,
                               "message": "the model limit was reached during this lemma"}
        remaining = [l for l in remaining if l not in done]
        if not result["reader"].get("ok") or a.reader_only:
            break
        if not stopped or budget < 1:
            break
    for l in lemmas:
        if l in done:
            result["lemmas"].append(done[l])
        elif not result["reader"].get("ok"):
            result["lemmas"].append({"name": l, "outcome": "rejected"})
        else:
            result["lemmas"].append({"name": l, "outcome": "not run",
                                     "message": "only the reader ran" if a.reader_only else
                                     "the model limit was reached first"
                                     if budget < 1 else "the module stopped before this lemma"})
    result["total_wall_s"] = round(total, 2)
    benchlib.write_json(benchlib.results_path("tamalean", mid), result)
    c = {}
    for l in result["lemmas"]:
        c[l["outcome"]] = c.get(l["outcome"], 0) + 1
    status = ("rejected: " + result["reader"].get("reason", "")) if not result["reader"].get("ok") \
        else ", ".join(f"{v} {k}" for k, v in sorted(c.items())) or "no lemmas"
    print(f"[{dt.datetime.now().strftime('%H:%M:%S')}] {mid}: {status} ({total:.1f} s)", flush=True)
    return result


def retime_model(s, x, a):
    """Run again, to time them alone on the machine, the lemmas of an accepted model that ended
    within their limits, and record their new times (and outcomes)."""
    mid = x["id"]
    r = benchlib.load_result("tamalean", mid)
    if not r or not r.get("reader", {}).get("ok"):
        return None
    names = [l["name"] for l in r["lemmas"]
             if l.get("outcome") in ("proved", "attack found", "no trace", "no verdict")]
    module = gen_lean.module_path(mid)
    logdir = benchlib.RUNS / "lean"
    logdir.mkdir(parents=True, exist_ok=True)
    log_path = logdir / (benchlib.id_to_filename(mid) + ".retime.log")
    events_path = logdir / (benchlib.id_to_filename(mid) + ".retime.events")
    if log_path.exists():
        log_path.unlink()
    events, stopped, model_cut, rc, tail, wall = run_module(
        module, names or ["-"], a.lemma_limit, a.model_limit, log_path, events_path)
    by = {l["name"]: l for l in r["lemmas"]}
    for ev in events:
        if ev["kind"] == "reader" and ev.get("ok"):
            r["reader"]["ms"] = ev["ms"]
            r["reader"]["measured_alone"] = a.measured_alone
        elif ev["kind"] == "lemma" and ev["name"] in by and not ev.get("missing"):
            l = by[ev["name"]]
            l["ms"] = ev["ms"]
            if ev["ok"]:
                l["outcome"] = "proved"
                l.pop("message", None)
            else:
                l["outcome"], l["message"] = classify_error(ev.get("error", ""))
            l["measured_alone"] = a.measured_alone
    if stopped and stopped in by:
        by[stopped].update(outcome="timeout", ms=int(a.lemma_limit * 1000),
                           measured_alone=a.measured_alone)
    r["measured_alone"] = a.measured_alone and all(
        l.get("measured_alone") for l in r["lemmas"] if l["outcome"] != "timeout")
    r["retimed"] = dt.date.today().isoformat()
    benchlib.write_json(benchlib.results_path("tamalean", mid), r)
    print(f"[{dt.datetime.now().strftime('%H:%M:%S')}] {mid}: retimed {len(names)} lemmas "
          f"({wall:.1f} s)", flush=True)
    return r


def reclassify():
    n = 0
    for p in sorted((benchlib.RESULTS / "tamalean").rglob("*.json")):
        r = json.loads(p.read_text(encoding="utf-8"))
        rd = r.get("reader", {})
        if not rd.get("ok") and rd.get("error"):
            rd["reason"] = rejection_reason(rd["error"])
        for l in r.get("lemmas", []):
            if l.get("outcome") in ("attack found", "no trace", "no verdict") and l.get("message"):
                l["outcome"], l["message"] = classify_error(l["message"])
        benchlib.write_json(p, r)
        n += 1
    print(f"{n} results reclassified", file=sys.stderr)


def host_description():
    import run_tamarin
    return run_tamarin.host_description()


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--only", action="append", help="only ids starting with this (repeatable)")
    ap.add_argument("--accepted", action="store_true",
                    help="only models whose last result says the reader accepted them")
    ap.add_argument("--missing", action="store_true", help="only models without a result")
    ap.add_argument("--lemma-limit", type=int, default=600)
    ap.add_argument("--model-limit", type=int, default=1800)
    ap.add_argument("--measured-alone", action="store_true",
                    help="record that the run had the machine to itself (an exclusive lock)")
    ap.add_argument("--no-build", action="store_true", help="do not build Bench.Harness first")
    ap.add_argument("--reader-only", action="store_true",
                    help="only read each model (no certify): the reader's verdict, quickly")
    ap.add_argument("--retime", action="store_true",
                    help="run again the lemmas of accepted models that ended within their limits, "
                         "to time them (start it with an exclusive lock and --measured-alone)")
    ap.add_argument("--reclassify", action="store_true",
                    help="recompute the outcomes and rejection reasons of the results from their "
                         "stored messages, and run nothing")
    ap.add_argument("--shard", help="I/N: run only the I-th of N equal shares of the models (CI)")
    ap.add_argument("--total-limit", type=float,
                    help="stop starting models after this many seconds (CI); the rest are skipped")
    a = ap.parse_args()
    if a.reclassify:
        reclassify()
        return
    a.commit = subprocess.run(["git", "-C", str(benchlib.ROOT / "tamalean"), "rev-parse", "HEAD"],
                              capture_output=True, text=True).stdout.strip()
    a.toolchain = (benchlib.ROOT / "lean-toolchain").read_text().strip()
    gen_lean.generate()
    if not a.no_build:
        b = subprocess.run((shlex.split(LOCK) if LOCK else []) + [LAKE, "build", "Bench.Harness"],
                           cwd=benchlib.ROOT)
        if b.returncode:
            sys.exit("lake build Bench.Harness failed")
    m = benchlib.load_manifest()
    host = host_description()
    todo = []
    for s, x in benchlib.iter_models(m):
        if not benchlib.lean_in_scope(x):
            continue
        if a.only and not any(x["id"].startswith(o) for o in a.only):
            continue
        if not benchlib.model_path(s, x).exists():
            print(f"skipped {x['id']}: the model file is missing", file=sys.stderr)
            continue
        prev = benchlib.load_result("tamalean", x["id"])
        if a.missing and prev:
            continue
        if a.accepted and not (prev and prev.get("reader", {}).get("ok")):
            continue
        todo.append((s, x))
    if a.shard:
        i, n = (int(v) for v in a.shard.split("/"))
        todo = [t for k, t in enumerate(todo) if k % n == i - 1]
    print(f"{len(todo)} models", file=sys.stderr)
    t0 = time.monotonic()
    for k, (s, x) in enumerate(todo):
        if a.total_limit and time.monotonic() - t0 > a.total_limit:
            print(f"the total limit was reached: {len(todo) - k} models not run", file=sys.stderr)
            break
        try:
            if a.retime:
                retime_model(s, x, a)
            else:
                run_model(s, x, a, host)
        except Exception as e:
            print(f"{x['id']}: runner error: {e!r}", file=sys.stderr)


if __name__ == "__main__":
    main()
