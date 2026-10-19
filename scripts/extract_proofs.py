#!/usr/bin/env python3
"""Read the proof scripts in Tamarin's output files into a tree per lemma.

Tamarin writes a proof as an indented script: a proof method per step (`simplify`,
`solve( goal )`, `induction`, ...), its cases (`case name` ... `next` ... `qed`), and each
branch's end (`by contradiction /* cyclic */`, `SOLVED // trace found`, `by sorry`, ...).  This
script turns the proof of a lemma into a JSON tree:

  {"method": "solve", "goal": "!KU( ~k ) @ #vk.1", "goal_kind": "KU action",
   "cases": [{"case": "Client_1", "proof": {...}}, ...]}
  {"method": "contradiction", "end": "contradiction", "note": "cyclic"}

and counts, per lemma: the proof's size (its steps, leaves included), its depth, its leaves by
how they end, and its `solve` steps by the kind of goal they solve.

  python3 -I scripts/extract_proofs.py                    # every proof under proofs/: write
                                                          # proofs/<id>/<lemma>.json and the counts
                                                          # into results/tamarin/<id>.json
  python3 -I scripts/extract_proofs.py FILE [--lemma L]   # print the trees of one file
"""

import argparse
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # -I leaves the script's dir out
import benchlib  # noqa: E402

LEAF_WORDS = ("SOLVED", "MIRRORED", "ATTACK", "UNFINISHABLE")
LEMMA_RE = re.compile(r"^(lemma|diffLemma)\s+([A-Za-z0-9_]+)\b")


def strip_comment(s):
    """(text, comment) for a step line: `/* ... */` and `// ...` comments are split off."""
    note = None
    m = re.search(r"/\*(.*?)\*/", s)
    if m:
        note = m.group(1).strip()
        s = (s[:m.start()] + s[m.end():]).rstrip()
    m = re.search(r"\s//\s*(.*)$", s)
    if m:
        note = (note + "; " if note else "") + m.group(1).strip()
        s = s[:m.start()].rstrip()
    return s.strip(), note


def balance(s):
    """Open parentheses minus closed ones, outside comments and quoted names."""
    s = re.sub(r"/\*.*?\*/", "", s)
    s = re.sub(r"'[^']*'", "", s)
    return s.count("(") - s.count(")")


def logical_lines(lines, start):
    """(indent, text) per proof line from `start`: a step that spans several lines (a long
    goal) is joined; block comments on their own lines are skipped."""
    i = start
    in_comment = False
    while i < len(lines):
        raw = lines[i]
        st = raw.strip()
        if in_comment:
            if "*/" in st:
                in_comment = False
            i += 1
            continue
        if not st:
            i += 1
            continue
        if st.startswith("/*") and "*/" not in st:
            in_comment = True
            i += 1
            continue
        if st.startswith("/*") and st.endswith("*/"):
            i += 1
            continue
        indent = len(raw) - len(raw.lstrip(" "))
        text = st
        b = balance(text)
        while b > 0 and i + 1 < len(lines):
            i += 1
            text += " " + lines[i].strip()
            b = balance(text)
        yield indent, re.sub(r"\s+", " ", text)
        i += 1


def goal_kind(goal):
    if "▶" in goal:
        return "premise"
    if "~~>" in goal:
        return "chain"
    if "∥" in goal:
        return "disjunction"
    if goal.startswith("splitEqs"):
        return "equation split"
    if "⊏" in goal:
        return "subterm"
    if goal.startswith("!KU(") or goal.startswith("KU("):
        return "KU action"
    if " @ " in goal:
        return "action"
    return "other"


class ProofSyntax(Exception):
    pass


def parse_step(toks, i):
    if i >= len(toks):
        raise ProofSyntax("the proof ends early")
    _, t = toks[i]
    body, note = strip_comment(t)
    if body.startswith("by "):
        meth = body[3:].strip()
        node = {"method": meth.split("(")[0].strip(), "end": meth.split("(")[0].strip()}
        if "(" in meth:
            node["goal"] = meth[meth.index("(") + 1:meth.rindex(")")].strip()
            node["goal_kind"] = goal_kind(node["goal"])
        if note:
            node["note"] = note
        return node, i + 1
    if body.split(" ")[0] in LEAF_WORDS:
        node = {"method": body.split(" ")[0], "end": body.split(" ")[0]}
        if note:
            node["note"] = note
        return node, i + 1
    if body in ("qed", "next") or body.startswith("case "):
        raise ProofSyntax(f"unexpected `{body}`")
    node = {"method": body.split("(")[0].strip()}
    if "(" in body and body.endswith(")"):
        node["goal"] = body[body.index("(") + 1:-1].strip()
        node["goal_kind"] = goal_kind(node["goal"])
    elif body != node["method"]:
        node["detail"] = body
    if note:
        node["note"] = note
    i += 1
    cases = []
    if i < len(toks) and toks[i][1].startswith("case "):
        while True:
            name = toks[i][1][5:].strip()
            child, i = parse_step(toks, i + 1)
            cases.append({"case": name, "proof": child})
            if i >= len(toks):
                raise ProofSyntax("missing qed")
            nxt = toks[i][1]
            if nxt == "next":
                i += 1
                if i >= len(toks) or not toks[i][1].startswith("case "):
                    raise ProofSyntax("`next` without a case")
                continue
            if nxt == "qed":
                i += 1
                break
            raise ProofSyntax(f"expected `next` or `qed`, found `{nxt}`")
    else:
        child, i = parse_step(toks, i)
        cases.append({"case": None, "proof": child})
    node["cases"] = cases
    return node, i


def lemma_proofs(text):
    """{lemma name: (proof tree or None, error or None)} for every lemma of a Tamarin file."""
    lines = text.splitlines()
    out = {}
    for n, line in enumerate(lines):
        m = LEMMA_RE.match(line)
        if not m:
            continue
        name = m.group(2)
        # skip the header: the trace quantifier and the formula in quotes, then the proof
        j = n + 1
        while j < len(lines) and lines[j].strip() in ("all-traces", "exists-trace", ""):
            j += 1
        if j < len(lines) and lines[j].lstrip().startswith('"'):
            k = j
            s = lines[k].lstrip()[1:]
            while '"' not in s and k + 1 < len(lines):
                k += 1
                s = lines[k]
            j = k + 1
        toks = []
        for tok in logical_lines(lines, j):
            if tok[0] == 0 and LEMMA_RE.match(tok[1]) or tok[1].startswith(("rule ", "restriction ",
                                                                             "end")) and tok[0] == 0:
                break
            toks.append(tok)
            if len(toks) > 2_000_000:
                break
        try:
            tree, used = parse_step(toks, 0)
            out[name] = (tree, None)
        except ProofSyntax as e:
            out[name] = (None, str(e))
    return out


def stats(tree):
    """Counts of a proof tree: steps (leaves included), depth, leaves by how they end, the
    methods, and the solve steps by goal kind (and contradictions by their note)."""
    st = {"size": 0, "depth": 0, "leaves": {}, "methods": {}, "solve_goal_kinds": {},
          "contradictions": {}}

    def go(node, d):
        st["size"] += 1
        st["depth"] = max(st["depth"], d)
        meth = node["method"]
        st["methods"][meth] = st["methods"].get(meth, 0) + 1
        if meth == "solve" and node.get("goal_kind"):
            k = node["goal_kind"]
            st["solve_goal_kinds"][k] = st["solve_goal_kinds"].get(k, 0) + 1
        if "end" in node:
            e = node["end"]
            st["leaves"][e] = st["leaves"].get(e, 0) + 1
            if e == "contradiction":
                n = node.get("note") or "unspecified"
                st["contradictions"][n] = st["contradictions"].get(n, 0) + 1
        for c in node.get("cases", []):
            go(c["proof"], d + 1)

    go(tree, 1)
    return st


def is_sorry(tree):
    return tree is not None and tree.get("end") == "sorry"


def extract_file(path, lemma=None):
    text = open(path, encoding="utf-8", errors="replace").read()
    res = lemma_proofs(text)
    if lemma:
        res = {k: v for k, v in res.items() if k == lemma}
    return res


def process_result(model_id, write_trees=True):
    """Add the counts of each lemma's proof to results/tamarin/<id>.json (and write the trees
    to proofs/<id>/<lemma>.json)."""
    r = benchlib.load_result("tamarin", model_id)
    if not r:
        return 0
    n = 0
    for lem in r.get("lemmas", []):
        p = benchlib.PROOFS / model_id / f"{lem['name']}.spthy"
        if not p.exists() or lem.get("verdict") not in ("verified", "falsified"):
            continue
        res = extract_file(p, lem["name"]).get(lem["name"])
        if not res:
            continue
        tree, err = res
        if err:
            lem["proof_stats"] = {"error": err}
            continue
        if is_sorry(tree):
            continue
        lem["proof_stats"] = stats(tree)
        if write_trees:
            benchlib.write_json(benchlib.PROOFS / model_id / f"{lem['name']}.json", tree)
        n += 1
    benchlib.write_json(benchlib.results_path("tamarin", model_id), r)
    return n


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("file", nargs="?", help="a Tamarin output file (default: every proof)")
    ap.add_argument("--lemma")
    ap.add_argument("--stats", action="store_true", help="print the counts, not the trees")
    a = ap.parse_args()
    if a.file:
        res = extract_file(a.file, a.lemma)
        out = {}
        for k, (tree, err) in res.items():
            out[k] = {"error": err} if err else (stats(tree) if a.stats else tree)
        json.dump(out, sys.stdout, indent=1, ensure_ascii=False)
        print()
        return
    total = 0
    for p in sorted((benchlib.RESULTS / "tamarin").rglob("*.json")):
        mid = str(p.relative_to(benchlib.RESULTS / "tamarin"))[:-len(".json")]
        total += process_result(mid)
        benchlib.backup_proofs(mid)
    print(f"{total} proofs extracted", file=sys.stderr)


if __name__ == "__main__":
    main()
