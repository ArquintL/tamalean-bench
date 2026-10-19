#!/usr/bin/env python3
"""Add to the manifest what the scripts need to fetch and run each model.

For every entry of kind "model" it adds, when missing:

* `id`: a short, stable slug of the source and the path (never changed once assigned);
* `files`: the model file, the files it #includes and the oracles it is run with, each with its
  path in the source, its place under models/<id>/ (`dest`) and its sha256 at the pinned commit;
* `tamarin_args` (and `tamarin_env`): the flags Tamarin runs the model with, beyond the lemma to
  prove and the output file, and `tamarin_args_basis`, where they come from;
* `lean_scope`: whether the Lean side runs it (observational equivalence is out of its scope).

It reads the files through scripts/sources.py: from the local clones that bench.local.toml lists
under [mirrors], or by downloading them at the pinned commits.  Run it with `python3 -I`.
"""

import argparse
import os
import posixpath
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # -I leaves the script's dir out
import benchlib  # noqa: E402
import sources  # noqa: E402

# Source id -> (slug, path prefixes dropped from the id)
SLUGS = {
    "tamarin-prover@1.10.0": ("tamarin", ["examples/"]),
    "tamarin-prover@develop": ("tamarin-dev", ["examples/"]),
    "EMVrace/EMVerify": ("emv/emverify", []),
    "EMVrace/EMVerify-PAN-routing": ("emv/pan-routing", ["models-n-proofs/"]),
    "EMVrace/auth-failure-attack": ("emv/auth-failure", []),
    "viperproject/protocol-verification-refinement": ("tamigloo", []),
    "viperproject/diodon-artifact": ("diodon", []),
    "freedomofpress/securedrop-protocol-models": ("securedrop", []),
    "lumaier/securedrop-formalanalysis": ("securedrop-thesis", ["models/"]),
    "tamarin-pq3/tamarin-pq3": ("pq3", []),
    "AKMA-Plus/AKMA-Plus-Tamarin": ("akma-plus", []),
    "gitlab:anonym_123/anon_payments": ("emv/more-is-less", ["tamarin_models/"]),
    "xiaofeng-L/BLETracker": ("ble-tracking", []),
    "zenodo:16736982 (WireGuard hybridization)": ("wg-hybrid", ["artifacts_evaluation/"]),
    "pure-uwb/pure-models": ("emv/pure", []),
    "zenodo:15357178 (One For All, aggregate signatures)": ("one-for-all", []),
}

# The two archives: where they are downloaded from, and the directory their files are under.
ARCHIVES = {
    "zenodo:16736982 (WireGuard hybridization)": {
        "archive_url": "https://zenodo.org/api/records/16736982/files/"
                       "artifacts-usenix-2025-wireguard-hybridization.zip/content",
        "archive_sha256": "7ccd000f2c785aa83318bceea5218742c57a2c40eb8c37b98488752f1e2273e7",
        "archive_root": "artifacts-usenix-2025-wireguard-hybridization/",
    },
    "zenodo:15357178 (One For All, aggregate signatures)": {
        "archive_url": "https://zenodo.org/api/records/15357178/files/"
                       "tamarin-aggregate-signatures.zip/content",
        "archive_sha256": "101a4756c17638c7e076ad76e7bfc69a6f4fdbba8dbe6da86ff0d0aeb36d7268",
        "archive_root": "tamarin-aggregate-signatures/",
    },
}

# The license text kept next to the copies of each redistributable source: (path in the
# source, file name under models/<slug>/).  The WireGuard archive states GPL-3.0 in its README
# and has no license file; Tamarin's LICENSE is the GPL-3.0 text.
LICENSE_FILES = {
    "tamarin-prover@1.10.0": [("LICENSE", "LICENSE")],
    "tamarin-prover@develop": [("LICENSE", "LICENSE")],
    "viperproject/protocol-verification-refinement": [("LICENSE", "LICENSE")],
    "viperproject/diodon-artifact": [("license.txt", "LICENSE")],
    "freedomofpress/securedrop-protocol-models": [("LICENSE", "LICENSE")],
    "tamarin-pq3/tamarin-pq3": [("LICENSE", "LICENSE")],
    "zenodo:15357178 (One For All, aggregate signatures)": [("LICENSE", "LICENSE")],
    "zenodo:16736982 (WireGuard hybridization)": [
        ("README.md", "README.md"), ("LICENSE", "LICENSE", "tamarin-prover@1.10.0")],
}

DEV_LETTER_o = ("csf18-alethea", "eurosp19-eccDAA/observationalEquivalence", "wisec21-5G-handover",
                "csf21-acc-unbounded")


def make_id(source, model):
    slug, strip = SLUGS[source["id"]]
    p = model["path"]
    for st in strip:
        if p.startswith(st):
            p = p[len(st):]
            break
    p = re.sub(r"\.spthy$", "", p)
    comps = [re.sub(r"[^A-Za-z0-9_+-]", "_", c) for c in p.split("/")]
    return slug + "/" + "/".join(comps)


def check_ids(ids):
    """Ids must differ ignoring case (macOS file systems), and no model's directory may contain
    another model's."""
    low = sorted(i.lower() for i in ids)
    dup = {i for i in low if low.count(i) > 1}
    if dup:
        raise SystemExit(f"ids that differ only in case: {sorted(dup)}")
    s = set(low)
    for i in low:
        parts = i.split("/")
        for k in range(1, len(parts)):
            if "/".join(parts[:k]) in s:
                raise SystemExit(f"the id {'/'.join(parts[:k])} is a directory of {i}")


INCLUDE_RE = re.compile(r'^\s*#include\s+"([^"]+)"', re.M)


def includes(reader, source, path, seen=None):
    """The files `path` #includes, transitively, resolved against the including file's dir."""
    seen = seen if seen is not None else set()
    data, _ = reader.read(source, path)
    out = []
    for inc in INCLUDE_RE.findall(data.decode("utf-8", "replace")):
        p = posixpath.normpath(posixpath.join(posixpath.dirname(path), inc))
        if p in seen:
            continue
        seen.add(p)
        out.append(p)
        out.extend(includes(reader, source, p, seen))
    return out


def text_of(model):
    return " || ".join(model.get("oracle_basis", []) + [str(model.get("run_flags") or "")]
                       + list(model.get("commands_in_file") or []))


def theory_oracle(model):
    """True when the theory file itself names the oracle (a `heuristic:` line or a lemma
    attribute), so that Tamarin needs no flag for it."""
    return any(b.startswith(("theory file", "lemma attribute")) for b in model.get("oracle_basis", []))


def oracle_letter(source, model):
    found = re.findall(r"--heuristics?=([oO])\b", text_of(model))
    if found:
        return found[0], "the command the authors give"
    if any(d in model["path"] for d in DEV_LETTER_o):
        return "o", "the directory's README"
    return "O", "the directory's README"


def bluetooth_config(reader, source, model):
    """The first configuration the Bluetooth README lists for this model (its -D flags)."""
    readme, _ = reader.read(source, "examples/esorics23-bluetooth/README.md")
    name = posixpath.basename(model["path"])
    for line in readme.decode().splitlines():
        line = line.strip()
        if line.startswith(f"tamarin-prover {name} "):
            return [a for a in line.split()[2:] if a.startswith("-D")]
    return []


SP14 = {  # examples/sp14/run.sh: the configuration of each model it runs (the first one)
    "STR.spthy": ["-Dsecure"], "GDH.spthy": ["-Dsecure"], "RYY.spthy": ["-Dsecure"],
    "Chen_Kudla.spthy": ["-Dsecure"],
}


def derive_args(reader, source, model, oracle_dests):
    """The flags Tamarin runs the model with, the environment, and where they come from."""
    sid, path = source["id"], model["path"]
    rf = str(model.get("run_flags") or "")
    ci = " ".join(c.get("flags", "") for c in model.get("tamarin_ci", []))
    cmds = " ".join(model.get("commands_in_file") or [])
    args, env, basis = [], {}, []

    if model.get("diff"):
        args.append("--diff")
        basis.append("--diff: the model states observational equivalence")

    # proof-search sources
    auto = "--auto-source" in ci
    if sid == "tamarin-prover@develop" and "csf26-ac" in path:
        auto = "toy_voting_system" in path
    elif re.search(r"--auto-sources?\b", rf):
        auto = True
    if auto:
        args.append("--auto-sources")
        basis.append("--auto-sources: " + ("Tamarin's own CI command" if "--auto-source" in ci
                                           else "the authors' command (README or Makefile)"))

    for flag in ("--derivcheck-timeout=\\d+", "--quit-on-warning", "--bound=\\d+"):
        mm = re.search(flag, rf + " " + cmds)
        if mm:
            args.append(mm.group(0))
            basis.append(f"{mm.group(0)}: the authors' command")

    st = re.search(r"--stop-on-trace=(\w+)", cmds + " " + rf)
    if st and st.group(1).lower() != "dfs":
        if not (sid == "tamarin-prover@develop" and "exponential_mixnet" not in path):
            args.append(st.group(0))
            basis.append(f"{st.group(0)}: the authors' command")
    elif "--stop-on-trace=seqdfs" in ci:
        args.append("--stop-on-trace=seqdfs")
        basis.append("--stop-on-trace=seqdfs: Tamarin's own CI command")

    # non-oracle heuristics given on the command line
    if "--heuristic=S" in rf:
        args.append("--heuristic=S")
        basis.append("--heuristic=S: README")
    if "heuristics=P" in rf or "--heuristic=P" in rf:
        args.append("--heuristic=P")
        basis.append("--heuristic=P: README")

    # configuration macros
    name = posixpath.basename(path)
    if sid == "tamarin-prover@1.10.0" and path.startswith("examples/sp14/") and name in SP14:
        args.extend(SP14[name])
        basis.append(f"{' '.join(SP14[name])}: examples/sp14/run.sh (its first configuration)")
        if name == "GDH.spthy":
            env["TAMARIN_EXTENSIVE_SPLIT"] = "1"
            basis.append("TAMARIN_EXTENSIVE_SPLIT=1: examples/sp14/run.sh")
    if sid == "tamarin-prover@1.10.0" and path.startswith("examples/esorics23-bluetooth/"):
        d = bluetooth_config(reader, source, model)
        args.extend(d)
        basis.append("the -D flags of the first configuration the README lists for the model")

    # the oracle, when the command line names it
    cli = [o for o in oracle_dests if o["cli"]]
    if cli:
        letter, why = oracle_letter(source, model)
        if model.get("_letter"):
            letter, why = model["_letter"], model["_letter_why"]
        args += [f"--heuristic={letter}", f"--oraclename={cli[0]['dest_rel']}"]
        basis.append(f"--heuristic={letter} --oraclename: {why}")
    elif oracle_dests:
        basis.append("the oracle is named in the theory file (no flag needed)")
    if not basis:
        basis.append("no flags: the source gives none for this model")
    return args, env, "; ".join(basis)


# Per-model corrections of the oracle the manifest records (source id, path) -> oracle paths
# (with the source each one is read from) and the heuristic letter.
ORACLE_OVERRIDES = {
    ("EMVrace/EMVerify", "Contactless.spthy"): (
        [("EMVrace/EMVerify", "Mastercard.oracle")], "O",
        "Makefile: the default kernel is Mastercard (--heuristic=O --oraclename=Mastercard.oracle)"),
    ("EMVrace/auth-failure-attack", "Contactless.spthy"): (
        [("EMVrace/EMVerify", "Mastercard.oracle")], "O",
        "README: EMVerify's Makefile with kernel=Mastercard (--heuristic=O "
        "--oraclename=Mastercard.oracle, from EMVerify)"),
    ("EMVrace/EMVerify-PAN-routing", "models-n-proofs/Contactless_HardFix.spthy"): (
        [("EMVrace/EMVerify-PAN-routing", "Visa.oracle")], "O",
        "Makefile: the default brand is Visa (--heuristic=O --oraclename=Visa.oracle)"),
    ("EMVrace/EMVerify-PAN-routing", "models-n-proofs/Contactless_SoftFix.spthy"): (
        [("EMVrace/EMVerify-PAN-routing", "Visa.oracle")], "O",
        "Makefile: the default brand is Visa (--heuristic=O --oraclename=Visa.oracle)"),
}


def layout(model_path, entries):
    """Where each file goes under models/<id>/: at its path relative to the model's directory,
    except an oracle named on the command line from outside it, which goes next to the model.
    When an include or an oracle the theory names lies outside the model's directory, the files
    keep their paths relative to the deepest directory that contains them all."""
    mdir = posixpath.dirname(model_path)
    rel = {}
    outside = False
    for e in entries:
        r = posixpath.relpath(e["path"], mdir) if mdir else e["path"]
        if r.startswith("../"):
            if e["role"] == "oracle" and e.get("cli"):
                r = posixpath.basename(e["path"])
            else:
                outside = True
        rel[e["path"]] = r
    if outside:
        dirs = [posixpath.dirname(e["path"]) for e in entries if not e.get("cli")]
        root = posixpath.commonpath(dirs) if all(dirs) else ""
        for e in entries:
            if not e.get("cli"):
                rel[e["path"]] = posixpath.relpath(e["path"], root) if root else e["path"]
    return rel


def curate(m, reader, only=None):
    by_id = {s["id"]: s for s in m["source"]}
    for s in m["source"]:
        slug = SLUGS[s["id"]][0]
        s.setdefault("slug", slug)
        if s["id"] in ARCHIVES:
            for k, v in ARCHIVES[s["id"]].items():
                s.setdefault(k, v)
        if s["redistributable"] and s["id"] in LICENSE_FILES and "license_copies" not in s:
            copies = []
            for t in LICENSE_FILES[s["id"]]:
                c = {"role": "license", "path": t[0], "dest": t[1]}
                if len(t) > 2:
                    c["source"] = t[2]
                data, _ = reader.read(by_id[c.get("source", s["id"])], c["path"])
                c["sha256"] = benchlib.sha256_bytes(data)
                copies.append(c)
            s["license_copies"] = copies

    ids = []
    for s in m["source"]:
        for x in s.get("model", []):
            if x["kind"] != "model":
                continue
            x.setdefault("id", make_id(s, x))
            ids.append(x["id"])
    check_ids(ids)

    n = 0
    for s in m["source"]:
        for x in s.get("model", []):
            if x["kind"] != "model" or (only and not x["id"].startswith(only)):
                continue
            if "files" in x and "tamarin_args" in x:
                continue
            n += 1
            entries = [{"role": "model", "path": x["path"], "source": s["id"]}]
            for inc in includes(reader, s, x["path"]):
                entries.append({"role": "include", "path": inc, "source": s["id"]})
            key = (s["id"], x["path"])
            if key in ORACLE_OVERRIDES:
                orcs, letter, why = ORACLE_OVERRIDES[key]
                x["_letter"], x["_letter_why"] = letter, why
                for src, p in orcs:
                    entries.append({"role": "oracle", "path": p, "source": src, "cli": True})
            else:
                cli = not theory_oracle(x)
                for p in x.get("oracle", []):
                    entries.append({"role": "oracle", "path": p, "source": s["id"], "cli": cli})
            rel = layout(x["path"], [e for e in entries if e["source"] == s["id"]] +
                            [dict(e, path=posixpath.join(posixpath.dirname(x["path"]),
                                                         posixpath.basename(e["path"])))
                             for e in entries if e["source"] != s["id"]])
            files = []
            for e in entries:
                src = by_id[e["source"]]
                data, mode = reader.read(src, e["path"])
                lookup = e["path"] if e["source"] == s["id"] else posixpath.join(
                    posixpath.dirname(x["path"]), posixpath.basename(e["path"]))
                f = {"role": e["role"], "path": e["path"], "dest": rel[lookup],
                     "sha256": benchlib.sha256_bytes(data), "bytes": len(data)}
                if e["source"] != s["id"]:
                    f["source"] = e["source"]
                if mode:
                    f["mode"] = mode
                files.append(f)
                e["dest_rel"] = posixpath.relpath(
                    rel[lookup], posixpath.dirname(rel[x["path"]]) or ".")
            x["files"] = files
            odests = [e for e in entries if e["role"] == "oracle"]
            args, env, basis = derive_args(reader, s, x, odests)
            x.pop("_letter", None)
            x.pop("_letter_why", None)
            x["tamarin_args"] = args
            if env:
                x["tamarin_env"] = env
            x["tamarin_args_basis"] = basis
            if x.get("diff"):
                x["lean_scope"] = ("out of scope: observational equivalence (a diff model); "
                                   "Tamalean checks trace properties only")
            else:
                x["lean_scope"] = "trace properties"
    return n


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--only", help="curate only the models whose id starts with this")
    ap.add_argument("--offline", action="store_true", help="read local clones only")
    a = ap.parse_args()
    cfg = benchlib.local_config()
    reader = sources.SourceReader(mirrors=cfg.get("mirrors", {}), offline=a.offline)
    m = benchlib.load_manifest()
    n = curate(m, reader, a.only)
    meta = m["meta"]
    meta.pop("installed_tamarin", None)
    meta["curated"] = ("ids, files (with sha256), tamarin_args and lean_scope added by "
                       "scripts/curate_manifest.py")
    benchlib.dump_manifest(m, header=benchlib.MANIFEST_HEADER)
    print(f"curated {n} models", file=sys.stderr)


if __name__ == "__main__":
    main()
