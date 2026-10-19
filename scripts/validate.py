#!/usr/bin/env python3
"""Check the manifest, the copies under models/ and every SOURCE.txt against each other.

* The manifest reads, every model of the benchmark has an id, its files with their sha256, its
  Tamarin flags and its Lean scope; ids differ ignoring case and no model's directory contains
  another's; every paper a model names is in the manifest.
* Every file that may be redistributed is in models/<id>/ with the sha256 the manifest records,
  and no file that may not be redistributed is there; every directory under models/ with a
  SOURCE.txt belongs to a model; the license texts are next to the copies.
* Every SOURCE.txt is what scripts/gen_sources.py writes from the manifest and the results.
* Every result under results/ belongs to a model of the manifest.

  python3 -I scripts/validate.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # -I leaves the script's dir out
import benchlib  # noqa: E402
import gen_sources  # noqa: E402

REQUIRED = ("id", "files", "tamarin_args", "lean_scope", "url", "paper", "license",
            "redistributable", "redistributable_reason")


def main():
    errors = []
    m = benchlib.load_manifest()
    papers = benchlib.papers_by_key(m)
    ids = []
    for s in m["source"]:
        for k in ("id", "slug", "repo", "commit", "license_spdx", "redistributable"):
            if k not in s:
                errors.append(f"source {s.get('id')}: no `{k}`")
        for x in s.get("model", []):
            if x.get("kind") == "model" and "id" not in x:
                errors.append(f"{s['id']}:{x['path']}: a model without an id")
            if "id" not in x:
                continue
            ids.append(x["id"])
            for k in REQUIRED:
                if k not in x:
                    errors.append(f"{x['id']}: no `{k}`")
            for p in x.get("paper", []):
                if p not in papers:
                    errors.append(f"{x['id']}: unknown paper {p}")
            roles = [f["role"] for f in x.get("files", [])]
            if roles.count("model") != 1:
                errors.append(f"{x['id']}: {roles.count('model')} files with role model")
            for f in x.get("files", []):
                if len(f.get("sha256", "")) != 64:
                    errors.append(f"{x['id']}: {f.get('path')}: no sha256")
                dest = benchlib.MODELS / x["id"] / f["dest"]
                if x["redistributable"]:
                    if not dest.exists():
                        errors.append(f"{x['id']}: missing copy {dest.relative_to(benchlib.ROOT)}")
                    elif benchlib.sha256_file(dest) != f["sha256"]:
                        errors.append(f"{x['id']}: {dest.relative_to(benchlib.ROOT)} differs "
                                      "from the sha256 in the manifest")
                elif dest.exists():
                    errors.append(f"{x['id']}: {dest.relative_to(benchlib.ROOT)} may not be "
                                  "redistributed, but is in models/")
        if s.get("redistributable") and any("id" in x and x["redistributable"]
                                           for x in s.get("model", [])):
            for c in s.get("license_copies", []):
                p = benchlib.MODELS / s["slug"] / c["dest"]
                if not p.exists() or benchlib.sha256_file(p) != c["sha256"]:
                    errors.append(f"{s['id']}: license text {p.relative_to(benchlib.ROOT)} "
                                  "missing or changed")
    low = [i.lower() for i in ids]
    if len(set(low)) != len(low):
        errors.append("ids that differ only in case")
    ls = set(low)
    for i in low:
        parts = i.split("/")
        for k in range(1, len(parts)):
            if "/".join(parts[:k]) in ls:
                errors.append(f"the directory of {'/'.join(parts[:k])} contains {i}")
    known = set(ids)
    for p in benchlib.MODELS.rglob("SOURCE.txt"):
        mid = str(p.parent.relative_to(benchlib.MODELS))
        if mid not in known:
            errors.append(f"models/{mid}/SOURCE.txt belongs to no model of the manifest")
    for tool in ("tamarin", "tamalean"):
        d = benchlib.RESULTS / tool
        if d.exists():
            for p in d.rglob("*.json"):
                mid = str(p.relative_to(d))[:-len(".json")]
                if mid not in known:
                    errors.append(f"results/{tool}/{mid}.json belongs to no model of the manifest")
    try:
        gen_sources.main(["--check"])
    except SystemExit as e:
        if e.code:
            errors.append("some SOURCE.txt files are not what scripts/gen_sources.py writes")
    for e in errors[:200]:
        print(e, file=sys.stderr)
    print(f"{len(ids)} models, {len(errors)} problems", file=sys.stderr)
    sys.exit(1 if errors else 0)


if __name__ == "__main__":
    main()
