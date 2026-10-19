#!/usr/bin/env python3
"""Copy or fetch every model of the benchmark from its pinned source, and verify each file by
its sha256 in the manifest.

* A file that may be redistributed goes to models/<id>/ (committed), with the source's license
  text in models/<slug>/; a file that may not goes to cache/<id>/ (not committed).
* Every file is checked against the sha256 the manifest records; a mismatch is an error.
* By default a file already in place with the right sha256 is kept; --refetch reads every file
  from its source again (a clone that bench.local.toml lists under [mirrors], or a download at
  the pinned commit) and compares it with the copy.

Afterwards it writes every models/<id>/SOURCE.txt (scripts/gen_sources.py) unless --no-sources.

Usage:
  python3 -I scripts/fetch_models.py                     # everything
  python3 -I scripts/fetch_models.py --cache-only        # only what may not be redistributed (CI)
  python3 -I scripts/fetch_models.py --check             # verify the files in place, no network
  python3 -I scripts/fetch_models.py --refetch --no-mirrors   # compare every copy with the source
"""

import argparse
import os
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # -I leaves the script's dir out
import benchlib  # noqa: E402
import sources  # noqa: E402


def target_mode(entry):
    # Tamarin runs an oracle directly, so every oracle is made executable (the file's mode, not
    # its content: the sha256 is unchanged).
    if entry["role"] == "oracle" or entry.get("mode") == "100755":
        return 0o755
    return 0o644


def place(reader, by_id, source, home, entry, refetch, check, stats):
    dest = home / entry["dest"]
    want = entry["sha256"]
    if dest.exists() and not refetch:
        got = benchlib.sha256_file(dest)
        if got == want:
            if (dest.stat().st_mode & 0o777) != target_mode(entry) and not check:
                os.chmod(dest, target_mode(entry))
            stats["kept"] += 1
            return True
        if check:
            print(f"MISMATCH {dest}: sha256 {got}, the manifest records {want}", file=sys.stderr)
            stats["bad"] += 1
            return False
    elif check:
        print(f"MISSING {dest}", file=sys.stderr)
        stats["missing"] += 1
        return False
    src = by_id[entry.get("source", source["id"])]
    data, _ = reader.read(src, entry["path"])
    got = benchlib.sha256_bytes(data)
    if got != want:
        print(f"MISMATCH {src['id']}:{entry['path']}: sha256 {got}, the manifest records {want}",
              file=sys.stderr)
        stats["bad"] += 1
        return False
    if dest.exists() and benchlib.sha256_file(dest) == want:
        stats["verified"] += 1
    else:
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        stats["fetched"] += 1
    os.chmod(dest, target_mode(entry))
    return True


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--cache-only", action="store_true",
                    help="only the models that may not be redistributed (into cache/)")
    ap.add_argument("--only", help="only the models whose id starts with this")
    ap.add_argument("--check", action="store_true", help="verify the files in place; fetch nothing")
    ap.add_argument("--refetch", action="store_true",
                    help="read every file from its source again and compare it with the copy")
    ap.add_argument("--no-mirrors", action="store_true",
                    help="ignore the local clones of bench.local.toml and download")
    ap.add_argument("--no-sources", action="store_true", help="do not write the SOURCE.txt files")
    a = ap.parse_args()

    m = benchlib.load_manifest()
    cfg = benchlib.local_config()
    reader = sources.SourceReader(mirrors={} if a.no_mirrors else cfg.get("mirrors", {}))
    by_id = {s["id"]: s for s in m["source"]}
    stats = {"kept": 0, "fetched": 0, "verified": 0, "bad": 0, "missing": 0}
    models = {"copied": 0, "cached": 0}

    for s, x in benchlib.iter_models(m):
        if a.only and not x["id"].startswith(a.only):
            continue
        if a.cache_only and x["redistributable"]:
            continue
        home = benchlib.model_home(s, x)
        ok = all([place(reader, by_id, s, home, e, a.refetch, a.check, stats) for e in x["files"]])
        if ok:
            models["copied" if x["redistributable"] else "cached"] += 1

    # the license texts next to the copies
    if not a.cache_only:
        for s in m["source"]:
            for lc in s.get("license_copies", []):
                home = benchlib.MODELS / s["slug"]
                place(reader, by_id, s, home, lc, a.refetch, a.check, stats)

    print(f"models: {models['copied']} in models/, {models['cached']} in cache/; files: "
          f"{stats['kept']} in place, {stats['fetched']} fetched, {stats['verified']} re-verified "
          f"against the source, {stats['bad']} with a wrong sha256, {stats['missing']} missing",
          file=sys.stderr)
    if not a.no_sources and not a.check:
        import gen_sources
        gen_sources.main([])
    sys.exit(1 if stats["bad"] or stats["missing"] else 0)


if __name__ == "__main__":
    main()
