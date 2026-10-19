#!/usr/bin/env python3
"""Write models/<id>/SOURCE.txt for every model, from the manifest and results/tamarin/<id>.json.

A SOURCE.txt documents one model: the paper(s) it belongs to, as their DBLP records give them;
where the model is published and at which commit or archive; its files and their sha256; its
license and whether the file may be redistributed; how Tamarin is run on it; and how long
Tamarin takes on it, as measured here and as the authors (or Tamarin's own CI) report.

  python3 -I scripts/gen_sources.py            # write every SOURCE.txt
  python3 -I scripts/gen_sources.py --check    # fail if one differs from what it would write
"""

import argparse
import os
import sys
import textwrap

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # -I leaves the script's dir out
import benchlib  # noqa: E402

WIDTH = 96


def wrap(text, indent=""):
    return textwrap.fill(text, WIDTH, initial_indent=indent, subsequent_indent=indent,
                         break_long_words=False, break_on_hyphens=False)


def section(title):
    return [title, "-" * len(title)]


def paper_lines(p):
    out = []
    if p.get("dblp") == "found":
        out.append(wrap(", ".join(p["authors"]) + "."))
        out.append(wrap(p["title"]))
        where = p.get("venue") or p.get("school") or ""
        details = []
        if p.get("volume"):
            details.append(f"volume {p['volume']}")
        if p.get("number"):
            details.append(f"number {p['number']}")
        if p.get("pages"):
            details.append(f"pages {p['pages']}")
        out.append(wrap(", ".join(x for x in [where, p.get("year", "")] + details if x) + "."))
        if p.get("doi"):
            out.append(f"DOI:  {p['doi']}")
        elif p.get("document_url"):
            out.append(f"URL:  {p['document_url']}")
        out.append(f"DBLP: {p['dblp_url']}")
    else:
        out.append(wrap("DBLP has no record of this work (searched: "
                        + "; ".join(p.get("dblp_queries", [])) + ")."))
        out.append(wrap(f"What its own source states ({p.get('stated_by_source', 'the source')}):"))
        if p.get("source_authors"):
            out.append(wrap("Authors: " + ", ".join(p["source_authors"]), "  "))
        if p.get("source_title"):
            out.append(wrap("Title: " + p["source_title"], "  "))
        for k, label in (("source_type", "Type"), ("source_date", "Date"),
                         ("source_status", "Status")):
            if p.get(k):
                out.append(wrap(f"{label}: {p[k]}", "  "))
        if p.get("url"):
            out.append(f"  URL: {p['url']}")
    return out


def source_lines(s, x):
    out = []
    url = x["url"]
    if url.startswith("zip:"):
        archive, _, member = url[4:].partition("#")
        out.append(f"Archive: {archive}")
        out.append(f"  (the repository's DOI: {s['repo']})")
        out.append(f"File in the archive: {s.get('archive_root', '')}{x['path']}")
        out.append(f"Archive sha256: {s['archive_sha256']}")
    else:
        out.append(f"File:       {url}")
        out.append(f"Repository: {s['repo']}")
        out.append(f"Commit:     {s['commit']}")
        if s.get("ref"):
            out.append(wrap(f"Ref:        {s['ref']}"))
    return out


def tool_versions(r):
    return f"Tamarin {r.get('tamarin_version', '?')}, Maude {r.get('maude_version', '?')}"


def fmt_s(v):
    if v is None:
        return "-"
    return f"{v:.1f} s" if v >= 1 else f"{v:.2f} s"


def measured_lines(r):
    out = []
    host = r.get("host", "")
    out.append(wrap(f"Measured for this benchmark ({tool_versions(r)}, {r.get('rts', '')}, "
                    f"{host}, {r.get('date', '')}; limits {r['limits']['lemma_s']} s per lemma, "
                    f"{r['limits']['model_s']} s per model; results/tamarin/{r['id']}.json):"))
    if r.get("load", {}).get("status") not in (None, "ok"):
        out.append(wrap(f"Tamarin did not load the model: {r['load'].get('message', '')}", "  "))
    rows = []
    for lem in r.get("lemmas", []):
        kind = lem.get("kind", "")
        name = lem["name"] + (f" [{lem['side']}]" if lem.get("side") else "")
        verdict = lem.get("verdict", "")
        steps = f"{lem['steps']} steps" if lem.get("steps") is not None else ""
        rows.append((name, kind, verdict, steps, fmt_s(lem.get("wall_s"))))
    if rows:
        w = [max(len(row[i]) for row in rows) for i in range(5)]
        for row in rows:
            out.append("  " + "  ".join(row[i].ljust(w[i]) for i in range(4)) + "  "
                       + row[4].rjust(w[4]))
    tot = r.get("total_wall_s")
    if tot is not None:
        out.append(f"  total wall-clock time: {fmt_s(tot)}")
    if r.get("warnings"):
        out.append(wrap("Tamarin's wellformedness or derivation warnings: "
                        + "; ".join(r["warnings"])[:600], "  "))
    if r.get("notes"):
        for n in r["notes"]:
            out.append(wrap(n, "  "))
    return out


def tamarin_lines(s, x, r):
    out = section("Tamarin")
    args = " ".join(x.get("tamarin_args", []))
    env = " ".join(f"{k}={v}" for k, v in x.get("tamarin_env", {}).items())
    cmd = (env + " " if env else "") + "tamarin-prover +RTS -N4 -RTS " + (args + " " if args else "")
    out.append(wrap(f"Run here, one lemma at a time, in the model's directory: {cmd}"
                    f"--prove=<lemma> {benchlib.model_entry(x)['dest'].split('/')[-1]}"))
    out.append(wrap(f"Where the flags come from: {x.get('tamarin_args_basis', '')}."))
    out.append("")
    if r:
        out.extend(measured_lines(r))
    else:
        out.append("Measured for this benchmark: not run yet.")
    out.append("")
    reported = []
    if x.get("reported_time"):
        reported.append(f"Reported by the authors: {x['reported_time']}")
    hw = x.get("hardware") or s.get("hardware")
    if hw:
        reported.append(f"Hardware the authors state: {hw}")
    tv = x.get("tamarin_version_used") or s.get("tamarin_version_used")
    if tv:
        reported.append(f"Tamarin version the authors used: {tv}")
    if x.get("time_notes_in_file"):
        notes = x["time_notes_in_file"]
        notes = notes if isinstance(notes, list) else [notes]
        reported.append("Times stated in the file: " + "; ".join(str(n) for n in notes)[:600])
    if x.get("embedded_processing_time_s") is not None:
        reported.append(f"Processing time stated in the file: {x['embedded_processing_time_s']} s"
                        + (f" (Tamarin {x['embedded_tamarin_version']})"
                           if x.get("embedded_tamarin_version") else ""))
    for c in x.get("tamarin_ci", []):
        t = c.get("processing_time_s")
        reported.append(f"Tamarin's own CI ({c.get('file')}): processing time "
                        f"{t if t is not None else '?'} s with Tamarin {c.get('tamarin_version')}, "
                        f"flags {c.get('flags')}, on {c.get('machine')}")
    if not reported:
        reported.append("The authors report no time for this model.")
    for line in reported:
        out.append(wrap(line))
    return out


def render(m, s, x, papers):
    lines = [x["id"], "=" * len(x["id"]), ""]
    model = benchlib.model_entry(x)
    if x["redistributable"]:
        lines.append(wrap(f"The model file is {model['dest']} in this directory."))
    else:
        lines.append(wrap(f"The model file is not stored here (see License): "
                          f"scripts/fetch_models.py fetches it to cache/{x['id']}/{model['dest']}."))
    if x.get("theory"):
        lines.append(f"Theory: {x['theory']}")
    lines.append("")
    keys = x.get("paper", [])
    lines.extend(section("Paper" if len(keys) == 1 else "Papers"))
    for i, k in enumerate(keys):
        if i:
            lines.append("")
        lines.extend(paper_lines(papers[k]))
    if x.get("paper_basis"):
        lines.append(wrap(f"(Why this paper: {x['paper_basis']}.)"))
    lines.append("")
    lines.extend(section("Online source"))
    lines.extend(source_lines(s, x))
    lines.append("")
    lines.extend(section("Files"))
    for f in x["files"]:
        where = f"{f['source']}: " if f.get("source") else ""
        lines.append(wrap(f"{f['role']}: {where}{f['path']} -> {f['dest']}"))
        lines.append(f"  sha256 {f['sha256']}")
    lines.append("")
    lines.extend(section("License"))
    lines.append(wrap(f"{x.get('license', s.get('license_spdx'))}. {x['redistributable_reason']}."))
    if x["redistributable"]:
        lic = ", ".join(f"models/{s['slug']}/{c['dest']}" for c in s.get("license_copies", []))
        lines.append(wrap("The files are copied here unchanged"
                          + (f"; the license text is in {lic}." if lic else ".")))
    else:
        lines.append(wrap("The files are not copied into this repository; scripts/fetch_models.py "
                          "fetches them at the pinned commit and checks their sha256."))
    lines.append("")
    r = benchlib.load_result("tamarin", x["id"])
    lines.extend(tamarin_lines(s, x, r))
    lines.append("")
    lines.extend(section("Lean side"))
    lines.append(wrap(x.get("lean_scope", "")))
    return "\n".join(lines) + "\n"


def akma_notice(s):
    return "\n".join([
        "The AKMA+ model files",
        "=====================",
        "",
        wrap("The GitHub repository " + s["repo"] + " states no license.  The authors' Zenodo "
             "deposit of the same files (https://doi.org/10.5281/zenodo.14649847, "
             "AKMA-Plus-Tamarin.zip, byte-identical by sha256 to the pinned commit) is licensed "
             "under the Creative Commons Attribution 4.0 International license (CC BY 4.0), "
             "https://creativecommons.org/licenses/by/4.0/legalcode ."),
        "",
        wrap("Attribution: the files are the authors' Tamarin model of AKMA+, from the "
             "artifact of the paper listed in each SOURCE.txt; they are copied unchanged."),
    ]) + "\n"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                    help="report SOURCE.txt files that differ from what this would write")
    a = ap.parse_args(argv)
    m = benchlib.load_manifest()
    papers = benchlib.papers_by_key(m)
    stale = 0
    outputs = {}
    for s, x in benchlib.iter_models(m):
        outputs[benchlib.MODELS / x["id"] / "SOURCE.txt"] = render(m, s, x, papers)
    for s in m["source"]:
        if s["slug"] == "akma-plus" and s["redistributable"]:
            outputs[benchlib.MODELS / s["slug"] / "LICENSE"] = akma_notice(s)
    for path, text in outputs.items():
        old = path.read_text(encoding="utf-8") if path.exists() else None
        if old != text:
            stale += 1
            if not a.check:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            else:
                print(f"stale: {path.relative_to(benchlib.ROOT)}", file=sys.stderr)
    print(f"{len(outputs)} files, {stale} {'stale' if a.check else 'written'}", file=sys.stderr)
    if a.check and stale:
        sys.exit(1)


if __name__ == "__main__":
    main()
