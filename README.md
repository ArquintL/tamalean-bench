# tamalean-bench

A benchmark of Tamarin models for [Tamalean](https://github.com/ArquintL/tamalean), the
kernel-checked reimplementation of Tamarin's constraint solving in Lean. It lives in its own
repository so that Tamalean's CI does not run it on every push: a run here tests the Tamalean
commit that the `tamalean` submodule pins, and bumping the submodule is how a new version enters
the benchmark.

## What is in it

- `models/manifest.toml` lists the sources (repositories at pinned commits, archives pinned by
  their sha256), every `.spthy` file in them, and the papers they belong to, with the fields of
  each paper's DBLP record. Each model of the benchmark has an `id`, its files (the model, the
  files it includes, its oracle) with their sha256, the flags Tamarin runs it with
  (`tamarin_args`, and `tamarin_args_basis` for where they come from), and its scope on the Lean
  side (`lean_scope`). Stored proofs, generated targets and variants that do not terminate are
  listed without an id.
- `models/<id>/` holds each model: its files, copied unchanged when their license allows it, and
  a `SOURCE.txt` that documents it: the paper(s) it belongs to (authors, title, venue, year and
  DOI as the DBLP record gives them, and the link to the record), the link to the online source,
  the commit or archive hash, the license and why the files may or may not be copied, the flags
  Tamarin runs it with, and how long Tamarin takes on it, as measured here and as its authors or
  Tamarin's own CI report it. `models/<source>/` holds the license text of each source whose
  files are copied. A model that may not be redistributed has only its `SOURCE.txt` here;
  `scripts/fetch_models.py` fetches its files into `cache/<id>/`.
- `Bench/<id>.lean` is the Lean side of one model: the model read by Tamalean's `.spthy` reader
  and one `certify` per lemma, generated from the manifest. `Bench/Harness.lean` has the commands
  these modules use; `Bench.lean` imports only the harness.
- `results/tamarin/<id>.json` and `results/tamalean/<id>.json` are each tool's committed results
  per model; `results/summary.md` sums them up; `results/tamarin/long-runs.txt` lists the lemmas
  and models that reached a limit here, for a run with more time or memory;
  `results/tamarin/progress.txt` logs the Tamarin runs in the order they finished.
- `heuristics/` is for model-specific search heuristics, the counterpart of Tamarin's oracles and
  tactics for Tamalean's search (none yet).

Not committed: `cache/` (the models that may not be redistributed, and downloaded archives),
`proofs/` (the proofs Tamarin finds: its `--output` file per lemma, and its tree as JSON),
`runs/` (the raw output of every run) and `bench.local.toml` (the settings of one machine).

## How results are compared

A comparison is only meaningful at equal guidance. Every result says which of three settings it
belongs to (its `setting` field), and results are compared only within one setting:

1. **No guidance.** Tamarin's built-in heuristic against `certify` with the model's default
   sources.
2. **A ranking.** Tamarin with the model's oracle, heuristic or tactic against Tamalean's search
   with a model-specific heuristic from `heuristics/`.
3. **A finished proof.** Tamarin's saved proof replayed by Tamalean and checked by Lean's kernel.
   This measures checking, not search.

Tamarin runs each model with the flags and the oracle its authors give, so a model with an oracle
belongs to the second setting. The Lean side runs bare `certify`, the first setting.

## The scripts

The scripts need Python 3.11 or later and nothing else, and run with `python3 -I` from any
directory. Each prints its options with `--help`.

| script | what it does |
|---|---|
| `scripts/fetch_models.py` | Copies or fetches every model's files from its pinned source into `models/<id>/` (redistributable) or `cache/<id>/` (not), checks each file's sha256 against the manifest, and writes every `SOURCE.txt`. `--cache-only` fetches only what may not be redistributed; `--check` verifies the files in place; `--refetch --no-mirrors` downloads everything again and compares it with the copies. |
| `scripts/gen_sources.py` | Writes every `models/<id>/SOURCE.txt` from the manifest and `results/tamarin/`; `--check` reports the ones that differ. |
| `scripts/run_tamarin.py` | Runs Tamarin on each model, one lemma at a time (`--prove=<lemma>`), in the model's directory, with the model's flags and oracle, `+RTS -N4 -M8G -RTS`, a limit per lemma (600 s) and per model (1800 s); writes `results/tamarin/<id>.json`, the proofs under `proofs/<id>/` and their backup, `long-runs.txt` and `progress.txt`. `--plan` prints the order: the papers run first, one model from every directory of Tamarin's examples, then the rest. |
| `scripts/extract_proofs.py` | Reads Tamarin's proof scripts into a JSON tree per lemma (`proofs/<id>/<lemma>.json`) and adds each proof's size, depth, leaves and `solve` steps by goal kind to `results/tamarin/<id>.json`. With a file argument it prints the trees of that file. |
| `scripts/gen_lean.py` | Writes `Bench/<id>.lean` for every model of trace properties; `--check` reports stale modules. |
| `scripts/run_lean.py` | Runs each `Bench/<id>.lean` with `lake lean`, which loads Tamalean's precompiled engine, and writes `results/tamalean/<id>.json`: whether the reader accepted the model (or why not), and per lemma `proved`, `attack found`, `no trace`, `no verdict` (with the first line of `certify`'s report) or `timeout`, with its time. |
| `scripts/summarize.py` | Writes `results/summary.md`: both tools' outcomes per source and overall, the reasons for the reader's rejections, and a table per lemma for the papers run first. |
| `scripts/validate.py` | Checks the manifest, the copies under `models/` and every `SOURCE.txt` against each other. |
| `scripts/curate_manifest.py` | Adds the id, the files with their sha256 and the Tamarin flags to new models of the manifest. |

### Running it

```sh
git submodule update --init tamalean   # private: needs access to Tamalean
python3 -I scripts/fetch_models.py     # the models that may not be redistributed go to cache/

# Tamarin (the committed results are Tamarin 1.12.0 with Maude 3.5.1)
python3 -I scripts/run_tamarin.py --jobs 2
python3 -I scripts/extract_proofs.py

# Lean
lake exe cache get && lake build
python3 -I scripts/run_lean.py

python3 -I scripts/gen_sources.py && python3 -I scripts/summarize.py
```

The settings of one machine go in `bench.local.toml` (not committed) or the environment:
`proof_backup` or `BENCH_PROOF_BACKUP` (a directory the proofs are copied to), `python2` or
`BENCH_PYTHON2` (a Python 2 interpreter for the oracles written for Python 2), and `[mirrors]`
(a local clone or archive per source id, read instead of downloading). `BENCH_LOCK` names a
command that every Tamarin process, and every `lake` call of `run_lean.py`, is started through,
such as a lock that shares a machine's build slots; the time spent waiting for it is not counted.

### Oracles

Tamarin runs an oracle directly, by its interpreter line, and many oracles of these models are
written for Python 2 and name `/usr/bin/python`. Where the interpreter an oracle names does not
exist, the runner leaves the oracle file unchanged and runs it with an interpreter of its
language (Python 2 for an oracle that is not Python 3 syntax). Each result lists under
`oracle_notes` how its oracles ran.

## CI

Every push runs `.github/workflows/bench.yml` on GitHub's runners:

1. **Manifest and SOURCE.txt files**: `scripts/validate.py`, which needs neither Lean nor
   Tamalean.
2. **Build**: fetches the private `tamalean` submodule with the read-only deploy key in the
   secret `TAMALEAN_DEPLOY_KEY`, installs elan, restores the build cache (keyed by the toolchain,
   the packages and the submodule's commit), fetches Mathlib's build of the modules Tamalean
   imports with `lake exe cache get`, runs `lake build`, and saves the cache.
3. **Lean side**, in four shards: fetches the models that may not be redistributed and runs
   `scripts/run_lean.py` on its share, with 300 s per lemma and 900 s per model, and uploads its
   results.
4. **Summary**: merges the shards, runs `scripts/summarize.py`, and uploads `results/` as the
   artifact `results`.

Tamarin does not run in CI: its runs take hours to days, so the committed results under
`results/tamarin/` stand for it. Tamalean's own CI never runs this benchmark.
