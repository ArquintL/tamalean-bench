# tamalean-bench

A benchmark of Tamarin models for [Tamalean](https://github.com/ArquintL/tamalean), the
kernel-checked reimplementation of Tamarin's constraint solving in Lean. It lives in its own
repository so that Tamalean's CI does not run it on every push: a run here tests the Tamalean
commit that the `tamalean` submodule pins, and bumping the submodule is how a new version enters
the benchmark.

## What is in it

- `models/<id>/` holds each model as its authors published it, with its oracle where it has one,
  and a `SOURCE.txt` that documents it: the paper it belongs to, with a BibTeX entry to cite it;
  the link to the online source; the commit or version; the license; and how long Tamarin takes on
  it. `models/manifest.toml` lists all of them, and
  `scripts/fetch_models.py` fetches them again from the pinned commits to check the copies.
- `scripts/` runs Tamarin on the models, extracts its proofs, and generates and runs the Lean side.
  The proofs Tamarin finds are stored under `proofs/`, which is not committed: run the scripts to
  produce them.
- `Bench/` holds one Lean module per model, generated from the manifest: the model read by
  Tamalean's `.spthy` reader and one `certify` per lemma.
- `heuristics/` holds model-specific search heuristics: the counterpart of Tamarin's oracles and
  tactics for Tamalean's search.
- `results/` holds the committed summaries of each run: per lemma the verdict, the time and the
  size of the proof, for both tools.

## How results are compared

A comparison is only meaningful at equal guidance. Every result says which of three settings it
belongs to, and results are compared only within one setting:

1. **No guidance.** Tamarin's built-in heuristic against `certify` with the model's default
   sources.
2. **A ranking.** Tamarin with the model's oracle or tactic against Tamalean's search with a
   model-specific heuristic from `heuristics/`.
3. **A finished proof.** Tamarin's saved proof replayed by Tamalean and checked by Lean's kernel.
   This measures checking, not search.

## CI

Every push runs the benchmark. Tamalean's own CI never runs it: this repository exists so that
Tamalean's CI stays as fast as it is.
