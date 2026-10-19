# tamalean-bench

A benchmark of Tamarin models for [Tamalean](https://github.com/ArquintL/tamalean), the
kernel-checked reimplementation of Tamarin's constraint solving in Lean. It lives in its own
repository so that Tamalean's CI does not run it on every push: a run here tests the Tamalean
commit that the `tamalean` submodule pins, and bumping the submodule is how a new version enters
the benchmark.

## What is in it

- `models/manifest.toml` lists every model with its source: the repository, the commit, the path,
  the paper it comes from and the license. The models are fetched at those commits
  (`scripts/fetch_models.py`), not copied into this repository.
- `scripts/` runs Tamarin on the models, extracts its proofs, and generates and runs the Lean side.
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

Pushes run only the light checks: the scripts and the manifest. The benchmark itself runs on
demand (`workflow_dispatch`, with a subset of models as input) and on a schedule.
