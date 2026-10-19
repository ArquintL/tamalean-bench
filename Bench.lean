import Bench.Harness

/-!
# The benchmark's models

One module per model in the Lean side's scope, `Bench/<id>.lean`, generated from
`models/manifest.toml` by `scripts/gen_lean.py`: the model read by Tamalean's `.spthy` reader
and one `certify` per lemma.  This file imports only the harness (`Bench/Harness.lean`), so that
`lake build` builds what the generated modules need and never fails because one of them does;
`scripts/run_lean.py` runs each generated module on its own.
-/
