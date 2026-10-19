import Tamalean.Core
import Tamalean.Theories
import Tamalean.Engine.Tactics.RefutationInteractive

/-!
# The benchmark's harness

Two commands for the modules `scripts/gen_lean.py` generates, one per model.  The harness
imports Tamalean's core, its equational theories (Diffie–Hellman, xor, multiset, …), which the
reader's models of those builtins refer to, and its tactics.

* `bench_model "path.spthy"` reads the model with Tamalean's reader (`tamarin_theory_file`);
* `bench_certify "lemma" Theory.Lemmas.lemma` states the lemma and proves it with `certify`
  (`example : Theory.Lemmas.lemma := by certify`).

Each writes one line `BENCH <kind> <json>` as soon as it is done (and one line `BENCH start
<json>` before it starts), with the outcome, the first error and the time in milliseconds, to
the file `BENCH_EVENTS` names; `scripts/run_lean.py` reads them as they come, and stops a lemma
that runs past its time limit.  The errors themselves are reported as usual.

The option `bench.only` (`lake lean Bench/….lean -- -Dbench.only=a,b`) restricts
`bench_certify` to the lemmas it lists, so that the runner can resume a model after a lemma it
stopped.
-/

namespace Bench

open Lean Elab Command

register_option bench.only : String := {
  defValue := ""
  descr := "a comma-separated list of the lemmas `bench_certify` runs (every lemma when empty)"
}

/-- One machine-readable line, appended at once to the file the environment variable
`BENCH_EVENTS` names (Lake passes a module's output on only when the module is done, so the
runner reads this file instead), and printed on standard output. -/
def emit (kind : String) (j : Json) : IO Unit := do
  let line := s!"BENCH {kind} {j.compress}"
  if let some path ← IO.getEnv "BENCH_EVENTS" then
    let h ← IO.FS.Handle.mk path .append
    h.putStrLn line
    h.flush
  let out ← IO.getStdout
  out.putStrLn line
  out.flush

/-- Elaborate `cmd`, and return the time it took and the texts of the errors and of the other
messages it logged. -/
def timedElab (cmd : Syntax) : CommandElabM (Nat × List String × List String) := do
  let n0 := (← get).messages.toList.length
  let t0 ← IO.monoMsNow
  try elabCommand cmd catch ex => logException ex
  let t1 ← IO.monoMsNow
  let msgs := (← get).messages.toList.drop n0
  let errs ← (msgs.filter (·.severity == .error)).mapM (·.toString)
  let others ← (msgs.filter (·.severity != .error)).mapM (·.toString)
  return (t1 - t0, errs, others)

/-- At most `n` characters of `s`. -/
def clip (s : String) (n : Nat := 4000) : String :=
  if s.length ≤ n then s else (s.take n).toString ++ " …"

syntax (name := benchModel) "bench_model " str : command

elab_rules : command
  | `(bench_model $p:str) => do
      emit "reading" <| Json.mkObj [("path", toJson p.getString)]
      let (ms, errs, _) ← timedElab (← `(command| tamarin_theory_file $p))
      emit "reader" <| Json.mkObj <|
        [("ok", toJson errs.isEmpty), ("ms", toJson ms)] ++
        (match errs with | e :: _ => [("error", toJson (clip e))] | [] => [])

syntax (name := benchCertify) "bench_certify " str ident : command

elab_rules : command
  | `(bench_certify $n:str $l:ident) => do
      let name := n.getString
      let only := bench.only.get (← getOptions)
      unless only.isEmpty || (only.splitOn ",").contains name do return
      -- the reader generates the statement; without it there is nothing to prove
      let exists_ ← try
          discard <| liftCoreM <| realizeGlobalConstNoOverload l
          pure true
        catch _ => pure false
      unless exists_ do
        emit "lemma" <| Json.mkObj [("name", toJson name), ("ok", toJson false),
          ("ms", toJson (0 : Nat)), ("missing", toJson true),
          ("error", toJson s!"no statement {l.getId}: the reader did not generate it")]
        return
      emit "start" <| Json.mkObj [("name", toJson name)]
      let (ms, errs, infos) ← timedElab (← `(command| example : $l := by certify))
      emit "lemma" <| Json.mkObj <|
        [("name", toJson name), ("ok", toJson errs.isEmpty), ("ms", toJson ms)] ++
        (match errs with | e :: _ => [("error", toJson (clip e))] | [] => []) ++
        (if infos.isEmpty then [] else [("info", toJson (infos.map (clip · 1000)))])

end Bench
