import PrimeFactors
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked := 0
  let mut state : CollectAxioms.State := {}
  for (name, _) in env.constants.toList do
    if (`PrimeFactors).isPrefixOf name then
      -- All roots come from this same immutable environment. Share Lean's
      -- visited set so common Mathlib dependencies are traversed only once.
      let (_, next) := ((CollectAxioms.collect name).run env).run state
      state := next
      for dep in state.axioms do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains dep do
          throwError "{name} depends on unapproved axiom {dep}"
      checked := checked + 1
  if checked == 0 then throwError "No PrimeFactors declarations were audited"
  logInfo m!"Audited {checked} project declarations"
