import PrimeFactors
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked := 0
  for (name, _) in env.constants.toList do
    if (`PrimeFactors).isPrefixOf name then
      let assumptions ← collectAxioms name
      for dep in assumptions do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains dep do
          throwError "{name} depends on unapproved axiom {dep}"
      checked := checked + 1
  if checked == 0 then throwError "No PrimeFactors declarations were audited"
  logInfo m!"Audited {checked} project declarations"
