import Lean.Data.Json
import PrimeFactors.GroupedNormFactors

/-! Run `lake env lean --run experiments/GroupedNormProbe.lean N` on a positive decimal integer. -/

/-- Keep the strict result and the public window calculation inside the timed IO call. -/
@[noinline] private def timedWork (n : Nat) : BaseIO (Option (Nat × Nat) × Nat) := do
  let t := n.sqrt
  let h := n-t^2
  let eligible := (t-1)/h
  return (PrimeFactors.GroupedNormFactors.topProbe n, eligible)

def main (args : List String) : IO Unit := do
  let [input] := args | throw <| IO.userError "expected one positive decimal integer N"
  let some n := input.toNat? | throw <| IO.userError "expected a positive decimal integer N"
  if n == 0 then throw <| IO.userError "expected a positive decimal integer N"
  let start ← IO.monoNanosNow
  let (pair, eligible) ← timedWork n
  let stop ← IO.monoNanosNow
  IO.println <| (Lean.Json.mkObj [
    ("pair", Lean.toJson (pair.map fun (p,q) => #[toString p, toString q])),
    ("eligible_multipliers", Lean.toJson (toString eligible)),
    ("square_tests", Lean.toJson (if eligible == 0 then 0 else 1 : Nat)),
    ("search_ns", Lean.toJson (stop-start))]).compress
