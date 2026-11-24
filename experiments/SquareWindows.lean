import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Prime.Basic

/-! Bounded experiment for the conjectured square detector in (b²/2, b²].
Run with `lake env lean --run experiments/SquareWindows.lean`. -/

private def squareTable (p : ℕ) : Array Bool := Id.run do
  let mut table := Array.replicate p false
  for r in [:p] do
    table := table.set! (r * r % p) true
  return table

private def checkSquareWindow (b : ℕ) : IO Unit := do
  let upper := b * b
  let primes := (List.range (upper + 1)).filter fun p => decide (upper / 2 < p ∧ p.Prime)
  let tables := primes.map fun p => (p, squareTable p)
  let mut survivors := (Array.range (2 ^ b)).filter fun d => d.sqrt ^ 2 != d
  let mut chosen : Array ℕ := #[]
  for _ in primes do
    if survivors.isEmpty then break
    let mut bestCount := survivors.size
    let mut best := none
    for (p, table) in tables do
      let count := survivors.foldl (fun acc d => if table[d % p]! then acc + 1 else acc) 0
      if count < bestCount then
        bestCount := count
        best := some (p, table)
    match best with
    | none => break
    | some (p, table) =>
      chosen := chosen.push p
      survivors := survivors.filter fun d => table[d % p]!
  IO.println s!"b={b}  primes={chosen}  remaining={survivors.size}  first={survivors[0]?}"

def main : IO Unit := do
  for b in [4:21] do checkSquareWindow b
