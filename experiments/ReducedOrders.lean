import Lean.Data.Json
import Std.Data.TreeMap
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Dist

/-! Input-only geometric period search and certificate replay.
Run from the repository root with `lake env lean --run experiments/ReducedOrders.lean`.
A single search emits JSON with `search N BASE STRIDE` after the file name. -/

namespace ReducedOrders

private def powerMod (a e n : ℕ) : ℕ := Id.run do
  let mut x := a % n
  let mut k := e
  let mut out := 1
  for _ in [:e.log2+1] do
    if k % 2 == 1 then out := out*x % n
    x := x*x % n
    k := k / 2
  return out

/-- Divide-and-conquer packing keeps the sum of intermediate bit lengths linear
per level. Digits are coefficients in a power-of-two base. -/
private partial def pack (xs : Array ℕ) (start len bits : ℕ) : ℕ :=
  if len = 0 then 0 else if len = 1 then xs[start]! else
    let half := len / 2
    pack xs start half bits ||| ((pack xs (start+half) (len-half) bits) <<< (bits*half))

private partial def unpack (x len bits n : ℕ) : Array ℕ :=
  if len = 0 then #[] else if len = 1 then #[x % n] else
    let half := len / 2
    let shift := bits*half
    unpack (x &&& ((1 <<< shift)-1)) half bits n ++ unpack (x >>> shift) (len-half) bits n

private def multiply (n : ℕ) (a b : Array ℕ) : Array ℕ :=
  let bits := 3 + 2*n.log2 + (min a.size b.size).log2
  let packed := pack a 0 a.size bits * pack b 0 b.size bits
  unpack packed (a.size+b.size-1) bits n

private partial def rootPolynomial (n : ℕ) (xs : Array ℕ) (start len : ℕ) : Array ℕ :=
  if len = 0 then #[1] else if len = 1 then #[(n-xs[start]!) % n, 1] else
    let half := len / 2
    multiply n (rootPolynomial n xs start half) (rootPolynomial n xs (start+half) (len-half))

private def powers (n v count : ℕ) : Array ℕ := Id.run do
  let mut result := #[]
  let mut x := 1
  for _ in [:count] do
    result := result.push x
    x := x*v % n
  return result

/-- Entry i is v^(choose(i,2)+choose(d,2)) * f(v^i), where d = degree f.
Since v is a unit, the multiplier preserves gcds with n. -/
private def geometricValues (n v count : ℕ) (f : Array ℕ) : Array ℕ := Id.run do
  let d := f.size - 1
  let geometric := powers n v (d + count)
  let mut chirps := #[]
  let mut c := 1
  for k in [:d+count] do
    chirps := chirps.push c
    c := c*geometric[k]! % n
  let mut coefficients := #[]
  let mut weight := 1
  for j in [:d+1] do
    let k := d-j
    coefficients := coefficients.push (f[k]! * weight % n)
    if 0 < k then weight := weight * geometric[k-1]! % n
  return (multiply n coefficients chirps).extract d (d+count)

private def proper (n x : ℕ) : Option ℕ :=
  let g := n.gcd x
  if 1 < g && g < n then some g else none

private def splitMultiple (n v k : ℕ) : Option ℕ := Id.run do
  for z in [1:k.sqrt+1] do
    if k%z == 0 then
      for e in #[z, k/z] do
        if let some p := proper n (powerMod v e n - 1) then return some p
  return none

structure SearchResult where
  factor : Option ℕ := none
  outcome : String
  entriesPerTable : ℕ := 0
  giantsProbed : ℕ := 0
  batchGcds : ℕ := 0

/-- The search takes only the product, deterministic trial base, and table budget.
Both full tables are allocated before the first comparison. Each batch gcd is
one inspected polynomial value, including the last row when it yields a split. -/
def search (n base m : ℕ) : SearchResult := Id.run do
  if n < 2 || m == 0 then return {outcome := "empty budget or invalid product"}
  if let some factor := proper n base then return {factor := some factor, outcome := "base gcd"}
  if base.gcd n != 1 then return {outcome := "base divisible by product"}
  let v := powerMod base (n-1) n
  if v == 1 then return {outcome := "identity base"}
  let babies := powers n v m
  let stride := powerMod v m n
  let giants := (powers n stride (m+1)).extract 1 (m+1)
  let mut indices : Std.TreeMap ℕ ℕ := {}
  for i in [:m] do indices := indices.insert babies[i]! i
  for j in [:m] do
    if let some i := indices[giants[j]!]? then
      let k := m*(j+1)-i
      return {factor := splitMultiple n v k, outcome := s!"whole collision at exponent {k}",
              entriesPerTable := m, giantsProbed := j+1}
  let values := geometricValues n v m (rootPolynomial n giants 0 m)
  for i in [:m] do
    let g := n.gcd values[i]!
    if g != 1 then
      if g != n then
        return {factor := some g, outcome := s!"batched evaluation at baby {i}",
                entriesPerTable := m, giantsProbed := m, batchGcds := i+1}
      for giant in giants do
        if let some factor := proper n (Nat.dist babies[i]! giant) then
          return {factor := some factor, outcome := s!"refined batched evaluation at baby {i}",
                  entriesPerTable := m, giantsProbed := m, batchGcds := i+1}
  return {outcome := "table exhausted", entriesPerTable := m, giantsProbed := m, batchGcds := m}

private def validateBatch : IO Unit := do
  for n in #[15, 35, 77, 143, 323] do
    for v in #[2, 4, 8] do
      for m in [1:10] do
        let babies := powers n v m
        let giants := (powers n (powerMod v m n) (m+1)).extract 1 (m+1)
        let values := geometricValues n v m (rootPolynomial n giants 0 m)
        for i in [:m] do
          let value := giants.foldl (fun acc y => acc*((n+babies[i]!-y)%n) % n) 1
          let shift := (i*(i-1) + m*(m-1))/2
          unless values[i]! == powerMod v shift n * value % n do
            throw <| IO.userError s!"geometric interpolation failed at {(n,v,m,i)}"
  unless (search 77 2 1).outcome == "table exhausted" && (search 77 1 6).outcome == "identity base" do
    throw <| IO.userError "expected bounded and identity-base searches to remain unresolved"

structure Fixture where
  id : String
  n : String
  base : ℕ
  stride : ℕ
  factors : Array String
  deriving Lean.FromJson

private def replay (case : Fixture) : IO Unit := do
  let some n := case.n.toNat? | throw <| IO.userError "invalid decimal input"
  let result := search n case.base case.stride
  let some factor := result.factor | do
    unless case.factors.isEmpty do throw <| IO.userError s!"{case.id} unexpectedly unresolved"
    IO.println s!"{case.id}: {result.outcome}; remaining {n}; {result.entriesPerTable} entries per table"
    return
  let factors := #[min factor (n/factor), max factor (n/factor)]
  unless factors.map toString == case.factors do throw <| IO.userError "unexpected factors"
  let output := "build/" ++ case.id ++ "-certificate.lean"
  let proof ← IO.Process.output {cmd := "python3", args := #["scripts/factor.py", case.n,
    "--max-steps", "0", "--factor-hint", toString factor, "--verify", "--lean", output]}
  unless proof.exitCode == 0 do throw <| IO.userError (proof.stderr ++ proof.stdout)
  IO.println s!"{case.id}: {result.outcome}; {result.entriesPerTable} entries per table; certificate {output}"

private def replayFixtures : IO Unit := do
  validateBatch
  let contents ← IO.FS.readFile "benchmarks/reduced-orders.json"
  let raw ← IO.ofExcept (Lean.Json.parse contents)
  let cases ← IO.ofExcept (Lean.fromJson? (α := Array Fixture) raw)
  for case in cases do replay case

def run (args : List String) : IO Unit := do
  match args with
  | [] => replayFixtures
  | ["search", input, baseArg, strideArg] =>
    let some n := input.toNat? | throw <| IO.userError "invalid decimal product"
    let some base := baseArg.toNat? | throw <| IO.userError "invalid base"
    let some stride := strideArg.toNat? | throw <| IO.userError "invalid stride"
    let before ← IO.monoNanosNow
    let result := search n base stride
    let after ← IO.monoNanosNow
    IO.println (Lean.Json.mkObj [
      ("factor", Lean.toJson (result.factor.map toString)),
      ("outcome", Lean.toJson result.outcome),
      ("entries_per_table", Lean.toJson result.entriesPerTable),
      ("giants_probed", Lean.toJson result.giantsProbed),
      ("batch_gcds", Lean.toJson result.batchGcds),
      ("search_nanoseconds", Lean.toJson (after-before))]).compress
  | _ => throw <| IO.userError "expected search N BASE STRIDE, or no arguments to replay the fixtures"

end ReducedOrders

def main (args : List String) : IO Unit := ReducedOrders.run args
