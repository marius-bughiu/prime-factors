import Mathlib.Algebra.Group.Basic

namespace PrimeFactors

/-- Shifting an exponent and the giant by the same amount preserves their
collision, in particular after reduction to the units modulo a prime. -/
theorem translated_image_collision {G : Type*} [Group G] (α v : G) (i c : ℕ) :
    α^(i+c) = α^c*v ↔ α^i = v := by
  rw [Nat.add_comm i c, pow_add, mul_left_cancel_iff]

/-- Inverting one giant reflects a whole integer exponent, simultaneously at
every sieve prime. The reflected equality is equivalent in both directions. -/
theorem reflected_image_collision {G : Type*} [Group G] (α v : G) {i L : ℕ}
    (c : ℕ) (hi : i ≤ L) : α^(L-i+c) = α^(L+c)*v⁻¹ ↔ α^i = v := by
  rw [eq_mul_inv_iff_mul_eq, show L+c = (L-i+c)+i by omega, pow_add α (L-i+c) i, mul_left_cancel_iff,
    eq_comm]

/-- The shared exponent span and exact decoding of both types of matches. -/
theorem reflected_image_decode {i L c M : ℕ} (hi : i ≤ L) (hc : c < M) :
    i+c < L+M ∧ L-i+c < L+M ∧ (i+c)-c = i ∧ L-((L-i+c)-c) = i := by
  omega

private def reflectedSquare (p x : ℕ) : Bool :=
  (List.range p).any fun z => x%p == z*z%p

private def reflectedUnion (p x : ℕ) : Bool :=
  reflectedSquare p x || reflectedSquare p ((1+p-x%p)%p)

/-- Counts for the two canonical translates Q and 1−Q used at the primes
7, 11 and 19. The final products count whole CRT periods. -/
theorem reflected_image_example :
    let count := fun (p : ℕ) (test : ℕ → ℕ → Bool) => (List.range p).countP (test p)
    (count 7 reflectedSquare,count 7 reflectedUnion) = (4,5) ∧
    (count 11 reflectedSquare,count 11 reflectedUnion) = (6,8) ∧
    (count 19 reflectedSquare,count 19 reflectedUnion) = (10,14) ∧
    7*11*19 = 1463 ∧ 5*8*14 = 560 ∧ 5*8*10 = 400 := by decide +kernel

private def reflectionStates (exclusive common : ℕ) : List (ℕ × ℕ) :=
  [(1,exclusive),(2,exclusive),(3,common)]

private def reflectionAllows (state : ℕ × ℕ) (sign : Bool) : Bool :=
  state.1.testBit (if sign then 1 else 0)

/-- Count the union of four oriented boxes in the example, weighted by the
number of residues with each membership pattern. Bit j of the code chooses
j or its bitwise complement 7−j, for 0 ≤ j < 4. -/
private def reflectionExampleCount (code : ℕ) : ℕ := Id.run do
  let mut total := 0
  for a in reflectionStates 1 3 do
    for b in reflectionStates 2 4 do
      for c in reflectionStates 4 6 do
        let hits := (List.range 4).any fun j =>
          let k := if code.testBit j then 7-j else j
          reflectionAllows a (k.testBit 0) && reflectionAllows b (k.testBit 1) &&
            reflectionAllows c (k.testBit 2)
        if hits then total := total + a.2*b.2*c.2
  return total

/-- Exhaust all sixteen ways to orient the four antipodal pairs of sign
patterns after coordinate compression. Fixing the last bit attains 400. -/
theorem reflected_image_optimum_example :
    reflectionExampleCount 0 = 400 ∧
    ((List.range 16).all fun code => decide (400 ≤ reflectionExampleCount code)) = true := by
  decide +kernel

end PrimeFactors
