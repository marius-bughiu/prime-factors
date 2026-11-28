import PrimeFactors.FractionalMatchedDivisors
import PrimeFactors.FractionalWheelNeighbours
import PrimeFactors.FractionalWheelTranscript

/-! Exact modulus cutoff for keeping every surviving nonzero index outside
both ends of the balanced product interval. -/

namespace PrimeFactors.FractionalWheelCutoff

open FractionalMatchedDivisors

private theorem endpoint {n m d a : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ((n : ℤ)-1) / ((d : ℤ)*m) < a ↔ n ≤ d*a*m := by
  rw [Int.ediv_lt_iff_lt_mul (by positivity)]
  have eqn : (a : ℤ)*(d*m) = ((d*a*m : ℕ) : ℤ) := by push_cast; ring
  rw [eqn]
  omega

/-- The index window excludes every surviving nonzero index precisely when
it ends strictly before the first survivor on each side. No condition on the
number of representative pairs at either endpoint is required. -/
theorem cutoff {n m a b : ℕ} (hn : 0 < n) (hm : 0 < m) (ha : 0 < a) (hb : 0 < b)
    (keep : ℤ → Prop) (left : keep (-(a : ℤ))) (right : keep b)
    (interior : ∀ j : ℤ, -(a : ℤ) < j → j < b → keep j → j = 0) :
    (∀ j : ℤ, InIndexRange n m j → keep j → j = 0) ↔ n ≤ 9*a*m ∧ n ≤ 8*b*m := by
  rw [← endpoint (a := a) hm (by decide : 0 < 9), ← endpoint (a := b) hm (by decide : 0 < 8)]
  change _ ↔ ((n : ℤ)-1)/(9*m) < a ∧ ((n : ℤ)-1)/(8*m) < b
  have num : 0 ≤ (n : ℤ)-1 := by omega
  have lpos : 0 ≤ ((n : ℤ)-1)/(9*m) := Int.ediv_nonneg num (by positivity)
  have rpos : 0 ≤ ((n : ℤ)-1)/(8*m) := Int.ediv_nonneg num (by positivity)
  constructor
  · intro only_zero
    constructor
    · by_contra! reached
      have loc : InIndexRange n m (-(a : ℤ)) := ⟨by omega, by omega⟩
      have eqn := only_zero _ loc left
      omega
    · by_contra! reached
      have loc : InIndexRange n m (b : ℤ) := ⟨by omega, by omega⟩
      have eqn := only_zero _ loc right
      omega
  · rintro ⟨lo,hi⟩ j ⟨jl,jh⟩ keep_j
    exact interior j (by omega) (by omega) keep_j

/-- For the original wheel the right endpoint reaches 1008 first. -/
theorem original {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (∀ j : ℤ, InIndexRange n m j → FractionalWheelNeighbours.indexGcd j = 1 → j = 0) ↔
      n ≤ 8064*m := by
  have first := FractionalWheelNeighbours.neighbours
  have interior (j : ℤ) (lo : -1010 < j) (hi : j < 1008)
      (unit : FractionalWheelNeighbours.indexGcd j = 1) : j = 0 := by
    by_contra off
    exact FractionalWheelNeighbours.interior lo hi off unit
  rw [cutoff (a := 1010) (b := 1008) hn hm (by decide) (by decide)
    (fun j => FractionalWheelNeighbours.indexGcd j = 1) first.1 first.2.2 interior]
  change (n ≤ 9090*m ∧ n ≤ 8064*m) ↔ n ≤ 8064*m
  exact ⟨And.right, fun h => ⟨h.trans (Nat.mul_le_mul_right m (by decide : 8064 ≤ 9090)), h⟩⟩

/-- Reversing the index leaves the origin fixed and exchanges the nearest
surviving indices. The positive endpoint then reaches 1010 first. -/
theorem reflected {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (∀ j : ℤ, InIndexRange n m j → FractionalWheelNeighbours.indexGcd (-j) = 1 → j = 0) ↔
      n ≤ 8080*m := by
  have first := FractionalWheelNeighbours.neighbours
  have interior (j : ℤ) (lo : -1008 < j) (hi : j < 1010)
      (unit : FractionalWheelNeighbours.indexGcd (-j) = 1) : j = 0 := by
    by_contra off
    have below : -j < 1008 := by simpa only [neg_neg] using neg_lt_neg lo
    exact FractionalWheelNeighbours.interior (neg_lt_neg hi) below (neg_ne_zero.mpr off) unit
  rw [cutoff (a := 1008) (b := 1010) hn hm (by decide) (by decide)
    (fun j => FractionalWheelNeighbours.indexGcd (-j) = 1) (by simpa only [neg_neg] using first.2.2) first.1 interior]
  change (n ≤ 9072*m ∧ n ≤ 8080*m) ↔ n ≤ 8080*m
  exact ⟨And.right, fun h => ⟨h.trans (Nat.mul_le_mul_right m (by decide : 8080 ≤ 9072)), h⟩⟩

/-- For a product coprime to the wheel and a step satisfying the two CRT
conditions, the gcd on the actual lifted products has the original cutoff. -/
theorem selected_lifts {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (unit : n.Coprime (primorial 1000 * 1009))
    (wheel : m ≡ n [MOD primorial 1000]) (extra : 2*m ≡ n [MOD 1009]) :
    (∀ j : ℤ, InIndexRange n m j →
      (liftProduct n m j).gcd (primorial 1000 * 1009 : ℕ) = 1 → j = 0) ↔ n ≤ 8064*m := by
  have readout (j : ℤ) : (liftProduct n m j).gcd (primorial 1000 * 1009 : ℕ) =
      FractionalWheelNeighbours.indexGcd j :=
    FractionalWheelTranscript.exact_gcd (P := primorial 1000) (r := 1009)
      FractionalSelectedProgression.aux_coprime unit wheel extra j
  simpa only [readout] using original hn hm

/-- A supplied modulus just below the H=3 cutoff admits index +4. Its
product is prime, so this surviving index cannot supply a nontrivial pair. -/
theorem prime_lift_control : (4453 : ℕ) = 61*73 ∧ 139 ≡ 4453 [MOD 6] ∧
    2*139 ≡ 4453 [MOD 5] ∧ InIndexRange 4453 139 4 ∧
    liftProduct 4453 139 4 = 5009 ∧ Nat.Coprime 5009 30 ∧ Nat.Prime 5009 ∧
    ∀ x y : ℕ, 1 < x → 1 < y → x*y ≠ 5009 := by
  have prime : Nat.Prime 5009 := by norm_num
  exact ⟨by decide, by decide, by decide, ⟨by decide, by decide⟩, by decide, by decide,
    prime, fun x y hx hy eqn => Nat.not_prime_mul' eqn (by omega) (by omega) prime⟩

end PrimeFactors.FractionalWheelCutoff
