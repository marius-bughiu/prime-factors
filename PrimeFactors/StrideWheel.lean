import PrimeFactors.PrimePower
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime

namespace PrimeFactors

/-- The divided discriminant along one root class has integer coefficients. -/
def strideQuotient {R : Type*} [CommRing R] (m h a j : R) : R :=
  a + 2 * h * j + m^2 * j^2

theorem strideQuotient_identity {R : Type*} [CommRing R] {N m h a : R}
    (root : h^2 = N + m^2 * a) (j : R) :
    (h + m^2 * j)^2 - N = m^2 * strideQuotient m h a j := by
  unfold strideQuotient
  linear_combination root

/-- At the genuine midpoint this polynomial equals the square of the
remaining half-gap after its stride divisor is removed. -/
theorem strideQuotient_gap_square {N m h a j c : ℤ} (root : h^2 = N + m^2*a)
    (nonzero : m ≠ 0) (hit : (h+m^2*j)^2 = N+(m*c)^2) :
    strideQuotient m h a j = c^2 := by
  apply mul_left_cancel₀ (pow_ne_zero 2 nonzero)
  rw [← strideQuotient_identity root, hit]; ring

/-- One more root-lift digit is exactly the zero of the divided discriminant
modulo the new radix. This applies even when that radix divides the stride. -/
theorem strideQuotient_zero_lift {N m h a : ℤ} (root : h^2 = N + m^2*a)
    (nonzero : m ≠ 0) (p j : ℤ) :
    N ≡ (h+m^2*j)^2 [ZMOD m^2*p] ↔ strideQuotient m h a j ≡ 0 [ZMOD p] := by
  rw [Int.modEq_iff_dvd, Int.modEq_zero_iff_dvd, strideQuotient_identity root]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, mul_left_cancel₀ (pow_ne_zero 2 nonzero) (by simpa [mul_assoc] using hk)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk, mul_assoc]⟩

/-- Every midpoint in a finer five-root branch passes the inclusive quotient
filter at the lower level with residue zero, before its final square test. -/
theorem strideWheel_coarser_zero {N m h a j H : ℤ} (baseRoot : h^2 = N+m^2*a)
    (nonzero : m ≠ 0) (fineRoot : N ≡ H^2 [ZMOD (5*m)^2])
    (inClass : h+m^2*j ≡ H [ZMOD (5*m)^2]) :
    strideQuotient m h a j ≡ 0 [ZMOD 5] := by
  apply (strideQuotient_zero_lift baseRoot nonzero 5 j).mp
  exact (fineRoot.trans (inClass.pow 2).symm).of_dvd ⟨5, by ring⟩

/-- Rank is counted by earlier midpoints in the same root class. Refining
the class and its acceptance rule can only decrease this rank. -/
theorem strideWheel_rank_le (m M r H : ℕ) (refines : m ∣ M) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (passes : ∀ t, t ≡ H [MOD M^2] → Q t → P t) :
    ((Finset.Ico r H).filter (fun t => t ≡ H [MOD M^2] ∧ Q t)).card ≤
      ((Finset.Ico r H).filter (fun t => t ≡ H [MOD m^2] ∧ P t)).card := by
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, ht.2.1.of_dvd (pow_dvd_pow_of_dvd refines 2), passes t ht.2.1 ht.2.2⟩

/-- At a prime dividing the stride the once-lifted root selects the origin
of the divided discriminant's linear progression. -/
theorem strideQuotient_center {R : Type*} [CommRing R] {m h a z : R}
    (ramified : m = 0) (lifted : strideQuotient m h a z = 0) (j : R) :
    strideQuotient m h a j = 2 * h * (j - z) := by
  subst m
  simp [strideQuotient] at lifted ⊢
  linear_combination lifted

private theorem five_unit_squares (x : ZMod 5) :
    (x ≠ 0 ∧ IsSquare x) ↔ x = 1 ∨ x = -1 := by
  exact (by decide : ∀ t : ZMod 5, (t ≠ 0 ∧ ∃ c : ZMod 5, t = c*c) ↔ t=1 ∨ t= -1) x

/-- Exactly two offset digits survive at the exact 5-adic valuation of the gap.
Their center comes from the Hensel digit needed to build the next stride level. -/
theorem strideQuotient_five_offsets {m h a z i : ZMod 5} (ramified : m = 0)
    (lifted : strideQuotient m h a z = 0) (inverse : 2*h*i = 1) (j : ZMod 5) :
    (strideQuotient m h a j ≠ 0 ∧ IsSquare (strideQuotient m h a j)) ↔
      j = z + i ∨ j = z - i := by
  rw [five_unit_squares, strideQuotient_center ramified lifted]
  have recov : j = z + i*(2*h*(j-z)) := by
    calc
      j = z + (2*h*i)*(j-z) := by rw [inverse]; ring
      _ = _ := by ring
  constructor
  · rintro (pos | neg)
    · exact Or.inl (by simpa [pos] using recov)
    · rw [neg] at recov
      exact Or.inr (by simpa [sub_eq_add_neg] using recov)
  · rintro (rfl | rfl)
    · exact Or.inl (by linear_combination inverse)
    · exact Or.inr (by linear_combination -inverse)

/-- At a truncated terminal level the zero digit must also be accepted,
since the true exact valuation may lie beyond the allocation. -/
theorem strideQuotient_terminal_five {m h a z i : ZMod 5} (ramified : m = 0)
    (lifted : strideQuotient m h a z = 0) (inverse : 2*h*i = 1) (j : ZMod 5) :
    IsSquare (strideQuotient m h a j) ↔ j = z ∨ j = z+i ∨ j = z-i := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have exactDigits := strideQuotient_five_offsets ramified lifted inverse j
  have nonzero : 2*h ≠ 0 := by intro zero; rw [zero, zero_mul] at inverse; exact zero_ne_one inverse
  constructor
  · intro hs
    by_cases hz : strideQuotient m h a j = 0
    · rw [strideQuotient_center ramified lifted] at hz
      exact Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left nonzero))
    · exact Or.inr (exactDigits.mp ⟨hz,hs⟩)
  · rintro (rfl | hd)
    · exact ⟨0, by simp [lifted]⟩
    · exact (exactDigits.mpr hd).2

/-- For an external modulus, division by a unit square preserves exactly the
ordinary Fermat square filter. -/
theorem strideQuotient_external {R : Type*} [CommRing R] {N m h a : R}
    (root : h^2 = N + m^2*a) (unit : IsUnit m) (j : R) :
    IsSquare ((h+m^2*j)^2-N) ↔ IsSquare (strideQuotient m h a j) := by
  rw [strideQuotient_identity root]
  obtain ⟨u, rfl⟩ := unit
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨(↑u⁻¹ : R)*c, ?_⟩
    calc
      _ = ((↑u⁻¹ : R)*(↑u : R))^2 * strideQuotient (↑u : R) h a j := by simp
      _ = (↑u⁻¹ : R)^2 * ((↑u : R)^2 * strideQuotient (↑u : R) h a j) := by ring
      _ = _ := by rw [hc]; ring
  · rintro ⟨c, hc⟩
    exact ⟨(↑u : R)*c, by rw [hc]; ring⟩

/-- At an exact (unit) gap cofactor, raising the matched prime's precision
cannot remove an offset that passes its first digit. -/
theorem strideQuotient_unit_saturation {p : ℕ} [Fact p.Prime] (odd : p ≠ 2)
    (m h a j : ℤ) (unit : ((strideQuotient m h a j : ℤ) : ZMod p) ≠ 0) (k : ℕ) :
    IsSquare ((strideQuotient m h a j : ℤ) : ZMod (p^(k+1))) ↔
      IsSquare ((strideQuotient m h a j : ℤ) : ZMod p) := by
  exact isSquare_primePow_iff_of_unit odd _ unit k

/-- The six square residues modulo 24, expressed as a bounded Boolean test. -/
noncomputable def wheelSquare24 (v : ℕ) : Bool := [0, 1, 4, 9, 12, 16].contains (v % 24)

theorem wheelSquare24_iff (n t : Fin 24) :
    wheelSquare24 (t.val^2 + 24 - n.val) = true ↔
      ∃ d : Fin 24, t.val^2 % 24 = (n.val + d.val^2) % 24 := by
  exact (by decide +kernel : ∀ n t : Fin 24,
    wheelSquare24 (t.val^2 + 24 - n.val) = true ↔
      ∃ d : Fin 24, t.val^2 % 24 = (n.val + d.val^2) % 24) n t

/-- One canonical period. The three patterns are {0}, {±1}, and {±2}. -/
noncomputable def strideWheelPeriod (n : Fin 24) (s : Fin 3) : List ℕ :=
  (List.range 120).filter fun t =>
    wheelSquare24 (t^2 + 24 - n.val) && (t%5 == s.val || t%5 == (5-s.val)%5)

/-- A single shift aligns the external midpoint phase and the internal
Hensel center. The rotation formula works for every pair of residues. -/
theorem strideWheel_phase_crt (b z : ℕ) :
    let phase := b + 24*((b+z)%5)
    phase % 24 = b % 24 ∧ (phase+z)%5 = 0 := by
  dsimp
  omega

/-- The external 8 and 3 filters and the internal 5 filter have the displayed
counts in a full period. This gives the exact budget for every product phase. -/
theorem strideWheelPeriod_length (n : Fin 24) (s : Fin 3) (unit : n.val.Coprime 6) :
    (strideWheelPeriod n s).length =
      (if n.val%4 = 1 then 4 else 2) * (if n.val%3 = 1 then 2 else 1) *
      (if s.val=0 then 1 else 2) := by
  exact (by decide +kernel : ∀ n : Fin 24, ∀ s : Fin 3, n.val.Coprime 6 →
    (strideWheelPeriod n s).length =
      (if n.val%4 = 1 then 4 else 2) * (if n.val%3 = 1 then 2 else 1) *
      (if s.val=0 then 1 else 2)) n s unit

/-- A coprime target leaves between two and sixteen offsets per 120-position
period across all three patterns, including the initial valuation zero. -/
theorem strideWheelPeriod_bounds (n : Fin 24) (s : Fin 3) (unit : n.val.Coprime 6) :
    2 ≤ (strideWheelPeriod n s).length ∧ (strideWheelPeriod n s).length ≤ 16 := by
  exact (by decide +kernel : ∀ n : Fin 24, ∀ s : Fin 3, n.val.Coprime 6 →
    2 ≤ (strideWheelPeriod n s).length ∧ (strideWheelPeriod n s).length ≤ 16) n s unit

/-- In this branch the first seven indices are all excluded; the eighth
gives both certified prime factors. -/
theorem strideWheel_27130781 :
    (List.range 8).filter (fun j => (strideWheelPeriod 5 2).contains ((80+j)%120)) = [7] ∧
    (5216+25*7)^2 = 27130781+1390^2 ∧
    27130781 = 4001*6781 ∧ Nat.Prime 4001 ∧ Nat.Prime 6781 := by
  refine ⟨by decide +kernel, by decide, by decide, ?_, ?_⟩ <;> norm_num

end PrimeFactors
