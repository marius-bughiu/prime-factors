import PrimeFactors.JacobiScalarStride
import PrimeFactors.JacobiPeriodProbe

/-!
# Unit-power tests for a single strided Jacobi moment sequence

For an odd stride whose local images have at least three elements, one
starting phase detects every common period. A nonidentity public unit power
can therefore reject a candidate without evaluating a complete moment.
-/

namespace PrimeFactors.JacobiScalarPeriodProbe

open JacobiScalarStride JacobiMomentPeriod JacobiPeriodProbe

private theorem cancel_stride {a s : ℕ} (positive : 0 < s) (t : ℕ) :
    a ∣ s*t ↔ a / s.gcd a ∣ t := by
  have gp := Nat.gcd_pos_of_pos_right a positive
  have factored : a.gcd s * (a / a.gcd s) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  rw [Nat.gcd_comm s a]
  calc
    a ∣ s*t ↔ a ∣ a.gcd s*t := dvd_gcd_mul_iff_dvd_mul.symm
    _ ↔ a / a.gcd s ∣ t := by
      nth_rw 1 [←factored]
      exact Nat.mul_dvd_mul_iff_left gp

private theorem prime_bound {p s : ℕ} (size : 3 ≤ imageSize p s) : 7 ≤ p := by
  have bound := Nat.div_le_self ((p-1)/2) (s.gcd ((p-1)/2))
  unfold imageSize at size
  omega

/-- Odd fibers and at least three elements in each image make the scalar
sequence starting at degree 2s detect all periods common to every phase. -/
theorem scalar_iff_all_offsets {p q s t : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (pos : 0 < s)
    (oddp : Odd (s.gcd ((p-1)/2))) (oddq : Odd (s.gcd ((q-1)/2)))
    (sizep : 3 ≤ imageSize p s) (sizeq : 3 ≤ imageSize q s) :
    Function.Periodic (sampled (p*q) s) t ↔ AllOffsets (completeEven (p*q)) s t := by
  have hp := prime_bound sizep
  have hq := prime_bound sizeq
  rw [composite_period cop (by omega) (by omega) s t pos oddp oddq sizep sizeq,
    allOffsets_iff, composite_iff cop (by omega) (by omega), Nat.lcm_dvd_iff, Nat.lcm_dvd_iff]
  simp only [localPeriod, if_neg (show p ≠ 5 by omega), if_neg (show q ≠ 5 by omega),
    cancel_stride pos, imageSize]

/-- A shift of one scalar sequence is valid exactly when every unit passes
the public exponent test. The stride itself may be any positive odd number. -/
theorem odd_stride_test {p q s t : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (odd : Odd s)
    (sizep : 3 ≤ imageSize p s) (sizeq : 3 ≤ imageSize q s) :
    Function.Periodic (sampled (p*q) s) t ↔ ∀ x : (ZMod (p*q))ˣ, x^(2*(s*t))=1 :=
  (scalar_iff_all_offsets cop odd.pos (odd.of_dvd_nat (Nat.gcd_dvd_left ..))
    (odd.of_dvd_nat (Nat.gcd_dvd_left ..)) sizep sizeq).trans
      (allOffsets_iff_units cop (prime_bound sizep) (prime_bound sizeq) s t)

private theorem odd_stride {p q : ℕ} [Fact p.Prime] [Fact q.Prime] :
    Odd (ordCompl[2] ((p*q-1)/2)) := by
  have hp := (Fact.out : p.Prime).two_le
  have hq := (Fact.out : q.Prime).two_le
  have bound : 4 ≤ p*q := by nlinarith
  exact Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (by omega))

/-- Once neither public trial candidate divides N, balanced factors imply
the odd predecessor stride has the required image sizes. -/
theorem balanced_test {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : p ≠ 2) (hq : q ≠ 2) (ordered : p < q) (balanced : q < 2*p) :
    let N := p*q
    let s := ordCompl[2] ((N-1)/2)
    ¬ ((8*N+1).sqrt+1)/4 ∣ N → ¬ ((24*N+1).sqrt+1)/6 ∣ N →
      ∀ t, Function.Periodic (sampled N s) t ↔ ∀ x : (ZMod N)ˣ, x^(2*(s*t))=1 := by
  intro N s first second t
  rcases balanced_image_sizes hp hq ordered balanced with trial | trial | ⟨lp,lq⟩
  · exact False.elim (first (trial ▸ (dvd_mul_right p q)))
  · exact False.elim (second (trial ▸ (dvd_mul_right p q)))
  · exact odd_stride_test cop odd_stride lp lq

/-- The least common period at stride H=(N−1)/2 is the least scalar
period at its odd part, divided by the gcd with the removed power of two. -/
theorem residual_from_scalar {p q L : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q) :
    let H := (p*q-1)/2
    let s := ordCompl[2] H
    3 ≤ imageSize p s → 3 ≤ imageSize q s →
      (∀ t, Function.Periodic (sampled (p*q) s) t ↔ L ∣ t) →
      JacobiPeriodCount.residualProduct p q = L / (ordProj[2] H).gcd L := by
  intro H s lp lq known
  let d := ordProj[2] H
  have pos : 0 < d := Nat.ordProj_pos H 2
  have reconstruct : s*d=H := (Nat.mul_comm s d).trans (Nat.ordProj_mul_ordCompl_eq_self H 2)
  have odd : Odd s := odd_stride
  have bridge (t : ℕ) : Function.Periodic (sampled (p*q) s) t ↔
      AllOffsets (completeEven (p*q)) s t := scalar_iff_all_offsets cop odd.pos
    (odd.of_dvd_nat (Nat.gcd_dvd_left ..)) (odd.of_dvd_nat (Nat.gcd_dvd_left ..)) lp lq
  have compare (t : ℕ) : JacobiPeriodCount.residualProduct p q ∣ t ↔ L/d.gcd L ∣ t := by
    rw [←canonical_period cop (prime_bound lp) (prime_bound lq),
      ←cancel_stride pos, ←known, bridge, allOffsets_iff, allOffsets_iff, ←Nat.mul_assoc, reconstruct]
  exact Nat.dvd_antisymm ((compare _).mpr dvd_rfl) ((compare _).mp dvd_rfl)

/-- One failed public base rejects both the proposed scalar shift and every
divisor of that shift. -/
theorem rejects_divisors {p q s d t : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (odd : Odd s) (lp : 3 ≤ imageSize p s) (lq : 3 ≤ imageSize q s)
    (divides : d ∣ t) (base : ℕ) (unit : base.Coprime (p*q))
    (miss : (base : ZMod (p*q))^(2*(s*t)) ≠ 1) :
    ¬Function.Periodic (sampled (p*q) s) d := by
  intro works
  have unitPower := (odd_stride_test cop odd lp lq).mp works (ZMod.unitOfCoprime base unit)
  have power : (base : ZMod (p*q))^(2*(s*d))=1 := by
    simpa only [Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime,Units.val_one]
      using congrArg Units.val unitPower
  obtain ⟨k,rfl⟩ := divides
  apply miss
  rw [show 2*(s*(d*k)) = (2*(s*d))*k by ring,pow_mul,power,one_pow]

private theorem modular_value {n a e r : ℕ} (h : a^e ≡ r [MOD n]) : (a : ZMod n)^e=r := by
  simpa only [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

/-- The same power distinguishes two assertions at 221. The raw even stride
has scalar period six, while for the odd stride base three rejects shift twelve. -/
theorem control221 :
    Function.Periodic (sampled 221 110) 6 ∧ (3 : ZMod 221)^1320=118 ∧
      ¬Function.Periodic (sampled 221 55) 12 := by
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  have evaluated : (3 : ZMod 221)^1320=118 := modular_value (a:=3) (r:=118) (by decide +kernel)
  refine ⟨(JacobiScalarStride.control221 6).2.mpr dvd_rfl,evaluated,?_⟩
  apply rejects_divisors (p:=13) (q:=17) (t:=12) (by decide) (by decide) (by decide)
    (by decide) dvd_rfl 3 (by decide)
  change (3 : ZMod 221)^1320 ≠ 1
  rw [evaluated]; decide

/-- On 3053, base three rejects both proper maximal divisors of fifteen at
the odd stride 763. Shift fifteen itself is separately proved to work. -/
theorem control3053 :
    Function.Periodic (sampled 3053 763) 15 ∧
      ¬Function.Periodic (sampled 3053 763) 3 ∧
      ¬Function.Periodic (sampled 3053 763) 5 := by
  letI : Fact (Nat.Prime 43) := ⟨by decide⟩
  letI : Fact (Nat.Prime 71) := ⟨by decide⟩
  refine ⟨(composite_period (p:=43) (q:=71) (by decide) (by decide) (by decide) 763 15
    (by decide) (by decide) (by decide) (by decide) (by decide)).mpr (by decide),?_,?_⟩
  · apply rejects_divisors (p:=43) (q:=71) (t:=3) (by decide) (by decide) (by decide)
      (by decide) dvd_rfl 3 (by decide)
    have value : (3 : ZMod 3053)^4578=431 := modular_value (a:=3) (r:=431) (by decide +kernel)
    change (3 : ZMod 3053)^4578 ≠ 1
    rw [value]; decide
  · apply rejects_divisors (p:=43) (q:=71) (t:=5) (by decide) (by decide) (by decide)
      (by decide) dvd_rfl 3 (by decide)
    have value : (3 : ZMod 3053)^7630=995 := modular_value (a:=3) (r:=995) (by decide +kernel)
    change (3 : ZMod 3053)^7630 ≠ 1
    rw [value]; decide

end PrimeFactors.JacobiScalarPeriodProbe
