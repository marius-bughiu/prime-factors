import PrimeFactors.BatchIntervals
import PrimeFactors.FractionalPrefixWheel
import PrimeFactors.FractionalMatchedDivisors

/-! A limit on excluding every noncentral product by a public wheel.
A step sharing primes with the wheel can drop those primes: they already
miss the central unit and every term in its progression. -/

namespace PrimeFactors.FractionalWheelGapBound

/-- For an arbitrary step, coprimality along the progression equals a
translated ordinary wheel on a divisor of the original wheel. -/
theorem translated {n w : ℕ} (wp : 0<w) (unit : n.Coprime w) (m : ℕ) :
    ∃ d u : ℕ, d∣w ∧ ∀ j : ℕ, (n+m*j).Coprime w ↔ (u+j).Coprime d := by
  obtain ⟨s,d,sp,dp,smooth,step,form⟩ := FractionalPrefixWheel.decompose m wp
  subst w
  have sd : n.Coprime s := (Nat.coprime_mul_iff_right.mp unit).1
  have harmless (j : ℕ) : (n+m*j).Coprime s := by
    by_contra bad
    obtain ⟨p,hp,hv,hs⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
    have pm := smooth p (Nat.mem_primeFactors.mpr ⟨hp,hs,sp.ne'⟩)
    have pn := (Nat.dvd_add_left (dvd_mul_of_dvd_left pm j)).mp hv
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hp,pn,hs⟩) sd
  letI : NeZero d := ⟨dp.ne'⟩
  let v := ZMod.unitOfCoprime m step
  let u : ZMod d := (↑v⁻¹ : ZMod d)*n
  have modEq : n ≡ m*u.val [MOD d] := by
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    rw [Nat.cast_mul,ZMod.natCast_zmod_val]
    change (n : ZMod d) = (↑v : ZMod d)*((↑v⁻¹ : ZMod d)*n)
    rw [←mul_assoc, v.mul_inv, one_mul]
  refine ⟨d,u.val,dvd_mul_left d s,fun j => ?_⟩
  rw [Nat.coprime_mul_iff_right, and_iff_right (harmless j)]
  exact batchIntervals_wheel_translate step modEq j

/-- Any upper bound for gaps between consecutive units of the wheel also
bounds the positive run of excluded product indices, for *every* step. -/
theorem necessary_modulus {n m w g : ℕ} (np : 0<n) (mp : 0<m) (wp : 0<w)
    (unit : n.Coprime w)
    (gap : ∀ u : ℕ, ∃ j : ℕ, 0<j ∧ j≤g ∧ (u+j).Coprime w)
    (isolated : ∀ j : ℕ, FractionalMatchedDivisors.InIndexRange n m (j : ℤ) →
      (n+m*j).Coprime w → j=0) : n ≤ 8*g*m := by
  obtain ⟨d,u,dw,translate⟩ := translated wp unit m
  obtain ⟨j,jp,jg,hit⟩ := gap u
  by_contra! small
  have bound : 8*j*m < n := (Nat.mul_le_mul_right m (Nat.mul_le_mul_left 8 jg)).trans_lt small
  have jb : 8*(j : ℤ)*m < n := by exact_mod_cast bound
  have nonneg : (0 : ℤ) ≤ (j : ℤ)*m := by positivity
  have window : FractionalMatchedDivisors.InIndexRange n m (j : ℤ) := by
    apply (FractionalMatchedDivisors.index_range_iff mp _).2
    unfold FractionalMatchedDivisors.liftProduct
    constructor <;> nlinarith
  exact jp.ne' (isolated j window ((translate j).mpr (hit.of_dvd_right dw)))

/-- The explicit full-width consequence of a 41,000-position gap bound.
For the primorial through 1009, the gap estimate itself is external. -/
theorem full_width_of_gap_41000 {n m w : ℕ} (full : 2^2047≤n) (mp : 0<m) (wp : 0<w)
    (unit : n.Coprime w)
    (gap : ∀ u : ℕ, ∃ j : ℕ, 0<j ∧ j≤41000 ∧ (u+j).Coprime w)
    (isolated : ∀ j : ℕ, FractionalMatchedDivisors.InIndexRange n m (j : ℤ) →
      (n+m*j).Coprime w → j=0) : 2^2028 < m := by
  have bound := necessary_modulus ((Nat.pow_pos (by decide : 0 < 2)).trans_le full) mp wp unit gap isolated
  apply lt_of_not_ge
  intro small
  have impossible := full.trans (bound.trans (Nat.mul_le_mul_left (8*41000) small))
  exact (not_le_of_gt (by decide +kernel : 8*41000*(2:ℕ)^2028 < 2^2047)) impossible

end PrimeFactors.FractionalWheelGapBound
