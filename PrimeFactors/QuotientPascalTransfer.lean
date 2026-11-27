import PrimeFactors.QuotientPascalMasks

/-! A binomial coefficient at an addressed row preserves the full gcd of
a finite arithmetic progression with the modulus, including prime powers. -/
namespace PrimeFactors.QuotientPascalTransfer
open Finset QuotientPascalMasks

/-- This congruence holds even when k>m. In that case the progression
contains its zero-residue term at index m and the binomial vanishes. -/
theorem progression_mod {n m d c : ℕ} (address : n∣c+d*m) (k : ℕ) :
    (progression c d k : ZMod n) =
      (-(d:ZMod n))^k*(k.factorial:ZMod n)*(m.choose k:ZMod n) := by
  have row : (c:ZMod n)+(d:ZMod n)*(m:ZMod n)=0 := by
    exact_mod_cast (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr address
  have identity (i : ℕ) (hi : i≤m) : (progression c d i : ZMod n) =
      (-(d:ZMod n))^i*(m.descFactorial i:ZMod n) := by
    induction i with
    | zero => simp [progression]
    | succ i ih =>
      have im : i≤m := by omega
      have rec : progression c d (i+1) = progression c d i*(c+d*i) := prod_range_succ _ _
      rw [rec,Nat.cast_mul,ih im,Nat.cast_add,Nat.cast_mul,Nat.descFactorial_succ,
        Nat.cast_mul,Nat.cast_sub im,pow_succ]
      have term : (c:ZMod n)+d*i = (-d:ZMod n)*(m-i) := by linear_combination row
      rw [term]
      ring
  by_cases km : k≤m
  · rw [identity k km,Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul,mul_assoc]
  · have mk : m<k := by omega
    have divides : n∣progression c d k := address.trans (Finset.dvd_prod_of_mem
      (fun i => c+d*i) (mem_range.mpr mk))
    rw [(ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr divides,Nat.choose_eq_zero_of_lt mk]
    simp

/-- Every divisor of n tests identically on the binomial column and the
progression, irrespective of its factorization. -/
theorem divisor_transfer {n e m d c k : ℕ} (de : e∣n)
    (unit : n.Coprime (d*k.factorial)) (address : n∣c+d*m) :
    e∣m.choose k ↔ e∣progression c d k := by
  have ⟨du,fu⟩ := Nat.coprime_mul_iff_right.mp (unit.of_dvd_left de)
  have first := ((ZMod.isUnit_iff_coprime d e).mpr du.symm).neg.pow k
  have second := (ZMod.isUnit_iff_coprime k.factorial e).mpr fu.symm
  rw [←ZMod.natCast_zmod_eq_zero_iff_dvd,←ZMod.natCast_zmod_eq_zero_iff_dvd,
    progression_mod (de.trans address), (first.mul second).mul_right_eq_zero]

/-- In particular, repeated prime factors of n are retained at their exact
multiplicities in the gcd. The statement also holds for n=1. -/
theorem gcd_transfer {n m d c k : ℕ} (unit : n.Coprime (d*k.factorial))
    (address : n∣c+d*m) :
    (m.choose k).gcd n = (progression c d k).gcd n := by
  apply Nat.dvd_antisymm
  · have de := Nat.gcd_dvd_right (m.choose k) n
    exact Nat.dvd_gcd ((divisor_transfer de unit address).mp (Nat.gcd_dvd_left ..)) de
  · have de := Nat.gcd_dvd_right (progression c d k) n
    exact Nat.dvd_gcd ((divisor_transfer de unit address).mpr (Nat.gcd_dvd_left ..)) de

/-- If part of the scale is noninvertible, its common divisor with n
is mandatory in every output. Remove precisely that divisor before testing
the binomial, preserving valuations at the remaining prime powers. -/
theorem gcd_without_units {n m d c k : ℕ} (np : 0<n) (address : n∣c+d*m) :
    let g := (d^k*k.factorial).gcd n
    (progression c d k).gcd n = g*((m.choose k).gcd (n/g)) := by
  let scale := d^k*k.factorial
  let value := m.choose k
  let g := scale.gcd n
  have transfer {e : ℕ} (de : e∣n) : e∣progression c d k ↔ e∣scale*value := by
    have signed : (progression c d k : ZMod e) =
        (-1:ZMod e)^k*((scale*value:ℕ):ZMod e) := by
      rw [progression_mod (de.trans address)]
      dsimp only [scale,value]
      push_cast
      rw [show (-(d:ZMod e))=(-1)*(d:ZMod e) by ring,mul_pow]
      ring
    rw [←ZMod.natCast_zmod_eq_zero_iff_dvd,←ZMod.natCast_zmod_eq_zero_iff_dvd,
      signed, (isUnit_one.neg.pow k).mul_right_eq_zero]
  have whole : (progression c d k).gcd n=(scale*value).gcd n := by
    apply Nat.dvd_antisymm
    · have de := Nat.gcd_dvd_right (progression c d k) n
      exact Nat.dvd_gcd ((transfer de).mp (Nat.gcd_dvd_left ..)) de
    · have de := Nat.gcd_dvd_right (scale*value) n
      exact Nat.dvd_gcd ((transfer de).mpr (Nat.gcd_dvd_left ..)) de
  have clean : (scale/g).Coprime (n/g) := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right scale np)
  have ds : scale/g*g=scale := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have dn : n/g*g=n := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  change _ = g*value.gcd (n/g)
  calc
    _ = (scale*value).gcd n := whole
    _ = ((scale/g*value)*g).gcd ((n/g)*g) := by rw [mul_right_comm _ value g,ds,dn]
    _ = _ := by rw [Nat.gcd_mul_right,clean.gcd_mul_left_cancel,mul_comm]

/-- The unique least nonnegative row for a public origin and invertible
stride. This uses one modular inverse and no factorization of n. -/
noncomputable def row (n c d : ℕ) := ((-(c:ZMod n))*(d:ZMod n)⁻¹).val

theorem row_spec {n c d : ℕ} (np : 0<n) (unit : n.Coprime d) :
    row n c d<n ∧ n∣c+d*row n c d := by
  letI : NeZero n := ⟨np.ne'⟩
  refine ⟨ZMod.val_lt _,(ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp ?_⟩
  have cancel : (d:ZMod n)*(d:ZMod n)⁻¹=1 :=
    ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr unit.symm)
  rw [Nat.cast_add,Nat.cast_mul,row,ZMod.natCast_zmod_val,mul_left_comm, cancel,mul_one,add_neg_cancel]

theorem row_unique {n c d m : ℕ} (np : 0<n) (unit : n.Coprime d)
    (lt : m<n) (address : n∣c+d*m) : m=row n c d := by
  have ⟨small,other⟩ := row_spec (c:=c) np unit
  have eq := Nat.ModEq.add_left_cancel' c (address.modEq_zero_nat.trans other.zero_modEq_nat)
  have residues := Nat.ModEq.cancel_left_of_coprime unit eq
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt lt,Nat.mod_eq_of_lt small] using residues

/-- The proper gcd retains the full 5² in 275 = 5²·11. -/
theorem square_example : row 275 25 3=175 ∧ (Nat.choose 175 2).gcd 275=25 ∧
    (progression 25 3 2).gcd 275=25 := by
  exact ⟨(row_unique (by decide) (by decide) (by decide) (by decide)).symm, by decide +kernel⟩

/-- Below the column index, the zero binomial corresponds to a whole-modulus gcd. -/
theorem zero_example : row 25 22 3=1 ∧ (Nat.choose 1 2).gcd 25=25 ∧
    (progression 22 3 2).gcd 25=25 := by
  exact ⟨(row_unique (by decide) (by decide) (by decide) (by decide)).symm, by decide +kernel⟩

/-- When 3 divides the denominator factorial, one factor of 3 comes
from the scale and another from the chosen column. -/
theorem nonunit_example : (progression 9 1 3).gcd 27=9 ∧
    (Nat.choose 18 3).gcd 27=3 ∧ (Nat.factorial 3).gcd 27=3 := by decide +kernel

end PrimeFactors.QuotientPascalTransfer
