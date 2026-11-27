import PrimeFactors.PrimePowerCount
import PrimeFactors.FactorSumCRT

/-! The least translation preserving the admissible factor-sum classes modulo
an odd prime square is determined by the quadratic character of the product. -/

namespace PrimeFactors.MinimalPrimeSquarePeriod

open scoped Classical

/-- Translation of every admissible sum class, in both directions. -/
def Period (n m t : ℕ) : Prop :=
  ∀ x : ZMod m, AdmissibleSum (n : ZMod m) (x+t) ↔ AdmissibleSum (n : ZMod m) x

/-- Summing all elements of a translation-invariant subset gives a necessary
divisibility constraint on the translation. -/
theorem modulus_dvd_card_mul {m t : ℕ} [NeZero m] (P : ZMod m → Prop)
    (h : ∀ x : ZMod m, P (x+t) ↔ P x) : m ∣ Nat.card {x // P x} * t := by
  classical
  let S := {x // P x}
  let e : S ≃ S := {
    toFun := fun x => ⟨x.1+t, (h _).mpr x.2⟩
    invFun := fun x => ⟨x.1-t, (h _).mp (by simpa using x.2)⟩
    left_inv := fun x => Subtype.ext (add_sub_cancel_right _ _)
    right_inv := fun x => Subtype.ext (sub_add_cancel _ _) }
  have total := e.sum_comp (fun x : S => x.1)
  change (∑ x : S, (x.1+t : ZMod m)) = ∑ x : S, x.1 at total
  rw [Finset.sum_add_distrib, add_eq_left, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at total
  apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa only [Nat.cast_mul, Nat.card_eq_fintype_card] using total

variable {p n : ℕ} [Fact p.Prime]

private theorem local_count (odd : p ≠ 2) (unitN : ¬ p ∣ n) :
    Nat.card {s : ZMod (p^2) // AdmissibleSum (n : ZMod (p^2)) s} =
      if IsSquare (n : ZMod p) then (p-3)/2*p + 2 else (p-1)/2*p := by
  classical
  have nz : firstPrimeDigit p 1 (n : ZMod (p^2)) ≠ 0 := by
    rw [map_natCast]
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd n p).mp.mt unitN
  have count := card_primePower_admissibleSum odd 1 (n : ZMod (p^2)) nz
  rw [map_natCast] at count
  by_cases sq : IsSquare (n : ZMod p) <;>
    simpa [sq,primePowerSumCount,collidingDigitCount,primePowerSquareCount] using count

/-- For a square product only translations by the entire modulus work. -/
theorem square_iff (odd : p ≠ 2) (unitN : ¬p ∣ n) (sq : IsSquare (n : ZMod p)) (t : ℕ) :
    Period n (p^2) t ↔ p^2 ∣ t := by
  classical
  constructor
  · intro h
    have d := modulus_dvd_card_mul (AdmissibleSum (n : ZMod (p^2))) h
    rw [local_count odd unitN, if_pos sq] at d
    have prime := (Fact.out : p.Prime)
    have large : 2<p := by have := prime.two_le; omega
    have cop : p.Coprime ((p-3)/2*p+2) := by
      apply prime.coprime_iff_not_dvd.mpr
      intro hd
      have two := (Nat.dvd_add_iff_right (dvd_mul_left p ((p-3)/2))).mpr hd
      exact Nat.not_dvd_of_pos_of_lt (by decide : 0<2) large two
    exact (Nat.Coprime.pow_left 2 cop).dvd_of_dvd_mul_left d
  · intro h x
    rw [(ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr h, add_zero]

/-- At a nonsquare product, every discriminant residue is regular, so
admissibility over the prime square reads only its first digit. -/
theorem nonsquare_pullback (odd : p ≠ 2) (sq : ¬IsSquare (n : ZMod p)) (s : ℕ) :
    AdmissibleSum (n : ZMod (p^2)) (s : ZMod (p^2)) ↔
      AdmissibleSum (n : ZMod p) (s : ZMod p) := by
  have two : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have regular : (((s : ℤ)^2-4*n : ℤ) : ZMod p) ≠ 0 := by
    intro zero
    push_cast at zero
    apply sq
    refine ⟨(s : ZMod p)/2, ?_⟩
    field_simp [two]
    linear_combination -zero
  simpa only [Int.cast_natCast] using
    admissibleSum_primePow_iff_of_regular odd (n : ℤ) (s : ℤ) regular 1

/-- At a nonsquare product the positive periods are precisely the multiples
of the underlying prime. -/
theorem nonsquare_iff (odd : p ≠ 2) (unitN : ¬p ∣ n) (sq : ¬IsSquare (n : ZMod p))
    (t : ℕ) : Period n (p^2) t ↔ p ∣ t := by
  classical
  constructor
  · intro h
    have d := modulus_dvd_card_mul (AdmissibleSum (n : ZMod (p^2))) h
    rw [local_count odd unitN, if_neg sq, pow_two] at d
    have prime := (Fact.out : p.Prime)
    have large : 2<p := by have := prime.two_le; omega
    have co : p.Coprime ((p-1)/2) :=
      prime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    apply co.dvd_of_dvd_mul_left
    apply (Nat.mul_dvd_mul_iff_left prime.pos).mp
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using d
  · intro h x
    obtain ⟨s,rfl⟩ := ZMod.natCast_zmod_surjective x
    rw [← Nat.cast_add, nonsquare_pullback odd sq, nonsquare_pullback odd sq, Nat.cast_add,
      (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr h, add_zero]

/-- For coprime moduli a translation preserves the whole admissible set
exactly when it preserves both component sets. Each component contains
`1+n`, so projecting the product detects changes in either component. -/
theorem crt_iff {a b : ℕ} (cop : a.Coprime b) (n t : ℕ) :
    Period n (a*b) t ↔ Period n a t ∧ Period n b t := by
  let e := ZMod.chineseRemainder cop
  have split (s : ZMod (a*b)) : AdmissibleSum (n : ZMod (a*b)) s ↔
      AdmissibleSum (n : ZMod a) (e s).1 ∧ AdmissibleSum (n : ZMod b) (e s).2 := by
    simpa only [e,map_natCast,Prod.fst_natCast,Prod.snd_natCast] using
      admissibleSum_crt_iff cop (n : ZMod (a*b)) s
  have transform : Period n (a*b) t ↔ ∀ x : ZMod a, ∀ y : ZMod b,
      (AdmissibleSum (n : ZMod a) (x+t) ∧ AdmissibleSum (n : ZMod b) (y+t) ↔
        AdmissibleSum (n : ZMod a) x ∧ AdmissibleSum (n : ZMod b) y) := by
    constructor
    · intro h x y
      have z := h (e.symm (x,y))
      rw [split,split,map_add,map_natCast,e.apply_symm_apply] at z
      exact z
    · intro h x
      rw [split,split,map_add,map_natCast]
      exact h _ _
  rw [transform]
  constructor
  · intro h
    have good (m : ℕ) : AdmissibleSum (n : ZMod m) (1+n) := ⟨1,n,one_mul _,rfl⟩
    have keep := (h (1+n) (1+n)).mpr ⟨good a,good b⟩
    constructor
    · intro x
      simpa only [good b,keep.2,and_true] using h x (1+n)
    · intro x
      simpa only [good a,keep.1,true_and] using h (1+n) x
  · rintro ⟨ha,hb⟩ x y
    exact and_congr (ha x) (hb y)

/-- If the component periods are exactly the multiples of `u` and `v`,
the combined periods are the multiples of their least common multiple. -/
theorem crt_lcm {a b n u v : ℕ} (cop : a.Coprime b)
    (ha : ∀ t, Period n a t ↔ u ∣ t) (hb : ∀ t, Period n b t ↔ v ∣ t) (t : ℕ) :
    Period n (a*b) t ↔ u.lcm v ∣ t := by
  rw [crt_iff cop,ha,hb,Nat.lcm_dvd_iff]

end PrimeFactors.MinimalPrimeSquarePeriod
