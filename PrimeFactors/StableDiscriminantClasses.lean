import PrimeFactors.MaskedSquareWitness
import PrimeFactors.PrimitiveNorm
import PrimeFactors.LocalSumMenu

/-! A discriminant which is already a nonzero square at an odd prime-power
precision remains a square at every precision. Only zero discriminants can
split into accepted and rejected lifts later. -/

namespace PrimeFactors.StableDiscriminantClasses

open scoped Classical

variable {p : ℕ} [Fact p.Prime]

private theorem project {a b : ℕ} (div : a ∣ b) (D : ℤ) (sq : IsSquare (D : ZMod b)) :
    IsSquare (D : ZMod a) := by
  simpa only [map_intCast] using IsSquare.map (ZMod.castHom div (ZMod a)) sq

/-- Nonzero here means nonzero modulo p^k. The residue may still be
divisible by p. The conclusion covers the same integer at any precision. -/
theorem stable_square (odd : p ≠ 2) (k : ℕ) (D : ℤ)
    (nz : (D : ZMod (p^k)) ≠ 0) (sq : IsSquare (D : ZMod (p^k))) (e : ℕ) :
    IsSquare (D : ZMod (p^e)) := by
  have prime := (Fact.out : p.Prime)
  by_cases unit : (D : ZMod p) ≠ 0
  · cases e with
    | zero =>
      rw [pow_zero]
      exact ⟨0,Subsingleton.elim _ _⟩
    | succ e =>
      have pos : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at nz
        exact nz (Subsingleton.elim _ _)
      exact (isSquare_primePow_iff_of_unit odd D unit e).mpr (project (dvd_pow_self p pos) D sq)
  · have div := (ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp (not_ne_iff.mp unit)
    match k with
    | 0 =>
      rw [pow_zero] at nz
      exact (nz (Subsingleton.elim _ _)).elim
    | 1 =>
      rw [pow_one] at nz
      exact (unit nz).elim
    | k+2 =>
      have base := project (pow_dvd_pow p (by omega : 2 ≤ k+2)) D sq
      obtain ⟨v,rep⟩ := (isSquare_prime_sq_iff_of_dvd D div).mp base
      have repr : D = v*(p : ℤ)^2 := rep.trans (mul_comm ..)
      have lower : IsSquare (v : ZMod (p^k)) := by
        rw [repr,show p^(k+2) = p^2*p^k by rw [pow_add,mul_comm]] at sq
        exact (MaskedSquareWitness.scale_iff prime.ne_zero _ v).mp sq
      have vn : (v : ZMod (p^k)) ≠ 0 := by
        intro zero
        obtain ⟨w,eq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd v (p^k)).mp zero
        apply nz
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd D (p^(k+2))).mpr
        refine ⟨w,?_⟩
        push_cast at eq ⊢
        rw [repr,eq,pow_add]
        ring
      rw [repr]
      push_cast
      exact (stable_square odd k v vn lower e).mul (IsSquare.sq _)
termination_by k

private theorem two_unit (odd : p ≠ 2) (e : ℕ) : IsUnit (2 : ZMod (p^e)) :=
  (ZMod.isUnit_iff_coprime 2 _).mpr
    ((Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two Fact.out).mpr odd.symm)))

/-- Any integer representative of an allowed class whose discriminant is
nonzero in the finite ring remains allowed at all precisions. -/
theorem permanent {n s : ℕ} (odd : p ≠ 2) (k : ℕ)
    (pass : AdmissibleSum (n : ZMod (p^(k+1))) (s : ZMod (p^(k+1))))
    (nz : (s : ZMod (p^(k+1)))^2-4*n ≠ 0) (e : ℕ) :
    AdmissibleSum (n : ZMod (p^e)) (s : ZMod (p^e)) := by
  rw [admissibleSum_iff_isSquare_of_two_unit (two_unit odd _)] at pass ⊢
  have nonzero : (((s : ℤ)^2-4*n : ℤ) : ZMod (p^(k+1))) ≠ 0 := by push_cast; exact nz
  have ok : IsSquare (((s : ℤ)^2-4*n : ℤ) : ZMod (p^(k+1))) := by push_cast; exact pass
  simpa only [Int.cast_sub,Int.cast_pow,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat] using
    stable_square odd (k+1) ((s : ℤ)^2-4*n) nonzero ok e

noncomputable def stableCount (n m : ℕ) := Nat.card
  {s : ZMod m // AdmissibleSum (n : ZMod m) s ∧ s^2-4*n ≠ 0}

/-- The zero discriminant classes have two possible sums for a square unit
and none for a nonsquare unit, at every positive precision. -/
theorem zero_count {n : ℕ} (odd : p ≠ 2) (unitN : ¬p ∣ n) (k : ℕ) :
    Nat.card {s : ZMod (p^(k+1)) // s^2-4*n = 0} =
      if IsSquare (n : ZMod p) then 2 else 0 := by
  classical
  have two : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have nz : (n : ZMod p) ≠ 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp.mt unitN
  have four : (4 : ZMod p) ≠ 0 := by
    convert mul_ne_zero two two using 1; norm_num
  have unit : (((4:ℤ)*n : ℤ) : ZMod p) ≠ 0 := by push_cast; exact mul_ne_zero four nz
  have iffSq : IsSquare ((4 : ZMod p)*n) ↔ IsSquare (n : ZMod p) := by
    constructor
    · rintro ⟨x,h⟩
      refine ⟨x/2,?_⟩
      field_simp [two]
      linear_combination h
    · exact fun h => (show IsSquare (4 : ZMod p) from ⟨2,by norm_num⟩).mul h
  simpa only [sub_eq_zero,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,iffSq] using
    primitiveNorm_odd_root_count odd ((4:ℤ)*n) unit k

/-- At most two accepted classes are omitted by the sufficient persistence
test. A nonsquare unit omits none. -/
theorem stable_count {n : ℕ} (odd : p ≠ 2) (unitN : ¬p ∣ n) (k : ℕ) :
    stableCount n (p^(k+1)) + (if IsSquare (n : ZMod p) then 2 else 0) =
      LocalSumMenu.count n (p^(k+1)) := by
  classical
  let m := p^(k+1)
  let A := Finset.univ.filter (AdmissibleSum (n : ZMod m))
  have accept (s : ZMod m) (h : s^2-4*n=0) : AdmissibleSum (n : ZMod m) s :=
    (admissibleSum_iff_isSquare_of_two_unit (two_unit odd (k+1)) _ _).mpr
      (by rw [h]; exact ⟨0,by simp⟩)
  rw [←zero_count odd unitN k,stableCount,LocalSumMenu.count]
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have split := Finset.filter_card_add_filter_neg_card_eq_card (s := A)
    (fun s : ZMod m => s^2-4*n=0)
  have zeros : A.filter (fun s : ZMod m => s^2-4*n=0) =
      Finset.univ.filter (fun s : ZMod m => s^2-4*n=0) := by
    ext s
    simp [A,and_iff_right_of_imp (accept s)]
  rw [zeros] at split
  simpa only [A,Finset.filter_filter,add_comm] using split

end PrimeFactors.StableDiscriminantClasses
