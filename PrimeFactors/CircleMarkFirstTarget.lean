import PrimeFactors.QuarticSlopeBit
import Mathlib.Tactic.NormNum.Prime

/-! When the first negative Jacobi target permits powers of two greater than four
in a square difference. The first six possible prime targets have a common test
on the public product residue. -/

namespace PrimeFactors.CircleMarkFirstTarget

open Finset
open private PrimeFactors.QuarticSlopeBit.square_crt from PrimeFactors.QuarticSlopeBit

/-- The target chosen by trying positive integers in order. -/
def First (n a : ℕ) : Prop :=
  jacobiSym (a:ℤ) n = -1 ∧ ∀ k : ℕ, jacobiSym (k:ℤ) n = -1 → a≤k

theorem prime {n a : ℕ} (large : 1<n) (first : First n a) : a.Prime := by
  have two : 2≤a := by
    obtain ⟨neg,_⟩ := first
    by_contra! h
    interval_cases a <;> simp [jacobiSym.zero_left large,jacobiSym.one_left] at neg
  by_contra bad
  obtain ⟨u,⟨v,eq⟩,up,ua⟩ := (Nat.not_prime_iff_exists_dvd_lt two).mp bad
  have va : v<a := by
    have vp : 0<v := by by_contra! h; simp [show v=0 by omega] at eq; omega
    simpa [eq] using (Nat.mul_lt_mul_of_pos_right (show 1<u by omega) vp)
  have neg := first.1
  rw [eq,Nat.cast_mul,jacobiSym.mul_left] at neg
  have L := jacobiSym.trichotomy (u:ℤ) n
  have R := jacobiSym.trichotomy (v:ℤ) n
  rcases L with l|l|l <;> rcases R with r|r|r <;> rw [l,r] at neg <;>
    first | exact (Nat.not_le_of_lt ua) (first.2 u l) | exact (Nat.not_le_of_lt va) (first.2 v r) | norm_num at neg

/-- For each prime through 13, squared coordinates miss the target modulo eight.
Hence the largest removable power of two is at most four. -/
theorem low_valuation {n a x : ℕ} (large : 1<n) (first : First n a) (early : a≤13) :
    ¬ x^2 ≡ a [MOD 8] := by
  have pp := prime large first
  have vals : (x%8)^2%8=0 ∨ (x%8)^2%8=1 ∨ (x%8)^2%8=4 := by
    have b := Nat.mod_lt x (by decide : 0<8)
    generalize x%8 = r at b ⊢
    interval_cases r <;> decide
  change x^2%8≠a%8
  rw [Nat.pow_mod]
  interval_cases a <;> first | norm_num at pp ⊢ <;> omega

abbrev modulus : ℕ := 120120
noncomputable abbrev small : Finset ℕ := {2,3,5,7,11,13}
noncomputable abbrev oddPrimes : Finset ℕ := {3,5,7,11,13}
def signedProduct (n : ℕ) : ℤ := if n%4=1 then n else -(n:ℤ)

private theorem local_sign {n r : ℕ} (odd : Odd n) (pr : r.Prime) (orr : r≠2) (cop : n.Coprime r) :
    jacobiSym (r:ℤ) n=1 ↔ IsSquare ((signedProduct n : ℤ):ZMod r) := by
  letI : Fact r.Prime := ⟨pr⟩
  have nro := Nat.odd_iff.mp odd
  have ro := pr.odd_of_ne_two orr
  have rr := Nat.odd_iff.mp ro
  have sym : jacobiSym (r:ℤ) n=jacobiSym (signedProduct n) r := by
    rw [←jacobiSym.quadratic_reciprocity_if rr nro]
    by_cases n1 : n%4=1
    · simp [signedProduct,n1,show n%4≠3 by omega]
    · have n3 : n%4=3 := by omega
      rw [signedProduct,if_neg n1,jacobiSym.neg _ ro]
      rcases (show r%4=1 ∨ r%4=3 by omega) with r1|r3
      · simp [r1,ZMod.χ₄_nat_one_mod_four r1]
      · simp [r3,n3,ZMod.χ₄_nat_three_mod_four r3]
  have nz : ((signedProduct n : ℤ) : ZMod r)≠0 := by
    have nn : (n:ZMod r)≠0 := fun h => (pr.coprime_iff_not_dvd.mp cop.symm)
      ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h)
    unfold signedProduct
    split <;> simpa using nn
  rw [sym,←jacobiSym.legendreSym.to_jacobiSym r]
  exact quadraticChar_one_iff_isSquare nz

private theorem pos_eight (z : ZMod 8) (odd : IsUnit z) : IsSquare z ↔ z=1 := by
  have all : ∀ t : ZMod 8, IsUnit t → (IsSquare t ↔ t=1) := by decide +kernel
  exact all z odd

theorem small_signs {n : ℕ} (odd : Odd n) (cop : n.Coprime modulus) :
    (∀ r∈small, jacobiSym (r:ℤ) n=1) ↔ IsSquare ((signedProduct n:ℤ):ZMod modulus) := by
  have nz8 := (ZMod.isUnit_iff_coprime n 8).mpr (cop.of_dvd_right (by decide : 8∣modulus))
  have eight : jacobiSym 2 n=1 ↔ IsSquare ((signedProduct n:ℤ):ZMod 8) := by
    have u : IsUnit ((signedProduct n:ℤ):ZMod 8) := by
      unfold signedProduct; split <;> simp [nz8]
    rw [pos_eight _ u,jacobiSym.at_two odd,ZMod.χ₈_nat_eq_if_mod_eight]
    have o := Nat.odd_iff.mp odd
    have eq : (n:ZMod 8) = ((n%8 : ℕ):ZMod 8) := (ZMod.natCast_mod ..).symm
    unfold signedProduct
    have f : n%4=(n%8)%4 := (Nat.mod_mod_of_dvd n (by decide : 4∣8)).symm
    rw [f]
    rcases (show n%8=1 ∨ n%8=3 ∨ n%8=5 ∨ n%8=7 by omega) with h|h|h|h <;>
      rw [h] at eq ⊢ <;> simp [o,eq] <;> decide
  have test (r : ℕ) (m : r∈oddPrimes) : jacobiSym (r:ℤ) n=1 ↔ IsSquare ((signedProduct n:ℤ):ZMod r) := by
    simp only [oddPrimes,mem_insert,mem_singleton] at m
    rcases m with rfl|rfl|rfl|rfl|rfl <;> apply local_sign odd (by decide) (by decide) (cop.of_dvd_right (by decide))
  change _ ↔ IsSquare ((signedProduct n:ℤ):ZMod (((((8*3)*5)*7)*11)*13))
  repeat rw [PrimeFactors.QuarticSlopeBit.square_crt (by decide)]
  simp only [small,forall_mem_insert,mem_singleton,forall_eq]
  rw [test 3 (by decide),test 5 (by decide),test 7 (by decide),test 11 (by decide),test 13 (by decide)]
  simp only [Nat.cast_ofNat,eight,and_assoc]

/-- The six small signs all pass precisely for a square or the negative of a
square modulo 120120. Their signs modulo four distinguish these two cases. -/
theorem quiet_iff_signed_square {n : ℕ} (odd : Odd n) (cop : n.Coprime modulus) :
    (∀ r∈small, jacobiSym (r:ℤ) n=1) ↔ IsSquare (n:ZMod modulus) ∨ IsSquare (-(n:ZMod modulus)) := by
  rw [small_signs odd cop]
  have down (z : ZMod modulus) (sq : IsSquare z) :
      IsSquare ((ZMod.castHom (by decide : 4∣modulus) (ZMod 4)) z) := sq.map _
  have nn := Nat.odd_iff.mp odd
  have cast : (n : ZMod 4) = ((n%4 : ℕ) : ZMod 4) := (ZMod.natCast_mod ..).symm
  by_cases n1 : n%4=1
  · have bad : ¬IsSquare (-(n:ZMod modulus)) := by
      intro sq
      have h := down _ sq
      rw [map_neg,map_natCast,cast,n1] at h
      exact (by decide : ¬IsSquare (-(1:ZMod 4))) h
    simp [signedProduct,n1,bad]
  · have n3 : n%4=3 := by omega
    have bad : ¬IsSquare (n:ZMod modulus) := by
      intro sq
      have h := down _ sq
      rw [map_natCast,cast,n3] at h
      exact (by decide : ¬IsSquare (3:ZMod 4)) h
    simp [signedProduct,n1,bad]

/-- For the first negative target, postponement beyond 13 is exactly the
all-positive character test. Coprimality excludes a zero in the small menu. -/
theorem late_iff {n a : ℕ} (large : 1<n) (cop : n.Coprime modulus) (first : First n a) :
    13<a ↔ ∀ r∈small, jacobiSym (r:ℤ) n=1 := by
  have pp := prime large first
  constructor
  · intro late r mem
    have dv : r∣modulus ∧ r≤13 := by
      simp only [small,mem_insert,mem_singleton] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have c := (cop.of_dvd_right dv.1).symm
    apply (jacobiSym.eq_one_or_neg_one (by simpa using c.gcd_eq_one : (r:ℤ).gcd n=1)).resolve_right
    exact fun neg => (Nat.not_le_of_lt (dv.2.trans_lt late)) (first.2 r neg)
  · intro signs
    by_contra! early
    have mem : a∈small := by
      interval_cases a <;> first | decide | norm_num at pp
    have := signs a mem
    have := first.1
    omega


end PrimeFactors.CircleMarkFirstTarget
