import PrimeFactors.AffinePrimeSign
import PrimeFactors.ReciprocalDivisorClasses
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ChineseRemainder

/-! For any odd nonsquare candidate coprime to the input, the affine draw has
a nonprincipal Jacobi character. The complete periods and the incomplete
final block can be counted without a primality assumption on the candidate. -/

namespace PrimeFactors.AffineNonsquareSign

open AffinePrimeSign ReciprocalSumCharacter Finset

private theorem odd_exponent {c : ℕ} (pos : c ≠ 0) (ns : ¬ IsSquare c) :
    ∃ p ∈ c.primeFactors, Odd (c.factorization p) := by
  by_contra! no
  let root := ∏ p ∈ c.primeFactors, p^(c.factorization p/2)
  apply ns
  refine ⟨root, ?_⟩
  rw [← pow_two, show root^2 = ∏ p ∈ c.primeFactors, (p^(c.factorization p/2))^2 from
    (prod_pow ..).symm]
  calc
    c = ∏ p ∈ c.primeFactors, p^(c.factorization p) := (Nat.factorization_prod_pow_eq_self pos).symm
    _ = _ := by
      apply prod_congr rfl
      intro p hp
      rw [← pow_mul]
      congr 1
      have even := Nat.even_iff.mp (Nat.not_odd_iff_even.mp (no p hp))
      omega

/-- An odd nonsquare denominator has a negative Jacobi value. The proof picks
a prime with odd exponent, chooses a nonresidue there, and prescribes 1 on
the entire complementary prime-power factor. -/
theorem nonprincipal {c : ℕ} (odd : Odd c) (ns : ¬ IsSquare c) :
    ∃ a : ℕ, jacobiSym (a : ℤ) c = -1 := by
  obtain ⟨p,mem,parity⟩ := odd_exponent odd.pos.ne' ns
  have pp := Nat.prime_of_mem_primeFactors mem
  letI : Fact p.Prime := ⟨pp⟩
  have hp : p ≠ 2 := fun h => odd.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors mem)
  obtain ⟨y,hy⟩ := quadraticChar_exists_neg_one (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  have neg : jacobiSym (y.val : ℤ) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hy
  let b := c / p^c.factorization p
  let a := Nat.chineseRemainder (Nat.coprime_ordCompl pp odd.pos.ne') y.val 1
  have left : jacobiSym (a.val : ℤ) p = jacobiSym (y.val : ℤ) p :=
    jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr a.property.1)
  have right : jacobiSym (a.val : ℤ) b = jacobiSym 1 b := by
    have h := jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr a.property.2)
    simpa only [Nat.cast_one] using h
  have product : p^c.factorization p * b = c := Nat.ordProj_mul_ordCompl_eq_self c p
  have bn : b ≠ 0 := (Nat.ordCompl_pos p odd.pos.ne').ne'
  refine ⟨a.val, ?_⟩
  calc
    jacobiSym (a.val : ℤ) c = jacobiSym (a.val : ℤ) (p^c.factorization p*b) := congrArg _ product.symm
    _ = -1 := by
      rw [jacobiSym.mul_right' _ (pow_ne_zero _ pp.ne_zero) bn, jacobiSym.pow_right, left,
        right, neg, jacobiSym.one_left, mul_one, parity.neg_one_pow]

noncomputable def positive (c : ℕ) [NeZero c] : Finset (ZMod c) :=
  univ.filter fun x => sign x = 1

private theorem unit_of_sign {c : ℕ} [NeZero c] {x : ZMod c} (h : sign x ≠ 0) :
    IsUnit x := by
  have rep : ((x.val : ℤ) : ZMod c) = x := by simp
  rw [← rep, sign_cast] at h
  have cop : x.val.Coprime c := by
    by_contra bad
    exact h (jacobiSym.eq_zero_iff.mpr ⟨NeZero.ne c,
      by simpa only [Int.gcd_natCast_natCast] using bad⟩)
  simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime x.val c).mpr cop

/-- Exactly half the units of any odd nonsquare modulus have positive sign,
even with repeated prime factors. -/
theorem positive_count {c : ℕ} [NeZero c] (odd : Odd c) (ns : ¬ IsSquare c) :
    2*(positive c).card = c.totient := by
  classical
  obtain ⟨a,ha⟩ := nonprincipal odd ns
  have sa : sign (a : ZMod c) = -1 := by simpa only [← sign_cast, Int.cast_natCast] using ha
  obtain ⟨v,hv⟩ := unit_of_sign (sa ▸ (by decide : (-1 : ℤ) ≠ 0))
  have neg : sign (v : ZMod c) = -1 := hv ▸ sa
  let P (x : (ZMod c)ˣ) := sign (x : ZMod c) = 1
  let U := univ.filter P
  let T := univ.filter fun x => ¬ P x
  have flip (x : (ZMod c)ˣ) : P (v*x) ↔ ¬ P x := by
    simp only [P, Units.val_mul, sign_mul, neg, neg_one_mul]
    rcases ReciprocalDivisorClasses.unit_sign x with h | h <;> omega
  have toT : U.card ≤ T.card := by
    refine card_le_card_of_injOn (v*·) ?_ (mul_right_injective v).injOn
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _,fun h => (flip x).mp h (mem_filter.mp hx).2⟩
  have toU : T.card ≤ U.card := by
    refine card_le_card_of_injOn (v*·) ?_ (mul_right_injective v).injOn
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _,(flip x).mpr (mem_filter.mp hx).2⟩
  have parts := filter_card_add_filter_neg_card_eq_card (s := univ) P
  change U.card + T.card = _ at parts
  rw [card_univ, ZMod.card_units_eq_totient] at parts
  have fs : U.image (fun u : (ZMod c)ˣ => (u : ZMod c)) = positive c := by
    ext x
    constructor
    · rintro hx
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hu).2⟩
    · intro hx
      have plus : sign x = 1 := (mem_filter.mp hx).2
      obtain ⟨u,eq⟩ := unit_of_sign (plus ▸ (by decide : (1 : ℤ) ≠ 0))
      exact mem_image.mpr ⟨u,mem_filter.mpr ⟨mem_univ _, by simpa only [P, eq] using plus⟩,eq⟩
  rw [← fs, card_image_of_injective _ (fun _ _ eq => Units.ext eq)]
  omega

/-- Complete positive residues times the maximum number of draws per residue,
including the clipped last block. -/
theorem ceiling_bound {N c : ℕ} (odd : Odd c) (ns : ¬ IsSquare c) (cop : c.Coprime N) :
    2*(seeds N c).card ≤ ((N-1)/c+1)*c.totient := by
  classical
  letI : NeZero c := ⟨odd.pos.ne'⟩
  have four : (4*N).Coprime c := Nat.coprime_mul_iff_left.mpr ⟨
    by simpa using odd.coprime_two_left.pow_left 2, cop.symm⟩
  have unit : IsUnit (4*(N : ZMod c)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (ZMod.isUnit_iff_coprime _ _).mpr four
  let code (r : ℕ) : ℕ × ZMod c := (r/c, 1-4*(N : ZMod c)*r)
  have bound : (seeds N c).card ≤ (range ((N-1)/c+1) ×ˢ positive c).card := by
    apply card_le_card_of_injOn code
    · intro r hr
      obtain ⟨inside,pass⟩ := mem_seeds.mp hr
      refine mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le
        (Nat.div_le_div_right (by omega))),mem_filter.mpr ⟨mem_univ _,?_⟩⟩
      change sign (1-4*(N : ZMod c)*(r : ZMod c)) = 1
      rw [passes, ← sign_cast] at pass
      push_cast at pass
      exact pass
    · intro r _ s _ eq
      have quot : r/c = s/c := congrArg Prod.fst eq
      have affine : 1-4*(N : ZMod c)*r = 1-4*(N : ZMod c)*s := congrArg Prod.snd eq
      have field := unit.mul_left_cancel (sub_right_injective affine)
      have rem := (ZMod.natCast_eq_natCast_iff' r s c).mp field
      calc
        r = c*(r/c)+r%c := (Nat.div_add_mod r c).symm
        _ = s := by rw [quot,rem,Nat.div_add_mod]
  rw [card_product,card_range] at bound
  calc
    _ ≤ 2*(((N-1)/c+1)*(positive c).card) := Nat.mul_le_mul_left _ bound
    _ = ((N-1)/c+1)*(2*(positive c).card) := by ring
    _ = _ := by rw [positive_count odd ns]

/-- A false nonsquare unit candidate in the lower-factor range survives
strictly fewer than half the draws. -/
theorem false_strict {N c : ℕ} (odd : Odd c) (ns : ¬ IsSquare c) (cop : c.Coprime N)
    (fit : c^2 ≤ N) : 2*(seeds N c).card < N := by
  have big : 1 < c := by
    by_contra! small
    have eq : c = 1 := by have := odd.pos; omega
    exact ns (eq ▸ IsSquare.one)
  have tot := Nat.totient_lt c big
  have q : c ≤ N/c := (Nat.le_div_iff_mul_le odd.pos).mpr (by simpa [pow_two] using fit)
  have round : (N-1)/c+1 ≤ N/c+1 := Nat.add_le_add_right (Nat.div_le_div_right (by omega)) 1
  have entry := (ceiling_bound odd ns cop).trans
    (Nat.mul_le_mul round (show c.totient ≤ c-1 by omega))
  have full := Nat.div_mul_le_self N c
  have scale : (N/c)*(c-1) + N/c = (N/c)*c := by
    calc
      _ = (N/c)*(c-1+1) := by ring
      _ = _ := by rw [show c-1+1=c by omega]
  rw [Nat.add_mul, Nat.one_mul] at entry
  omega

theorem false_bound {N c : ℕ} (odd : Odd c) (ns : ¬ IsSquare c) (cop : c.Coprime N)
    (fit : c^2 ≤ N) : 2*(seeds N c).card ≤ N := (false_strict odd ns cop fit).le

end PrimeFactors.AffineNonsquareSign
