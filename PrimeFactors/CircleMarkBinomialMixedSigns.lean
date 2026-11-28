import PrimeFactors.CircleMarkJacobiMaskDegree

/-! For a product congruent to three modulo four, no power binomial can
reach the full product of the local half-periods. Negation exchanges signs
at one prime and preserves them at the other. -/

namespace PrimeFactors.CircleMarkBinomialMixedSigns

open Finset Polynomial CircleMarkJacobiMask CircleMarkJacobiMaskDegree
open scoped Classical
open private PrimeFactors.CircleMarkJacobiMaskDegree.sign_caps from PrimeFactors.CircleMarkJacobiMaskDegree
open CircleMarkJacobiMaskDegree (sign_caps)

private theorem bin_mem {r e : ℕ} [Fact r.Prime] {c s : ℤ} {x : ZMod r} :
    x ∈ signedRoots r (X^e-C c) s ↔ x^e=(c:ZMod r) ∧ quadraticChar (ZMod r) x=s := by
  simp [signedRoots,CircleMarkJacobiMask.rootSet,sub_eq_zero]

private theorem neg_char {r : ℕ} [Fact r.Prime] (x : ZMod r) :
    quadraticChar (ZMod r) (-x) = quadraticChar (ZMod r) (-1) * quadraticChar (ZMod r) x := by
  rw [←neg_one_mul x, map_mul]

private theorem at_minus_one {r : ℕ} [Fact r.Prime] (op : r≠2) :
    quadraticChar (ZMod r) (-1) = if r%4=1 then 1 else -1 := by
  have odd := Nat.odd_iff.mp (Fact.out (p:=r.Prime) |>.odd_of_ne_two op)
  rw [quadraticChar_neg_one (by rwa [ZMod.ringChar_zmod_n]),ZMod.card,ZMod.χ₄_nat_eq_if_mod_four,
    if_neg (by omega)]

/-- At a prime congruent to three modulo four, every even power binomial
has local sum zero. Opposite roots have opposite characters. -/
theorem even_vanish {r e : ℕ} [Fact r.Prime] (three : r%4=3) (ee : Even e) (c : ℤ) :
    localSum r (X^e-C c) = 0 := by
  have op : r≠2 := by omega
  have neg := at_minus_one op
  rw [if_neg (by omega)] at neg
  have swap (s : ℤ) (x : ZMod r) (hx : x ∈ signedRoots r (X^e-C c) s) :
      -x ∈ signedRoots r (X^e-C c) (-s) := by
    obtain ⟨pow,sign⟩ := bin_mem.mp hx
    exact bin_mem.mpr ⟨by rw [ee.neg_pow,pow],by rw [neg_char,neg,sign,neg_one_mul]⟩
  rw [local_difference op,sub_eq_zero]
  congr 1
  apply card_bij (fun x _ => -x)
  · intro x hx
    simpa using swap (-1) x hx
  · intro x _ y _ eq
    exact neg_inj.mp eq
  · intro y hy
    exact ⟨-y,swap 1 y hy,neg_neg _⟩

private theorem sign_half {r e : ℕ} [hr : Fact r.Prime] (one : r%4=1) (eo : Odd e) (c s : ℤ)
    (sn : s≠0) : 2*(signedRoots r (X^e-C c) s).card ≤ (signedRoots r 0 s).card := by
  let S := signedRoots r (X^e-C c) s
  have op : r≠2 := by omega
  have neg := at_minus_one op
  rw [if_pos one] at neg
  have sub : S ∪ S.image Neg.neg ⊆ signedRoots r 0 s := by
    intro x hx
    have sign : quadraticChar (ZMod r) x=s := by
      rcases mem_union.mp hx with h|h
      · exact (bin_mem.mp h).2
      · obtain ⟨w,hw,rfl⟩ := mem_image.mp h
        rw [neg_char,neg,one_mul]
        exact (bin_mem.mp hw).2
    simpa [signedRoots,CircleMarkJacobiMask.rootSet] using sign
  have dj : Disjoint S (S.image Neg.neg) := by
    apply disjoint_left.mpr
    intro x hx im
    obtain ⟨w,hw,rfl⟩ := mem_image.mp im
    obtain ⟨pow,sign⟩ := bin_mem.mp hw
    have opp := (bin_mem.mp hx).1
    rw [eo.neg_pow] at opp
    have same : -(w^e)=w^e := opp.trans pow.symm
    rcases (ZMod.neg_eq_self_iff _).mp same with zero|evenR
    · have nz : w≠0 := by intro eq; rw [eq,quadraticChar_zero] at sign; exact sn sign.symm
      exact pow_ne_zero e nz zero
    · omega
  have bound := card_le_card sub
  rw [card_union_of_disjoint dj,card_image_of_injective _ neg_injective] at bound
  simpa only [two_mul] using bound

/-- At a prime congruent to one modulo four, an odd power binomial removes
at most one root from each opposite pair of either character sign. -/
theorem odd_half {r e : ℕ} [Fact r.Prime] (one : r%4=1) (eo : Odd e) (c : ℤ) :
    2*|localSum r (X^e-C c)| ≤ (half r:ℤ) := by
  have op : r≠2 := by omega
  obtain ⟨minus,plus⟩ := sign_caps op 0
  have a := (sign_half one eo c (-1) (by decide)).trans minus
  have b := (sign_half one eo c 1 (by decide)).trans plus
  rw [local_difference op]
  rcases le_total (0:ℤ) ((signedRoots r (X^e-C c) (-1)).card-(signedRoots r (X^e-C c) 1).card:ℤ) with pos|neg
  · rw [abs_of_nonneg pos]; omega
  · rw [abs_of_nonpos neg]; omega

private theorem mixed_local {p q e : ℕ} [Fact p.Prime] [Fact q.Prime]
    (one : p%4=1) (three : q%4=3) (c : ℤ) :
    2*(|localSum p (X^e-C c)| * |localSum q (X^e-C c)|) ≤ (half p:ℤ)*half q := by
  rcases Nat.even_or_odd e with even|odd
  · rw [even_vanish three even,abs_zero,mul_zero,mul_zero]
    positivity
  · have h : |localSum q (X^e-C c)| ≤ (half q:ℤ) := (local_bound (show q≠2 by omega) (X^e-C c)).trans
      (by exact_mod_cast min_le_left (half q) (X^e-C c : ℤ[X]).natDegree)
    rw [←mul_assoc]
    exact mul_le_mul (odd_half one odd c) h (abs_nonneg _) (Int.natCast_nonneg _)

/-- The public product residue alone rules out the full half-period product.
For any exponent and integer constant the binomial magnitude is at most half
that value. -/
theorem mixed_bound {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q)
    (mixed : (p*q)%4=3) (e : ℕ) (c : ℤ) :
    2*|globalSum (p*q) (X^e-C c)| ≤ (half p:ℤ)*half q := by
  have classify : ∀ a b : Fin 4, (a.val*b.val)%4=3 →
      (a.val=1 ∧ b.val=3) ∨ (b.val=1 ∧ a.val=3) := by decide
  rw [Nat.mul_mod] at mixed
  rw [factorization diff,abs_mul]
  rcases classify ⟨p%4,Nat.mod_lt _ (by decide)⟩ ⟨q%4,Nat.mod_lt _ (by decide)⟩ mixed with h|h
  · exact mixed_local h.1 h.2 c
  · simpa only [mul_comm] using mixed_local (e:=e) h.1 h.2 c

end PrimeFactors.CircleMarkBinomialMixedSigns
