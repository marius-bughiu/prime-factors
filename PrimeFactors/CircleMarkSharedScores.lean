import PrimeFactors.CircleMarkJacobiMask

/-! Two square masks evaluated at the same residue have the same sign wherever
both survive. Their mixed second moment counts the nonzero residue pairs
surviving the union of the two coordinate sets. -/

namespace PrimeFactors.CircleMarkSharedScores

open Finset Polynomial CircleMarkJacobiMask CircleMarkTargetFrequency
open scoped Classical

/-- The masked Jacobi score of one residue in the public modulus. -/
noncomputable def score (n : ℕ) [NeZero n] (C : Finset ℕ) (t : ZMod n) : ℤ :=
  jacobiSym ((t.val : ℤ) * ((squareMask C).eval (t.val : ℤ))^2) n

theorem sum_score (n : ℕ) [NeZero n] (C : Finset ℕ) :
    (∑ t : ZMod n, score n C t) = globalSum n (squareMask C) := rfl

/-- A squared mask either preserves the Jacobi symbol or sets its score to zero.
The gcd check in the condition uses just the public modulus. -/
theorem score_eq (n : ℕ) [NeZero n] (C : Finset ℕ) (t : ZMod n) :
    score n C t = if ((squareMask C).eval (t.val : ℤ)).gcd n = 1 then
      jacobiSym (t.val : ℤ) n else 0 := by
  rw [score,jacobiSym.mul_left]
  split_ifs with cop
  · rw [jacobiSym.sq_one' cop,mul_one]
  · rw [jacobiSym.pow_left,jacobiSym.eq_zero_iff_not_coprime.mpr cop]
    simp

/-- Nonzero residues at a prime that none of the square roots in the mask removes. -/
noncomputable def survivors (r : ℕ) [Fact r.Prime] (C : Finset ℕ) : Finset (ZMod r) :=
  (univ.erase 0) \ covered r C

/-- Number of pairs of surviving local residues. -/
noncomputable def live (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (C : Finset ℕ) : ℕ :=
  (p-1-(covered p C).card)*(q-1-(covered q C).card)

theorem card_survivors (r : ℕ) [Fact r.Prime] (C : Finset ℕ) :
    (survivors r C).card = r-1-(covered r C).card := by
  have sub : covered r C ⊆ univ.erase 0 :=
    fun x hx => mem_erase.mpr ⟨(mem_erase.mp hx).1, mem_univ x⟩
  rw [survivors,card_sdiff sub,card_erase_of_mem (mem_univ _),card_univ,ZMod.card]

private theorem mem_survivors {r : ℕ} [Fact r.Prime] {C : Finset ℕ} {x : ZMod r} :
    x ∈ survivors r C ↔ x ≠ 0 ∧ x ∉ rootSet r (squareMask C) := by
  rw [rootSet_squareMask]
  simp only [survivors,mem_sdiff,mem_erase,mem_univ,and_true,covered]
  tauto

private theorem survivors_union (r : ℕ) [Fact r.Prime] (C D : Finset ℕ) (x : ZMod r) :
    x ∈ survivors r (C ∪ D) ↔ x ∈ survivors r C ∧ x ∈ survivors r D := by
  simp only [mem_survivors,rootSet_squareMask,image_union,mem_union]
  tauto

private noncomputable def localScore (r : ℕ) [Fact r.Prime] (C : Finset ℕ) (x : ZMod r) : ℤ :=
  if x ∈ survivors r C then quadraticChar (ZMod r) x else 0

private theorem local_eval (r : ℕ) [Fact r.Prime] (C : Finset ℕ) (a : ℕ) :
    quadraticChar (ZMod r) (((a:ℤ)*((squareMask C).eval (a:ℤ))^2:ℤ):ZMod r) =
      localScore r C a := by
  let Q := squareMask C
  let P := Q.map (Int.castRingHom (ZMod r))
  have eval_at : (Int.castRingHom (ZMod r)) (Q.eval (a:ℤ)) = P.eval (a:ZMod r) := by
    simpa only [P,←eval₂_eq_eval_map,Int.coe_castRingHom,Int.cast_natCast] using
      (eval₂_at_apply (p:=Q) (Int.castRingHom (ZMod r)) (a:ℤ)).symm
  have root : (a:ZMod r) ∈ rootSet r (squareMask C) ↔ P.eval (a:ZMod r) = 0 := by
    simp only [CircleMarkJacobiMask.rootSet,mem_filter,mem_univ,true_and,P,Q]
  change quadraticChar (ZMod r) (((a:ℤ)*(Q.eval (a:ℤ))^2:ℤ):ZMod r)=_
  simp only [Int.coe_castRingHom] at eval_at
  rw [Int.cast_mul,Int.cast_pow,Int.cast_natCast,eval_at,map_mul,localScore]
  simp only [mem_survivors,root]
  by_cases z : (a:ZMod r)=0
  · simp [z,quadraticChar_zero]
  by_cases zero : P.eval (a:ZMod r)=0
  · simp [zero,quadraticChar_zero]
  · simp [zero,z,quadraticChar_sq_one' zero]

private theorem separated {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (C : Finset ℕ)
    (t : ZMod (p*q)) :
    score (p*q) C t = localScore p C t.val * localScore q C t.val := by
  rw [score,ExtensionTrace.jacobi_crt,local_eval,local_eval]

private theorem localScore_eq (r : ℕ) [Fact r.Prime] (C : Finset ℕ) (x : ZMod r) :
    localScore r C x = if x ∈ covered r C then 0 else quadraticChar (ZMod r) x := by
  by_cases z : x=0
  · simp [z,localScore,survivors,covered,quadraticChar_zero]
  by_cases m : x ∈ covered r C <;> simp [localScore,survivors,m,z]

/-- A covered local square erases the public Jacobi score. -/
theorem score_eq_of_covered {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (C : Finset ℕ)
    (t : ZMod (p*q)) :
    score (p*q) C t =
      if (t.val : ZMod p) ∈ covered p C ∨ (t.val : ZMod q) ∈ covered q C then 0
      else jacobiSym (t.val : ℤ) (p*q) := by
  rw [separated,localScore_eq,localScore_eq,ExtensionTrace.jacobi_crt]
  by_cases pc : (t.val : ZMod p) ∈ covered p C <;>
    by_cases qc : (t.val : ZMod q) ∈ covered q C <;>
      simp only [pc,qc,or_true,true_or,or_false,false_or,if_true,if_false,zero_mul,mul_zero,Int.cast_natCast]

private theorem local_product (r : ℕ) [Fact r.Prime] (C D : Finset ℕ) (x : ZMod r) :
    localScore r C x * localScore r D x = if x ∈ survivors r (C ∪ D) then 1 else 0 := by
  simp only [localScore,survivors_union]
  by_cases hc : x ∈ survivors r C
  · by_cases hd : x ∈ survivors r D
    · simp only [hc,hd,if_true,and_self]
      exact (sq (quadraticChar (ZMod r) x)).symm.trans (quadraticChar_sq_one (mem_survivors.mp hc).1)
    · simp [hd]
  · simp [hc]

/-- The product of two scores on one residue is the indicator of joint survival. -/
theorem product_eq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (C D : Finset ℕ)
    (t : ZMod (p*q)) :
    score (p*q) C t * score (p*q) D t =
      (if (t.val : ZMod p) ∈ survivors p (C ∪ D) then 1 else 0) *
      (if (t.val : ZMod q) ∈ survivors q (C ∪ D) then 1 else 0) := by
  rw [separated,separated,mul_mul_mul_comm,local_product,local_product]

/-- The unnormalized mixed second moment on a shared residue counts the
surviving nonzero classes modulo each prime. -/
theorem sum_product {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p ≠ q) (C D : Finset ℕ) :
    (∑ t : ZMod (p*q), score (p*q) C t * score (p*q) D t) = (live p q (C ∪ D) : ℤ) := by
  let e := ZMod.chineseRemainder ((Nat.coprime_primes hp.out hq.out).mpr diff)
  let indicator (r : ℕ) [Fact r.Prime] (x : ZMod r) : ℤ :=
    if x ∈ survivors r (C ∪ D) then 1 else 0
  have count (r : ℕ) [Fact r.Prime] :
      (∑ x, indicator r x) = ((r-1-(covered r (C ∪ D)).card : ℕ) : ℤ) := by
    simp [indicator,sum_boole,card_survivors]
  rw [live,Nat.cast_mul,←count p,←count q]
  apply ExtensionTrace.separated e.toEquiv
  intro t
  have coord : e t = (t.val : ℕ) := by rw [←map_natCast e,ZMod.natCast_zmod_val]
  change _ = indicator p (e t).1 * indicator q (e t).2
  rw [coord]
  exact product_eq C D t

end PrimeFactors.CircleMarkSharedScores
