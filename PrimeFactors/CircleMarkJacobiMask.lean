import PrimeFactors.CircleMarkMidcutReadout
import PrimeFactors.ExtensionTrace
import Mathlib.Algebra.Polynomial.BigOperators

/-! A complete Jacobi sum over the public product records the product of
the two local counts of distinct square residues in a prefix menu. -/
namespace PrimeFactors.CircleMarkJacobiMask

open Finset Polynomial CircleMarkTargetFrequency CircleMarkMidcutReadout
open scoped Classical

/-- Residues where the integer polynomial vanishes after reduction at r. -/
noncomputable def rootSet (r : ℕ) [Fact r.Prime] (Q : Polynomial ℤ) : Finset (ZMod r) :=
  univ.filter fun t => (Q.map (Int.castRingHom (ZMod r))).eval t = 0

noncomputable def localSum (r : ℕ) [Fact r.Prime] (Q : Polynomial ℤ) : ℤ :=
  ∑ t : ZMod r, quadraticChar (ZMod r) (t*((Q.map (Int.castRingHom (ZMod r))).eval t)^2)

/-- Each summand takes one Jacobi symbol at an integer polynomial value.
The input modulus alone specifies the complete residue population. -/
noncomputable def globalSum (n : ℕ) [NeZero n] (Q : Polynomial ℤ) : ℤ :=
  ∑ t : ZMod n, jacobiSym ((t.val:ℤ)*(Q.eval (t.val:ℤ))^2) n

/-- A squared mask removes precisely its roots from the complete local
character sum. A root at zero has weight zero. -/
theorem local_eq {r : ℕ} [Fact r.Prime] (op : r≠2) (Q : Polynomial ℤ) :
    localSum r Q = -(∑ t∈rootSet r Q, quadraticChar (ZMod r) t) := by
  let P := Q.map (Int.castRingHom (ZMod r))
  have term (t : ZMod r) : quadraticChar (ZMod r) (t*(P.eval t)^2) =
      quadraticChar (ZMod r) t - (if P.eval t=0 then quadraticChar (ZMod r) t else 0) := by
    by_cases zero : P.eval t=0
    · simp [zero,quadraticChar_zero]
    · rw [map_mul,quadraticChar_sq_one' zero,if_neg zero,mul_one,sub_zero]
  change (∑ t : ZMod r, quadraticChar (ZMod r) (t*(P.eval t)^2)) = _
  simp only [term,sum_sub_distrib,quadraticChar_sum_zero (by rwa [ZMod.ringChar_zmod_n] : ringChar (ZMod r)≠2),
    zero_sub,←sum_filter,rootSet,P]

/-- CRT separates the complete sum, including polynomial evaluations at
nonunits of the composite modulus. -/
theorem factorization {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (Q : Polynomial ℤ) :
    globalSum (p*q) Q = localSum p Q * localSum q Q := by
  let e := ZMod.chineseRemainder ((Nat.coprime_primes hp.out hq.out).mpr diff)
  apply ExtensionTrace.separated e.toEquiv
  intro t
  have coord : e t = (t.val:ℕ) := by rw [←map_natCast e,ZMod.natCast_zmod_val]
  have eval_at (r : ℕ) (a : ℕ) : (Int.castRingHom (ZMod r)) (Q.eval (a:ℤ)) =
      (Q.map (Int.castRingHom (ZMod r))).eval (a:ZMod r) := by
    simpa only [←eval₂_eq_eval_map,Int.coe_castRingHom,Int.cast_natCast] using
      (eval₂_at_apply (p:=Q) (Int.castRingHom (ZMod r)) (a:ℤ)).symm
  simp only [Int.coe_castRingHom] at eval_at
  change jacobiSym _ _ =
    quadraticChar (ZMod p) ((e t).1*((Q.map (Int.castRingHom (ZMod p))).eval (e t).1)^2) *
    quadraticChar (ZMod q) ((e t).2*((Q.map (Int.castRingHom (ZMod q))).eval (e t).2)^2)
  rw [ExtensionTrace.jacobi_crt,coord]
  simp only [Int.cast_mul,Int.cast_pow,Int.cast_natCast,Prod.fst_natCast,Prod.snd_natCast,eval_at]

/-- Polynomial with one linear factor for the square of each public coordinate. -/
noncomputable def squareMask (C : Finset ℕ) : Polynomial ℤ :=
  ∏ x∈C, (X - Polynomial.C ((x:ℤ)^2))

noncomputable abbrev prefixMask (L : ℕ) := squareMask (Icc 1 L)

theorem degree_prefix (L : ℕ) : (prefixMask L).natDegree = L := by
  rw [prefixMask,squareMask,natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C,sum_const,nsmul_eq_mul,mul_one,Nat.cast_id,Nat.card_Icc,Nat.add_sub_cancel]

theorem rootSet_squareMask (r : ℕ) [Fact r.Prime] (C : Finset ℕ) :
    rootSet r (squareMask C) = C.image (fun x : ℕ => (x:ZMod r)^2) := by
  ext t
  simp only [rootSet,mem_filter,mem_univ,true_and,squareMask,Polynomial.map_prod,
    Polynomial.eval_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    eval_sub,eval_X,eval_C,Int.coe_castRingHom,Int.cast_pow,Int.cast_natCast,
    prod_eq_zero_iff,sub_eq_zero,mem_image]
  exact exists_congr fun _ => and_congr_right fun _ => eq_comm

/-- With the square mask every removed nonzero root has local character +1. -/
theorem square_sum (r : ℕ) [Fact r.Prime] (op : r≠2) (C : Finset ℕ) :
    localSum r (squareMask C) = -((covered r C).card:ℤ) := by
  rw [local_eq op,rootSet_squareMask]
  congr 1
  have term (t : ZMod r) (h : t∈C.image (fun x : ℕ => (x:ZMod r)^2)) :
      quadraticChar (ZMod r) t = if t≠0 then (1:ℤ) else 0 := by
    obtain ⟨x,_,rfl⟩ := mem_image.mp h
    split_ifs with nz
    · exact (quadraticChar_one_iff_isSquare nz).mpr (IsSquare.sq _)
    · simp only [ne_eq,not_not] at nz
      rw [nz,quadraticChar_zero]
  calc _ = ∑ t∈C.image (fun x : ℕ => (x:ZMod r)^2), if t≠0 then (1:ℤ) else 0 :=
         sum_congr rfl term
       _ = _ := by simp only [sum_boole,filter_ne',covered]

/-- For any prefix length, the complete sum multiplies the two capped
local half-periods. Each cap counts distinct nonzero square residues. -/
theorem prefix_sum {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (L : ℕ) :
    globalSum (p*q) (prefixMask L) =
      ((min L ((p-1)/2):ℕ):ℤ)*((min L ((q-1)/2):ℕ):ℤ) := by
  rw [factorization diff,prefixMask,square_sum p op,square_sum q oq,prefix_cover op,prefix_cover oq]
  ring

/-- The complete midpoint sum equals half the signed midpoint imbalance. -/
theorem midcut_sum {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) :
    globalSum (p*q) (prefixMask (cutoff (p*q))) = (cutoff (p*q):ℤ)*(((p-1)/2:ℕ):ℤ) := by
  rw [prefix_sum order.ne op oq,min_eq_right (between order).1,min_eq_left (between order).2,mul_comm]

theorem twice_midcut {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) :
    2*globalSum (p*q) (prefixMask (cutoff (p*q))) = imbalance (p*q) := by
  rw [midcut_sum order op oq,imbalance_eq order op oq]
  obtain ⟨k,pk⟩ := hp.out.odd_of_ne_two op
  have half : (p-1)/2=k := by omega
  rw [half]
  have cast : (p:ℤ)=2*k+1 := by exact_mod_cast pk
  rw [cast]
  ring

end PrimeFactors.CircleMarkJacobiMask
