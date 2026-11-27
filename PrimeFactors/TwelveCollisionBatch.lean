import PrimeFactors.TwelveResidueCollision
import Mathlib.Algebra.Polynomial.Derivative

namespace PrimeFactors.TwelveCollisionBatch
open Finset Polynomial TwelveResidueCollision
open scoped Polynomial

/-- For independently sampled CRT coordinates, a proper collision has exactly
one matching coordinate. The two rectangles in this union are disjoint. -/
private def separating {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P H : Finset α) (Q K : Finset β) := (H ×ˢ (Q\K)) ∪ ((P\H) ×ˢ K)

private theorem separating_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    {P H : Finset α} {Q K : Finset β} (hp : H⊆P) (hq : K⊆Q) :
    (separating P H Q K).card = H.card*(Q.card-K.card)+(P.card-H.card)*K.card := by
  have dis : Disjoint (H ×ˢ (Q\K)) ((P\H) ×ˢ K) := by
    apply disjoint_left.mpr
    intro z h k
    exact (mem_sdiff.mp (mem_product.mp k).1).2 (mem_product.mp h).1
  rw [separating,card_union_of_disjoint dis,card_product,card_product,card_sdiff hp,
    card_sdiff hq]

/-- Number of matching partners for a fixed regular seed modulo pq,
represented by its two coordinates under the Chinese remainder theorem. -/
theorem exact_counts {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (largeP : 864<p) (largeQ : 864<q)
    {x : ZMod p} {y : ZMod q} (hx : x∈regulars p) (hy : y∈regulars q) :
    let P := regulars p
    let Q := regulars q
    let H := P.filter (fun t => num x*den t=num t*den x)
    let K := Q.filter (fun t => num y*den t=num t*den y)
    (H ×ˢ (Q\K) ∪ ((P\H) ×ˢ K)).card = 12*(Q.card-12)+(P.card-12)*12 ∧
    (({x} : Finset _) ×ˢ (Q\{y}) ∪ ((P\{x}) ×ˢ {y})).card = (Q.card-1)+(P.card-1) := by
  intro P Q H K
  constructor
  · change (separating P H Q K).card=_
    rw [separating_card (filter_subset _ _) (filter_subset _ _),regular_fiber largeP hx,regular_fiber largeQ hy]
  · change (separating P {x} Q {y}).card=_
    rw [separating_card (singleton_subset_iff.mpr hx) (singleton_subset_iff.mpr hy)]
    simp [P,Q]

/-- At a fixed count of regular partners, the success fraction per pair
increases by more than a factor of eleven throughout this range. -/
theorem more_than_eleven {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : 864<p) (hq : 864<q) :
    11*(((regulars q).card-1)+((regulars p).card-1)) <
      12*((regulars q).card-12)+((regulars p).card-12)*12 := by
  have a := regular_count p
  have b := regular_count q
  omega

/-- Any pair distinguished by raw equality alone either has different
folded keys at the other prime or is recovered by checking the identity
branch of the shared key. The other orientation follows by exchanging fields. -/
theorem preserves_identity_match {K L : Type*} [Field K] [Field L]
    {x y : K} {u v : L} (same : x=y) (apart : u≠v) :
    num x*den y=num y*den x ∧
      (num u*den v≠num v*den u ∨
        (num u*den v=num v*den u ∧ ∃ i : Fin 12,
          imageDen x i*y-imageNum x i=0 ∧ imageDen u i*v-imageNum u i≠0)) := by
  subst y
  refine ⟨rfl, ?_⟩
  by_cases h : num u*den v=num v*den u
  · exact Or.inr ⟨h, 0, by simp [identity_branch], by simpa [identity_branch,sub_ne_zero] using apart.symm⟩
  · exact Or.inl h

/-- A local match at p alone gives exactly p as the gcd. -/
theorem gcd_of_one_match {p q z : ℕ} (qp : q.Prime) (atP : p∣z) (atQ : ¬ q∣z) :
    Nat.gcd (p*q) z=p := by
  rw [mul_comm, Nat.Coprime.gcd_mul_left_cancel _ (qp.coprime_iff_not_dvd.mpr atQ)]
  exact Nat.gcd_eq_left atP

/-- One derivative evaluation contains all the comparisons incident to its
key. This works over the composite residue ring as well as over a field. -/
theorem derivative_at_key {R : Type*} [CommRing R] [DecidableEq R] {s : Finset R}
    {x : R} (hx : x∈s) :
    (derivative (∏ t∈s, (X-C t))).eval x = ∏ t∈s.erase x, (x-t) := by
  rw [←mul_prod_erase s (fun t => (X-C t)) hx,derivative_mul]
  simp [Polynomial.eval_prod]

end PrimeFactors.TwelveCollisionBatch
