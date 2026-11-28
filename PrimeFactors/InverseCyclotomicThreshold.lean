import PrimeFactors.BalancedCyclotomicPrefix
import PrimeFactors.ConvexIntegerReadout

/-! Inverse cyclotomic coefficients and their threshold at the smaller
prime. The classical binary identity appears in Pieter Moree, *Inverse
cyclotomic polynomials* (2009), in the proof of Theorem 1.
[Author's preprint](https://arxiv.org/pdf/0709.1570#page=6)

The comparison count treats each requested coefficient as a supplied value. -/

namespace PrimeFactors.InverseCyclotomicThreshold

open Polynomial Finset
open scoped Polynomial

noncomputable def inversePoly (N : ℕ) : ℤ[X] := (X^N-1) /ₘ cyclotomic N ℤ

/-- For two distinct primes the inverse cyclotomic polynomial consists of
two translated geometric sums. -/
theorem binary_inverse {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q) :
    inversePoly (p*q)=(X^q-1)*(∑ i∈range p,X^i) := by
  have geo : (∑ i∈range p,(X:ℤ[X])^i)*(X-1)=X^p-1 := geom_sum_mul ..
  have nonzero : (X-1 : ℤ[X])≠0 := by
    intro h
    have eq := congrArg (fun f : ℤ[X] => f.coeff 0) h
    simp at eq
  have product : cyclotomic (p*q) ℤ*((X^q-1)*(∑ i∈range p,X^i))=X^(p*q)-1 := by
    apply mul_right_cancel₀ nonzero
    calc
      _ = cyclotomic (p*q) ℤ*(X^p-1)*(X^q-1) := by rw [←geo]; ring
      _ = cyclotomic (p*q) ℤ*(1-X^p)*(1-X^q) := by ring
      _ = _ := (BalancedCyclotomicPrefix.product_identity hp hq ord).trans (by ring)
  rw [inversePoly,←product,mul_divByMonic_cancel_left _ (cyclotomic.monic ..)]

private theorem geometric_coeff (p k : ℕ) :
    (∑ i∈range p,(X : ℤ[X])^i).coeff k=if k<p then 1 else 0 := by
  simp [finset_sum_coeff,coeff_X_pow]

/-- The negative block is [0,p), the positive block is [q,p+q), and the
coefficient vanishes everywhere else. -/
theorem coefficient {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q) (k : ℕ) :
    (inversePoly (p*q)).coeff k=if k<p then -1 else if q≤k ∧ k<p+q then 1 else 0 := by
  rw [binary_inverse hp hq ord,sub_mul,one_mul,coeff_sub,coeff_X_pow_mul',
    geometric_coeff,geometric_coeff]
  split_ifs <;> omega

/-- A nonnegative coefficient is equivalent to having reached p, at every index. -/
theorem nonnegative_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q) (k : ℕ) :
    0≤(inversePoly (p*q)).coeff k ↔ p≤k := by
  rw [coefficient hp hq ord]
  split_ifs <;> omega

theorem before_larger {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q) (early : k<q) :
    (inversePoly (p*q)).coeff k=if k<p then -1 else 0 := by
  simp only [coefficient hp hq ord,if_neg (show ¬(q≤k ∧ k<p+q) by omega)]

noncomputable def bisect (N fuel lo width : ℕ) : ℕ×ℕ :=
  ConvexIntegerReadout.boundary (fun k => 0≤(inversePoly N).coeff k) fuel lo width

/-- A supplied coefficient sign at each midpoint yields p within the indicated
comparison budget. The closed interval includes its upper sentinel. -/
theorem bisect_spec {p q fuel lo width : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (left : lo≤p) (right : p≤lo+width) (budget : width<2^fuel) :
    (bisect (p*q) fuel lo width).1=p ∧ (bisect (p*q) fuel lo width).2≤fuel := by
  let P := fun k => 0≤(inversePoly (p*q)).coeff k
  let cut := (ConvexIntegerReadout.boundary P fuel lo width).1
  have rule (k : ℕ) : P k ↔ p≤k := nonnegative_iff hp hq ord k
  obtain ⟨⟨cutlo,cuthi,before,after⟩,cost⟩ := ConvexIntegerReadout.boundary_spec P
    fuel lo width budget (fun i j _ ij _ hi => (rule j).mpr (((rule i).mp hi).trans ij))
  change lo≤cut at cutlo
  change cut≤lo+width at cuthi
  change (∀ i : ℕ, lo ≤ i → i < cut → ¬ P i) at before
  change (∀ i : ℕ, cut ≤ i → i < lo+width → P i) at after
  change cut=p ∧ _
  refine ⟨le_antisymm ?_ ?_,cost⟩
  · by_contra! h
    exact before p left h ((rule p).mpr le_rfl)
  · by_contra! h
    exact (not_le.mpr h) ((rule cut).mp (after cut le_rfl (h.trans_le right)))

/-- For a known 1024-bit factor width at most 1023 supplied signs suffice. -/
theorem full_width {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (lo : 2^1023≤p) (hi : p<2^1024) :
    (bisect (p*q) 1023 (2^1023) (2^1023-1)).1=p ∧
    (bisect (p*q) 1023 (2^1023) (2^1023-1)).2≤1023 := by
  apply bisect_spec hp hq ord lo
  · omega
  · decide +kernel

end PrimeFactors.InverseCyclotomicThreshold
