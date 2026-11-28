import PrimeFactors.CircleMarkJacobiMask
import PrimeFactors.NormBatchGCD
import Mathlib.Data.Nat.Factorial.BigOperators

/-! At the first square past the prefix, the mask becomes a product of ordinary
integers. Its gcd is accounted for by one trial divisor in a public interval. -/
namespace PrimeFactors.CircleMarkJacobiMaskEdge

open Finset Polynomial CircleMarkMidcutReadout CircleMarkJacobiMask

/-- Positive difference of the edge square and the i-th prefix square,
written as a product of its two linear factors for 1 ≤ i ≤ K. -/
def leaf (K i : ℕ) : ℕ := (K+1-i)*(K+1+i)

noncomputable def edgeValue (K : ℕ) : ℕ := ∏ i∈Icc 1 K, leaf K i

theorem edge_eval (K : ℕ) :
    (prefixMask K).eval (((K:ℤ)+1)^2) = (edgeValue K:ℤ) := by
  rw [prefixMask,squareMask,eval_prod,edgeValue,Nat.cast_prod]
  apply prod_congr rfl
  intro i mi
  have le := (mem_Icc.mp mi).2
  simp only [eval_sub,eval_X,eval_C,leaf,Nat.cast_mul,Nat.cast_sub (by omega : i≤K+1),
    Nat.cast_add,Nat.cast_one]
  ring

/-- The same value is the factorial through 2K+1 with K+1 removed. -/
theorem factorial_form (K : ℕ) : edgeValue K = (2*K+1).factorial/(K+1) := by
  have lower : (∏ i∈Icc 1 K, (K+1-i)) = K.factorial := by
    calc _ = ∏ i∈Icc 1 K, i := by
           apply prod_bij (fun i _ => K+1-i)
           · intro i hi; have := mem_Icc.mp hi; apply mem_Icc.mpr; omega
           · intro i hi j hj eq; have := mem_Icc.mp hi; have := mem_Icc.mp hj; omega
           · intro i hi; have := mem_Icc.mp hi
             exact ⟨K+1-i,mem_Icc.mpr (by omega),by omega⟩
           · intros; rfl
         _ = _ := by simpa only [Nat.Ico_succ_right] using prod_Ico_id_eq_factorial K
  have upper : (∏ i∈Icc 1 K, (K+1+i)) = (K+2).ascFactorial K := by
    rw [Nat.ascFactorial_eq_prod_range]
    apply prod_bij (fun i _ => i-1)
    · intro i hi; have := mem_Icc.mp hi; apply mem_range.mpr; omega
    · intro i hi j hj eq; have := mem_Icc.mp hi; have := mem_Icc.mp hj; omega
    · intro i hi; have := mem_range.mp hi
      exact ⟨i+1,mem_Icc.mpr (by omega),by omega⟩
    · intro i hi; have := mem_Icc.mp hi; omega
  have full : (K+1)*edgeValue K = (2*K+1).factorial := by
    simp only [edgeValue,leaf,prod_mul_distrib]
    rw [lower,upper,←Nat.mul_assoc,←Nat.factorial_succ,
      Nat.factorial_mul_ascFactorial, show K+1+K=2*K+1 by omega]
  exact Nat.eq_div_of_mul_eq_right (Nat.succ_ne_zero _) full

/-- The plus-factor interval K+2 through 2K+1 includes p and excludes q. -/
theorem bounds {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2) :
    cutoff (p*q)+1 < p ∧ p ≤ 2*cutoff (p*q)+1 ∧ 2*cutoff (p*q)+1 < q := by
  have rp : p ≤ (p*q).sqrt := Nat.le_sqrt.mpr (Nat.mul_le_mul_left p order.le)
  have rq : (p*q).sqrt < q-1 := by
    apply Nat.sqrt_lt'.mpr
    obtain ⟨a,pa⟩ := hp.out.odd_of_ne_two op
    obtain ⟨b,qb⟩ := hq.out.odd_of_ne_two oq
    have cap := Nat.mul_le_mul_right q (show p+2≤q by omega)
    rw [qb] at cap ⊢
    rw [show 2*b+1-1=2*b by omega]
    nlinarith only [cap]
  unfold cutoff
  omega

/-- At every index the smaller prime divides a leaf exactly when its upper
linear factor equals p. The larger prime divides neither linear factor. -/
theorem leaf_factors {p q i : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2)
    (inside : i∈Icc 1 (cutoff (p*q))) :
    (p∣leaf (cutoff (p*q)) i ↔ cutoff (p*q)+1+i=p) ∧ ¬q∣leaf (cutoff (p*q)) i := by
  let K := cutoff (p*q)
  change (p∣leaf K i ↔ K+1+i=p) ∧ ¬q∣leaf K i
  obtain ⟨ks,_,large⟩ := bounds order bal op oq
  change K+1<p at ks
  change 2*K+1<q at large
  obtain ⟨lo,hi⟩ := mem_Icc.mp inside
  change i≤K at hi
  have mp : 0<K+1-i := by omega
  have left := Nat.not_dvd_of_pos_of_lt mp (show K+1-i<p by omega)
  rw [leaf,hp.out.dvd_mul,hq.out.dvd_mul,or_iff_right left]
  refine ⟨⟨fun dv => Nat.eq_of_dvd_of_lt_two_mul (by omega) dv (by omega),fun eq => eq ▸ dvd_refl _⟩,?_⟩
  exact fun h => h.elim (Nat.not_dvd_of_pos_of_lt mp (by omega))
    (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))

/-- The direct non-coprimality test on a leaf agrees with trial division of
the input by its upper linear factor. -/
theorem scan_iff {p q i : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2)
    (inside : i∈Icc 1 (cutoff (p*q))) :
    (¬(p*q).Coprime (leaf (cutoff (p*q)) i)) ↔ cutoff (p*q)+1+i ∣ p*q := by
  let K := cutoff (p*q)
  obtain ⟨pos,cap⟩ := mem_Icc.mp inside
  change i≤K at cap
  obtain ⟨_,_,large⟩ := bounds order bal op oq
  change 2*K+1<q at large
  have cancel : (K+1+i).Coprime q :=
    (hq.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
  obtain ⟨atP,atQ⟩ := leaf_factors order bal op oq inside
  change (¬(p*q).Coprime (leaf K i)) ↔ K+1+i ∣ p*q
  rw [Nat.coprime_mul_iff_left,hp.out.coprime_iff_not_dvd,hq.out.coprime_iff_not_dvd,
    and_iff_left atQ,not_not,atP,cancel.dvd_mul_right,Nat.dvd_prime hp.out]
  omega

/-- Exactly one of the K leaves is divisible by p; the index is p−K−1. -/
theorem unique_index {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2) :
    (Icc 1 (cutoff (p*q))).filter (fun i => p∣leaf (cutoff (p*q)) i) =
      {p-cutoff (p*q)-1} := by
  let K := cutoff (p*q)
  obtain ⟨ks,pk,_⟩ := bounds order bal op oq
  change K+1<p at ks
  change p≤2*K+1 at pk
  ext i
  rw [mem_filter,mem_singleton]
  constructor
  · rintro ⟨inside,h⟩
    have eq := (leaf_factors order bal op oq inside).1.mp h
    change K+1+i=p at eq
    change i=p-K-1
    omega
  · intro eq
    change i=p-K-1 at eq
    have inside : i∈Icc 1 K := mem_Icc.mpr (by omega)
    exact ⟨inside,(leaf_factors order bal op oq inside).1.mpr (show K+1+i=p by omega)⟩

/-- One gcd of the polynomial value gives p. A direct leaf scan tests the
same candidates as divisibility by the consecutive integers K+2,…,2K+1. -/
theorem edge_gcd {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2) :
    (p*q).gcd ((prefixMask (cutoff (p*q))).eval (((cutoff (p*q):ℤ)+1)^2)).natAbs = p := by
  let K := cutoff (p*q)
  rw [edge_eval,Int.natAbs_natCast,Nat.gcd_comm]
  apply NormBatchGCD.one_batch hq.out
  · apply (hp.out.prime.dvd_finset_prod_iff _).mpr
    have exactSet := unique_index order bal op oq
    have witness : p-K-1 ∈ (Icc 1 K).filter (fun i => p∣leaf K i) := by
      rw [exactSet]
      exact mem_singleton_self _
    exact ⟨_,(mem_filter.mp witness).1,(mem_filter.mp witness).2⟩
  · intro dv
    obtain ⟨i,hi,hit⟩ := (hq.out.prime.dvd_finset_prod_iff _).mp dv
    exact (leaf_factors order bal op oq hi).2 hit

end PrimeFactors.CircleMarkJacobiMaskEdge
