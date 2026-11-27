import PrimeFactors.PrimitiveIntervalMoment
import Mathlib.Algebra.Order.Ring.Pow

/-! Probability that uniform sampling with replacement sees a nonbaseline
entry of the signed interval kernel. Each ordered pair in the box is
equally likely at each draw. -/

namespace PrimeFactors.PrimitiveIntervalSampling

open Finset PrimitiveIntervalMoment PrimitiveCharacterParityMoment
set_option exponentiation.threshold 4096

/-- Pairs at which the signed kernel differs from its ordinary value one. -/
noncomputable def hits (p q B : ℕ) : Finset (ℕ×ℕ) := by
  classical exact (box B).filter fun w => kernel p q true w.1 w.2≠1

private theorem hits_subset (p q B : ℕ) : hits p q B ⊆ box B := filter_subset ..

theorem box_card (B : ℕ) : (box B).card=B^2 := by simp [box,pow_two]

/-- The only exceptional diagonals are exactly the two prime sums that occur in the box. -/
theorem hit_layers {p q B : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q) (below : B<p) :
    hits p q B = layer B p ∪ layer B q := by
  classical
  have pn : ((p-1:ℕ):ℂ)≠0 := by exact_mod_cast Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt
  have qn : ((q-1:ℕ):ℂ)≠0 := by exact_mod_cast Nat.sub_ne_zero_of_lt (Fact.out : q.Prime).one_lt
  ext w
  simp only [hits,layer,mem_filter,mem_union]
  by_cases inside : w∈box B
  · simp only [inside,true_and]
    rw [kernel_layers order below w inside]
    by_cases left : w.1+w.2=p
    · have right : w.1+w.2≠q := by omega
      simp [left,right,order.ne,pn]
    · by_cases right : w.1+w.2=q
      · simp [left,right,order.ne',qn]
      · simp [left,right]
  · simp [inside]

/-- Exact one-draw numerator. Natural subtraction also covers an empty upper layer. -/
theorem hit_count {p q B : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q) (below : B<p) :
    (hits p q B).card=(2*B+1-p)+(2*B+1-q) := by
  have disjoint : Disjoint (layer B p) (layer B q) := by
    apply disjoint_left.mpr
    intro w hp hq
    exact order.ne ((mem_filter.mp hp).2.symm.trans (mem_filter.mp hq).2)
  rw [hit_layers order below,card_union_of_disjoint disjoint,layer_count below,layer_count (below.trans order)]

theorem hit_count_le {p q B : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q) (below : B<p) :
    (hits p q B).card≤2*B := by rw [hit_count order below]; omega

/-- The fraction of the box carrying nonbaseline entries. -/
noncomputable def single (p q B : ℕ) : ℝ := ((hits p q B).card : ℝ)/(box B).card

/-- Complement of the fraction of length-t ordered samples lying entirely in
the non-hit subset. The denominator counts all functions from Fin t to the box. -/
noncomputable def anyHit (p q B t : ℕ) : ℝ :=
  1 - (Fintype.card (Fin t → ↥(box B \ hits p q B)) : ℝ)/Fintype.card (Fin t → ↥(box B))

private theorem box_positive {B : ℕ} (bp : 0<B) : 0<((box B).card : ℝ) := by
  rw [box_card]; positivity

theorem one_draw {p q B : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q) (below : B<p)
    (bp : 0<B) : single p q B≤2/B := by
  have H := hit_count_le order below
  have bound : ((hits p q B).card:ℝ)≤2*B := by exact_mod_cast H
  rw [single,box_card,Nat.cast_pow]
  calc
    _ ≤ (2*B)/(B:ℝ)^2 := div_le_div_of_nonneg_right bound (by positivity)
    _ = _ := by field_simp; ring

/-- Counting all independent draws with replacement gives the exact power of
the one-draw miss fraction. This also covers t=0. -/
theorem exact_any {p q B : ℕ} (bp : 0<B) (t : ℕ) :
    anyHit p q B t=1-(1-single p q B)^t := by
  have pos := box_positive bp
  have sub := hits_subset p q B
  simp only [anyHit,Fintype.card_fun,Fintype.card_coe,Fintype.card_fin,Nat.cast_pow,
    card_sdiff sub,Nat.cast_sub (card_le_card sub),←div_pow,sub_div,div_self pos.ne',single]

/-- The union bound for uniform independent pairs. -/
theorem sampling_bound {p q B : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q) (below : B<p)
    (bp : 0<B) (t : ℕ) : anyHit p q B t≤2*t/B := by
  let x := single p q B
  have pos := box_positive bp
  have atMost : x≤1 := (div_le_one pos).mpr (by exact_mod_cast card_le_card (hits_subset p q B))
  have bern := one_add_mul_le_pow (a := -x) (by linarith) t
  have tail : 1-(1-x)^t≤t*x := by
    rw [←sub_eq_add_neg,mul_neg] at bern
    linarith
  rw [exact_any bp]
  calc
    _ ≤ (t:ℝ)*x := tail
    _ ≤ t*(2/B) := mul_le_mul_of_nonneg_left (one_draw order below bp) (by positivity)
    _ = _ := by ring

/-- With at most 2^64 such samples at the 2048-bit cutoff, the probability
of seeing any exceptional entry is at most 2^-958. -/
theorem full_width {p q t : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q) (balanced : q<2*p)
    (full : 2^2047≤p*q) (budget : t≤2^64) :
    anyHit p q (cutoff (p*q)) t≤1/(2:ℝ)^958 := by
  have wide := full_width_cutoff full
  have bp : 0<cutoff (p*q) := lt_of_lt_of_le (by decide +kernel : 0<2^1023) wide
  have B : (2:ℝ)^1023≤cutoff (p*q) := by exact_mod_cast wide
  have T : (t:ℝ)≤2^64 := by exact_mod_cast budget
  apply (sampling_bound order (cutoff_bounds (Fact.out : p.Prime).pos balanced).1 bp t).trans
  apply (div_le_div_iff₀ (by exact_mod_cast bp : (0:ℝ)<cutoff (p*q)) (by positivity)).mpr
  calc
    _ ≤ 2*(2:ℝ)^64*2^958 := by gcongr
    _ = (2:ℝ)^1023 := by ring
    _ ≤ _ := by simpa using B

/-- Ten of the 64 ordered pairs at 143 hit an exceptional diagonal.
Two independent samples have hit probability 295/1024. -/
theorem control_143 : (hits 11 13 8).card=10 ∧ single 11 13 8=5/32 ∧
    anyHit 11 13 8 2=295/1024 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have num : (hits 11 13 8).card=10 := (hit_count (by decide : 11<13) (by decide : 8<11)).trans rfl
  have frac : single 11 13 8=5/32 := by rw [single,num,box_card]; norm_num
  exact ⟨num,frac,by rw [exact_any (by decide),frac]; norm_num⟩

end PrimeFactors.PrimitiveIntervalSampling
