import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Sharp success probability for a decreasing distribution on positive gcd probes. -/

namespace PrimeFactors.MonotoneDivisorSampling

open Finset

/-- Index zero is the probe 1. A proper gcd splits the public product. -/
def split (n i : ℕ) : ℝ :=
  if ¬n.Coprime (i+1) ∧ ¬n ∣ i+1 then 1 else 0

private def mark (d i : ℕ) : ℝ := if d ∣ i+1 then 1 else 0

private theorem mark_sum (d m : ℕ) :
    ∑ i ∈ range m, mark d i = (m/d : ℕ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    by_cases h : d ∣ m+1
    · simp [mark, h, Nat.succ_div_of_dvd h]
    · simp [mark, h, Nat.succ_div_of_not_dvd h]

private theorem split_mark {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q) (i : ℕ) :
    split (p*q) i = mark p i + mark q i - 2 * mark (p*q) i := by
  have co := (Nat.coprime_primes pp qp).mpr ne
  have both : p*q ∣ i+1 ↔ p ∣ i+1 ∧ q ∣ i+1 := by
    exact ⟨fun h => ⟨(dvd_mul_right p q).trans h,(dvd_mul_left q p).trans h⟩,
      fun h => co.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  by_cases a : p ∣ i+1 <;> by_cases b : q ∣ i+1 <;> norm_num [split,mark,Nat.coprime_mul_iff_left,pp.coprime_iff_not_dvd,qp.coprime_iff_not_dvd,both,a,b]

/-- Exact count on the first m positive integers, including complete periods. -/
theorem split_prefix {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q) (m : ℕ) :
    ∑ i ∈ range m, split (p*q) i =
      (m/p : ℕ) + (m/q : ℕ) - 2 * (m/(p*q) : ℕ) := by
  simp_rw [split_mark pp qp ne]
  rw [sum_sub_distrib,sum_add_distrib,←mul_sum,mark_sum,mark_sum,mark_sum]

/-- A finite sum with decreasing weights is controlled by *all* its prefix means. -/
theorem weighted_of_prefix (a w : ℕ → ℝ) (s : ℝ) (M : ℕ) (decr : Antitone w)
    (nonneg : ∀ i, 0 ≤ w i) (bound : ∀ m ≤ M, ∑ i ∈ range m, a i ≤ m*s) :
    ∑ i ∈ range M, w i*a i ≤ (∑ i ∈ range M, w i)*s := by
  let excess (m : ℕ) := ∑ i ∈ range m, a i - m*s
  have neg (m : ℕ) (le : m≤M) : excess m ≤ 0 := sub_nonpos.mpr (bound m le)
  have major (m : ℕ) (le : m≤M) :
      ∑ i ∈ range m, w i*a i - (∑ i ∈ range m, w i)*s ≤ w m*excess m := by
    induction m with
    | zero => simp [excess]
    | succ m ih =>
      have prev := ih (by omega)
      have shrink := mul_le_mul_of_nonpos_right (decr (Nat.le_succ m)) (neg (m+1) le)
      have step : excess (m+1) = excess m + a m - s := by
        simp only [excess,sum_range_succ,Nat.cast_add,Nat.cast_one]
        ring
      rw [step] at shrink
      rw [sum_range_succ,sum_range_succ,step]
      linarith only [prev,shrink]
  have final := major M le_rfl
  linarith [mul_nonpos_of_nonneg_of_nonpos (nonneg M) (neg M le_rfl)]

/-- Density of the best prefix, expressed using the larger modular inverse. -/
noncomputable def best (p q k : ℕ) : ℝ := ((p:ℝ)+(q:ℝ)-1/(k:ℝ))/((p:ℝ)*q)

private theorem residue_bound {p q u v : ℕ} (co : p.Coprime q)
    (up : p*u ≡ 1 [MOD q]) (vq : q*v ≡ 1 [MOD p]) (m : ℕ) :
    m % (p*q) ≤ max u v * (q*(m%p) + p*(m%q)) := by
  let t := q*v*(m%p)+p*u*(m%q)
  have modp : t ≡ m [MOD p] := by
    have free := vq.mul (Nat.mod_modEq m p)
    have zero : p*u*(m%q) ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (dvd_mul_right p u) _)
    simpa [t] using free.add zero
  have modq : t ≡ m [MOD q] := by
    have free := up.mul (Nat.mod_modEq m q)
    have zero : q*v*(m%p) ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (dvd_mul_right q v) _)
    simpa [t] using zero.add free
  have g := (Nat.modEq_and_modEq_iff_modEq_mul co).mp ⟨modp,modq⟩
  calc
    m % (p*q) = t % (p*q) := g.symm
    _ ≤ t := Nat.mod_le ..
    _ ≤ max u v * (q*(m%p) + p*(m%q)) := by
      dsimp [t]
      have a := Nat.mul_le_mul_left (q*(m%p)) (le_max_right u v)
      have b := Nat.mul_le_mul_left (p*(m%q)) (le_max_left u v)
      nlinarith only [a,b]

private theorem defect (p q m : ℕ) :
    ((p:ℝ)+q)*m - ((p:ℝ)*q)*((m/p:ℕ)+(m/q:ℕ)-2*(m/(p*q):ℕ) : ℝ) =
      (q:ℝ)*(m%p:ℕ)+(p:ℝ)*(m%q:ℕ)+2*((p:ℝ)*q)*(m/(p*q):ℕ) := by
  have a : (m%p:ℕ) + (p:ℝ)*(m/p:ℕ) = m := by exact_mod_cast Nat.mod_add_div m p
  have b : (m%q:ℕ) + (q:ℝ)*(m/q:ℕ) = m := by exact_mod_cast Nat.mod_add_div m q
  linear_combination -(q:ℝ)*a - (p:ℝ)*b

theorem prefix_bound {p q u v : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (up : p*u ≡ 1 [MOD q]) (vq : q*v ≡ 1 [MOD p]) (uk : 0<u) (m : ℕ) :
    ∑ i ∈ range m, split (p*q) i ≤ m*best p q (max u v) := by
  let k := max u v
  have hk : 0<k := lt_of_lt_of_le uk (le_max_left ..)
  have part := residue_bound ((Nat.coprime_primes pp qp).mpr ne) up vq m
  have whole : m ≤ k*(q*(m%p)+p*(m%q)+2*(p*q)*(m/(p*q))) := by
    have times := Nat.mul_le_mul_right ((p*q)*(m/(p*q))) (show 1≤2*k by omega)
    dsimp [k] at *
    nlinarith only [part,times,Nat.mod_add_div m (p*q)]
  have realWhole : (m:ℝ) ≤ (k:ℝ)*((q:ℝ)*(m%p:ℕ)+(p:ℝ)*(m%q:ℕ)+2*((p:ℝ)*q)*(m/(p*q):ℕ)) := by
    exact_mod_cast whole
  rw [←defect] at realWhole
  rw [split_prefix pp qp ne]
  change _ ≤ (m:ℝ)*(((p:ℝ)+q-1/(k:ℝ))/((p:ℝ)*q))
  have pd : (0:ℝ)<p := by exact_mod_cast pp.pos
  have qd : (0:ℝ)<q := by exact_mod_cast qp.pos
  have kd : (0:ℝ)<k := by exact_mod_cast hk
  calc
    _ ≤ (m*((p+q)*(k:ℝ)-1))/((k:ℝ)*(p*q)) := by
      apply (le_div_iff₀ (mul_pos kd (mul_pos pd qd))).mpr
      nlinarith only [realWhole]
    _ = _ := by field_simp

/-- At this endpoint the prime-weighted CRT remainder is exactly p. -/
private theorem attains_at {p q u : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (up : p*u ≡ 1 [MOD q]) (pos : 0<u) (small : u<q) :
    ∑ i ∈ range (p*u), split (p*q) i = (p*u : ℕ)*best p q u := by
  have rem : (p*u)%q=1 := (show (p*u)%q=1%q from up).trans (Nat.mod_eq_of_lt qp.one_lt)
  have small' := Nat.mul_lt_mul_of_pos_left small pp.pos
  have eqn := defect p q (p*u)
  simp only [Nat.mul_mod_right,rem,Nat.div_eq_of_lt small',Nat.cast_zero,Nat.cast_one,
    mul_zero,mul_one,zero_add,add_zero,sub_zero] at eqn
  rw [split_prefix pp qp ne,Nat.div_eq_of_lt small']
  simp only [Nat.cast_zero,mul_zero,sub_zero]
  unfold best
  have pd : (0:ℝ)<p := by exact_mod_cast pp.pos
  have qd : (0:ℝ)<q := by exact_mod_cast qp.pos
  have ud : (0:ℝ)<u := by exact_mod_cast pos
  rw [← mul_div_assoc,eq_div_iff (mul_pos pd qd).ne']
  rw [Nat.cast_mul] at *
  field_simp at ⊢
  nlinarith only [congrArg (fun x : ℝ => x*u) eqn]

private theorem inverse_exists {p q : ℕ} (co : p.Coprime q) (large : 1<q) :
    ∃ u : ℕ, 0<u ∧ u<q ∧ p*u ≡ 1 [MOD q] := by
  letI : NeZero q := ⟨by omega⟩
  let u := ((p : ZMod q)⁻¹).val
  have inv : p*u ≡ 1 [MOD q] := by
    apply (ZMod.eq_iff_modEq_nat ..).mp
    simpa only [Nat.cast_mul,Nat.cast_one] using ZMod.mul_val_inv co
  have pos : 0<u := by
    by_contra! h
    have e : u=0 := by omega
    simp [e,Nat.ModEq,Nat.mod_eq_of_lt large] at inv
  exact ⟨u,pos,ZMod.val_lt _,inv⟩

/-- The stated maximum holds over every finite decreasing distribution of positive
probes. A uniform prefix attains it at an endpoint sharing exactly one prime. -/
theorem optimum {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q) :
    ∃ u v M : ℕ, p*u ≡ 1 [MOD q] ∧ q*v ≡ 1 [MOD p] ∧
      u<q ∧ v<p ∧ 0<M ∧ M<p*q ∧ ¬(p*q).Coprime M ∧
      (∑ i ∈ range M, split (p*q) i) = M*best p q (max u v) ∧
      ∀ (w : ℕ → ℝ) (L : ℕ), Antitone w → (∀ i, 0≤w i) →
        ∑ i ∈ range L, w i*split (p*q) i ≤ (∑ i ∈ range L, w i)*best p q (max u v) := by
  have co := (Nat.coprime_primes pp qp).mpr ne
  obtain ⟨u,upos,usmall,up⟩ := inverse_exists co qp.one_lt
  obtain ⟨v,vpos,vsmall,vq⟩ := inverse_exists co.symm pp.one_lt
  have allWeights (w : ℕ → ℝ) (L : ℕ) (hw : Antitone w) (hn : ∀ i, 0≤w i) :=
    weighted_of_prefix (split (p*q)) w (best p q (max u v)) L hw hn
      (fun m _ => prefix_bound pp qp ne up vq upos m)
  by_cases h : v≤u
  · refine ⟨u,v,p*u,up,vq,usmall,vsmall,Nat.mul_pos pp.pos upos,
      Nat.mul_lt_mul_of_pos_left usmall pp.pos,?_,?_,allWeights⟩
    · simp [Nat.coprime_mul_iff_left, pp.coprime_iff_not_dvd]
    · simpa only [max_eq_left h] using attains_at pp qp ne up upos usmall
  · refine ⟨u,v,q*v,up,vq,usmall,vsmall,Nat.mul_pos qp.pos vpos,?_,?_,?_,allWeights⟩
    · simpa [Nat.mul_comm p q] using Nat.mul_lt_mul_of_pos_left vsmall qp.pos
    · simp [Nat.coprime_mul_iff_left, qp.coprime_iff_not_dvd]
    · simpa only [max_eq_right (by omega : u≤v),Nat.mul_comm q p,best,
        add_comm (q:ℝ) p,mul_comm (q:ℝ) p] using attains_at qp pp ne.symm vq vpos vsmall

/-- The same sharp rate bounds normalized distributions with infinite support.
Taking more terms of a convergent Dirichlet sampling weight preserves the bound. -/
theorem infinite_weighted {n : ℕ} {w : ℕ → ℝ} {rate : ℝ}
    (decr : Antitone w) (nonneg : ∀ i, 0≤w i) (law : HasSum w 1)
    (prefixCap : ∀ m, ∑ i ∈ range m, split n i ≤ m*rate) :
    ∑' i, w i*split n i ≤ rate := by
  have bounds (i : ℕ) : 0≤w i*split n i ∧ w i*split n i≤w i := by
    unfold split
    split <;> simp [nonneg i]
  have conv := Summable.of_nonneg_of_le (fun i => (bounds i).1) (fun i => (bounds i).2) law.summable
  have a := conv.hasSum.tendsto_sum_nat
  have b := law.tendsto_sum_nat.mul_const rate
  simpa using le_of_tendsto_of_tendsto' a b (fun M =>
    weighted_of_prefix (split n) w rate M decr nonneg (fun m _ => prefixCap m))

/-- Every positive-density maximizing cutoff itself has a proper gcd with N.
This uses the public prefix statistic and requires no modular inverses. -/
theorem maximum_splits {n m : ℕ} {rate : ℝ} (pos : 0<rate)
    (bound : ∑ i ∈ range m, split n i ≤ m*rate)
    (attains : ∑ i ∈ range (m+1), split n i = ((m:ℝ)+1)*rate) :
    ¬n.Coprime (m+1) ∧ ¬n ∣ m+1 := by
  by_contra no
  rw [sum_range_succ,split,if_neg no] at attains
  linarith

/-- The optimum, scaled by the product and shifted by a half, determines
the prime sum up to rounding to an even integer when both primes are odd. -/
theorem sum_from_rate {p q k : ℕ} (hp : 0<p) (hq : 0<q) (hk : 0<k) {A : ℝ}
    (accurate : |A-((p:ℝ)*q)*best p q k|<1/2) :
    |(A+1/2)-((p:ℝ)+q)|<1 := by
  have ppos : (0:ℝ)<p := by exact_mod_cast hp
  have qpos : (0:ℝ)<q := by exact_mod_cast hq
  have kpos : (0:ℝ)<k := by exact_mod_cast hk
  have one : (1:ℝ)≤k := by exact_mod_cast hk
  have reciprocal := one_div_le_one_div_of_le zero_lt_one one
  have exactValue : ((p:ℝ)*q)*best p q k=(p:ℝ)+q-1/(k:ℝ) := by
    unfold best
    field_simp
    ring
  rw [exactValue,abs_lt] at accurate
  rw [abs_lt]
  constructor <;> linarith [one_div_pos.mpr kpos]

/-- Even the optimum is strictly below one chance in 2^1022 per draw when
both primes have at least 1024 bits. -/
theorem target_rate {p q k : ℕ} (lowp : 2^1023≤p) (lowq : 2^1023≤q) (hk : 0<k) :
    best p q k < 1/(2:ℝ)^1022 := by
  have pd : (2:ℝ)^1023≤p := by exact_mod_cast lowp
  have qd : (2:ℝ)^1023≤q := by exact_mod_cast lowq
  have ppos : (0:ℝ)<p := lt_of_lt_of_le (by positivity) pd
  have qpos : (0:ℝ)<q := lt_of_lt_of_le (by positivity) qd
  have kpos : (0:ℝ)<k := by exact_mod_cast hk
  calc
    best p q k < 1/(p:ℝ)+1/(q:ℝ) := by
      unfold best
      rw [div_add_div _ _ ppos.ne' qpos.ne']
      apply (div_lt_div_iff_of_pos_right (mul_pos ppos qpos)).mpr
      linarith [one_div_pos.mpr kpos]
    _ ≤ 1/(2:ℝ)^1023 + 1/(2:ℝ)^1023 := add_le_add
      (one_div_le_one_div_of_le (by positivity) pd) (one_div_le_one_div_of_le (by positivity) qd)
    _ = _ := by norm_num

/-- All cutoff lengths, including those past the tested two periods. -/
theorem example77 (m : ℕ) : ∑ i ∈ range m, split 77 i ≤ m * (13/56) := by
  have h := prefix_bound (p:=7) (q:=11) (u:=8) (v:=2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m
  norm_num [best] at h ⊢
  linarith

theorem example77_attains : ∑ i ∈ range 56, split 77 i = 13 := by
  have h := split_prefix (p:=7) (q:=11) (by decide) (by decide) (by decide) 56
  norm_num at h
  exact h

end PrimeFactors.MonotoneDivisorSampling
