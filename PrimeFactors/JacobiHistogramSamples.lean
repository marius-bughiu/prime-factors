import PrimeFactors.ProjectiveWordMoments
import Mathlib.Tactic

/-! # Sampling only the signs of the projective-word discriminants

We compare the sign-only law for independent uniform residues with fair coin
flips. The finite overlap is the sum of the smaller masses on each possible word.
The total variation distance is one minus this overlap.
-/
namespace PrimeFactors.JacobiHistogramSamples
open Finset

noncomputable def signCount (n : ℕ) [NeZero n] (s : ℤ) : ℕ :=
  (univ.filter fun t : ZMod n => jacobiSym ((t.val:ℤ)^2-4) n = s).card

theorem histogram {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) :
    signCount (p*q) 1 = signCount (p*q) (-1)+1 ∧
    signCount (p*q) 0 = 2*(p+q)-4 ∧
    signCount (p*q) 0+signCount (p*q) 1+signCount (p*q) (-1) = p*q := by
  let n := p*q
  let J (t : ZMod n) := jacobiSym ((t.val:ℤ)^2-4) n
  have val (t : ZMod n) : J t = (if J t=1 then (1:ℤ) else 0) - (if J t= -1 then 1 else 0) := by
    rcases jacobiSym.trichotomy ((t.val:ℤ)^2-4) n with h|h|h <;> change J t = _ at h <;> simp [h]
  have mass (t : ZMod n) : (1:ℕ) = (if J t=0 then 1 else 0)+(if J t=1 then 1 else 0)+(if J t= -1 then 1 else 0) := by
    rcases jacobiSym.trichotomy ((t.val:ℤ)^2-4) n with h|h|h <;> change J t = _ at h <;> simp [h]
  have sum := ProjectiveWordMoments.full_signed cop hp hq
  change ∑ t : ZMod n, J t = 1 at sum
  rw [sum_congr rfl (fun t _ => val t),sum_sub_distrib,sum_boole,sum_boole] at sum
  have total := sum_congr (show (univ : Finset (ZMod n)) = univ from rfl) (fun t _ => mass t)
  rw [sum_add_distrib, sum_add_distrib, sum_boole, sum_boole, sum_boole] at total
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,ZMod.card] at total
  constructor
  · change (univ.filter fun t => J t=1).card=(univ.filter fun t => J t= -1).card+1
    omega
  · exact ⟨ProjectiveWordMoments.zero_count cop hp hq, total.symm⟩

/-- Overlap of independent sign-only samples with independent fair signs.
Label zero is the zero symbol; labels one and two are the two signs. -/
theorem overlap {w : Fin 3 → ℝ} (pos : ∀ i, 0≤w i) (fair : ∀ i, i≠0 → w i ≤ 1/2) (t : ℕ) :
    (∑ v : Fin t → Fin 3, min (∏ i, w (v i)) (∏ i, if v i=0 then 0 else (1:ℝ)/2)) =
      (w 1+w 2)^t := by
  classical
  let cut (j : Fin 3) := if j=0 then 0 else w j
  have each (v : Fin t → Fin 3) : min (∏ i, w (v i)) (∏ i, if v i=0 then 0 else (1:ℝ)/2) = ∏ i, cut (v i) := by
    by_cases h : ∃ i, v i=0
    · obtain ⟨i,hi⟩ := h
      have f : (∏ j, if v j=0 then 0 else (1:ℝ)/2) = 0 := prod_eq_zero (mem_univ i) (by rw [hi]; simp)
      have c : (∏ j, cut (v j))=0 := prod_eq_zero (mem_univ i) (by simp [cut,hi])
      rw [f,c,min_eq_right (prod_nonneg (fun j _ => pos _))]
    · push_neg at h
      simp only [cut, if_neg (h _)]
      exact min_eq_left (prod_le_prod (fun i _ => pos _) (fun i _ => fair _ (h i)))
  rw [sum_congr rfl (fun v _ => each v), ← Fintype.prod_sum]
  simp [Fin.sum_univ_three, cut]

/-- Probabilities of zero, positive and negative signs for one uniform residue. -/
noncomputable def weight (n : ℕ) [NeZero n] (i : Fin 3) : ℝ :=
  (signCount n (if i=0 then 0 else if i=1 then 1 else -1) : ℝ)/n

noncomputable def commonMass (n : ℕ) [NeZero n] (t : ℕ) : ℝ :=
  ∑ v : Fin t → Fin 3, min (∏ i, weight n (v i)) (∏ i, if v i=0 then 0 else (1:ℝ)/2)

/-- Shared mass of the two laws equals the probability of seeing no zero. -/
theorem common {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (t : ℕ) :
    commonMass (p*q) t = (1-(signCount (p*q) 0 : ℝ)/(p*q:ℕ))^t := by
  obtain ⟨diff,zeros,total⟩ := histogram cop hp hq
  have pp := (Fact.out : p.Prime).two_le
  have qp := (Fact.out : q.Prime).two_le
  have hn : 0<(p*q:ℕ) := Nat.mul_pos (by omega) (by omega)
  have pos : 0<((p*q:ℕ):ℝ) := by exact_mod_cast hn
  have cap (b : ℕ) (le : 2*b≤p*q) : (b:ℝ)/(p*q:ℕ) ≤ 1/2 := by
    rw [div_le_iff₀ pos]
    have real : 2*(b:ℝ)≤((p*q:ℕ):ℝ) := by exact_mod_cast le
    linarith
  unfold commonMass
  rw [overlap (fun i => by unfold weight; positivity) (fun i ne => ?_)]
  · congr 1
    simp only [weight, Fin.isValue, one_ne_zero, Fin.reduceEq, if_false, if_true]
    rw [← add_div, div_eq_iff pos.ne', sub_mul,one_mul, div_mul_cancel₀ _ pos.ne']
    have eq : ((signCount (p*q) 0:ℝ)+signCount (p*q) 1+signCount (p*q) (-1))=((p*q:ℕ):ℝ) := by exact_mod_cast total
    linarith
  · unfold weight
    rw [if_neg ne]
    split_ifs <;> apply cap <;> omega

theorem missed {x : ℝ} (lo : 0≤x) (hi : x≤1) (t : ℕ) :
    1-x^t ≤ t*(1-x) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := mul_le_mul_of_nonneg_right (pow_le_one₀ lo hi (n:=t)) (sub_nonneg.mpr hi)
    rw [pow_succ,Nat.cast_succ]
    linarith

set_option exponentiation.threshold 2048 in
/-- Even a trillion independent sign-only readings have an extremely small
statistical distance from fair coin flips. The public sample arguments are discarded. -/
theorem full_size {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (left : 2^1023≤p) (right : 2^1023≤q) (t : ℕ) (budget : t≤2^40) :
    (2:ℝ)^981*(1-commonMass (p*q) t)<1 := by
  have hp : p≠2 := by omega
  have hq : q≠2 := by omega
  obtain ⟨_,zeros,total⟩ := histogram cop hp hq
  let n := p*q
  let z := signCount (p*q) 0
  have zn : z≤n := by dsimp [n,z]; omega
  have num : 2^1021*z<n := by
    have a := Nat.mul_le_mul_right q left
    have b := Nat.mul_le_mul_left p right
    dsimp [n,z]
    rw [zeros]
    omega
  have np : 0<(n:ℝ) := by exact_mod_cast Nat.mul_pos (by omega : 0<p) (by omega : 0<q)
  have znn : 0≤(z:ℝ)/n := by positivity
  have frac : (z:ℝ)/n≤1 := (div_le_one np).mpr (by exact_mod_cast zn)
  have small := missed (x:=1-(z:ℝ)/n) (by linarith) (by linarith) t
  rw [sub_sub_cancel] at small
  have tcap : (t:ℝ)≤2^40 := by exact_mod_cast budget
  have extra := mul_le_mul_of_nonneg_right tcap znn
  have scaled := mul_le_mul_of_nonneg_left (small.trans extra) (by positivity : 0≤(2:ℝ)^981)
  rw [common cop hp hq]
  change 2^981*(1-(1-(z:ℝ)/n)^t)<1
  apply scaled.trans_lt
  rw [← mul_assoc,←pow_add,show 981+40=1021 by decide,← mul_div_assoc,div_lt_one np]
  exact_mod_cast num

theorem example77 : signCount 77 0=32 ∧ signCount 77 1=23 ∧ signCount 77 (-1)=22 ∧
    commonMass 77 2=(2025:ℝ)/5929 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have cop : Nat.Coprime 7 11 := by decide
  obtain ⟨diff,zeros,total⟩ := histogram cop (by decide) (by decide)
  change signCount 77 0=32 at zeros
  change signCount 77 1=signCount 77 (-1)+1 at diff
  change signCount 77 0+signCount 77 1+signCount 77 (-1)=77 at total
  refine ⟨zeros,by omega,by omega,?_⟩
  have pair := common cop (by decide) (by decide) 2
  change commonMass 77 2 = (1-(signCount 77 0:ℝ)/77)^2 at pair
  rw [pair,zeros]
  norm_num

end PrimeFactors.JacobiHistogramSamples
