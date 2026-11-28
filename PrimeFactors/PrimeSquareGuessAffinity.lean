import PrimeFactors.PrimeSquareExpectedRank
import PrimeFactors.IndependentGuessRanks

/-! Squared affinity between the attained sum labels sampled uniformly and
the same labels sampled by a uniform ordered pair with fixed square unit
product modulo an odd prime square. -/

namespace PrimeFactors.PrimeSquareGuessAffinity

open PrimeSquareExpectedRank PrimeSquareSumWeights Real
open scoped Classical
open private PrimeFactors.PrimeSquareExpectedRank.class_count
  PrimeFactors.PrimeSquareExpectedRank.two_labels
  PrimeFactors.PrimeSquareExpectedRank.class_formula
  PrimeFactors.PrimeSquareExpectedRank.pairs_formula from PrimeFactors.PrimeSquareExpectedRank

/-- Squared sum of square roots of local multiplicities, divided by the
number of attained labels times the number of ordered pairs. -/
noncomputable def affinity (p : ℕ) : ℝ :=
  (2*sqrt p+((classes p:ℝ)-2)*sqrt 2)^2/((classes p:ℝ)*pairs p)

variable {p n : ℕ} [Fact p.Prime]

/-- Two labels have weight p and every other attained label has weight two. -/
theorem sum_weights (f : ℕ→ℝ) (odd : p≠2) (unit : ¬p∣n) (sq : IsSquare (n:ZMod p)) :
    (∑ s : Allowed p n, f (weight n s.val))=2*f p+((classes p:ℝ)-2)*f 2 := by
  classical
  obtain ⟨a,b,ne,_,_,w⟩ := PrimeFactors.PrimeSquareExpectedRank.two_labels odd unit sq
  have kernel (s : Allowed p n) : f (weight n s.val) = f 2+
      (if s=a then f p-f 2 else 0)+(if s=b then f p-f 2 else 0) := by
    rw [w]
    have hp := (Fact.out : p.Prime).two_le
    by_cases ha : s=a
    · have hb : s≠b := ha ▸ ne
      simp only [if_pos ha,if_neg hb,add_zero,show 2+(p-2)=p by omega]
      ring
    by_cases hb : s=b
    · simp only [if_neg ha,if_pos hb,add_zero,show 2+(p-2)=p by omega]
      ring
    · simp only [if_neg ha,if_neg hb,add_zero,Nat.cast_ofNat]
  simp only [kernel,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,PrimeFactors.PrimeSquareExpectedRank.class_count odd unit sq]
  ring

theorem root_mass (odd : p≠2) (unit : ¬p∣n) (sq : IsSquare (n:ZMod p)) :
    (∑ s : Allowed p n, sqrt (weight n s.val))=2*sqrt p+((classes p:ℝ)-2)*sqrt 2 :=
  sum_weights (fun k => sqrt k) odd unit sq

/-- This expression equals the finite affinity computed from the actual
local sample space for any square unit product, including product one. -/
theorem affinity_eq (odd : p≠2) (unit : ¬p∣n) (sq : IsSquare (n:ZMod p)) :
    affinity p=(∑ s : Allowed p n, sqrt (weight n s.val))^2 /
      ((Fintype.card (Allowed p n):ℝ)*Nat.card (Pairs n (p^2))) := by
  rw [root_mass odd unit sq,PrimeFactors.PrimeSquareExpectedRank.class_count odd unit sq,pair_count unit,affinity]

private theorem sizes (odd : p≠2) :
    (classes p:ℝ)=((p:ℝ)^2-3*p+4)/2 ∧ (pairs p:ℝ)=p*((p:ℝ)-1) := by
  exact ⟨by exact_mod_cast PrimeFactors.PrimeSquareExpectedRank.class_formula odd,
    by exact_mod_cast PrimeFactors.PrimeSquareExpectedRank.pairs_formula (p:=p)⟩

/-- Summing multiplicities over the attained labels counts every ordered pair once. -/
theorem total_mass (odd : p≠2) (unit : ¬p∣n) (sq : IsSquare (n:ZMod p)) :
    (∑ s : Allowed p n, (weight n s.val:ℝ))=(Nat.card (Pairs n (p^2)):ℝ) := by
  rw [sum_weights (fun k => (k:ℝ)) odd unit sq, pair_count unit, (sizes odd).1, (sizes odd).2]
  push_cast
  ring

/-- The local number-theoretic expression agrees with the finite-table definition. -/
theorem table_affinity (odd : p≠2) (unit : ¬p∣n) (sq : IsSquare (n:ZMod p)) :
    IndependentGuessRanks.affinity (fun s : Allowed p n => (weight n s.val:ℝ))=affinity p := by
  rw [IndependentGuessRanks.affinity,IndependentGuessRanks.rootTotal,
    IndependentGuessRanks.total,total_mass odd unit sq,affinity_eq odd unit sq]

/-- The affinity multiplies for independent local coordinates. Distinctness
is needed only to interpret their tuple as one residue by the Chinese remainder theorem. -/
theorem product_affinity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prime : ι→ℕ) [∀ i, Fact (prime i).Prime] (n : ℕ)
    (odd : ∀ i, prime i≠2) (unit : ∀ i, ¬prime i∣n) (sq : ∀ i, IsSquare (n:ZMod (prime i))) :
    IndependentGuessRanks.affinity
      (fun x : ∀ i, Allowed (prime i) n => ∏ i, (weight n (x i).val:ℝ))=
      ∏ i, affinity (prime i) := by
  rw [IndependentGuessRanks.affinity_product (fun i (s : Allowed (prime i) n) => (weight n s.val:ℝ))
    (fun _ _ => Nat.cast_nonneg _)]
  exact Finset.prod_congr rfl (fun i _ => table_affinity (odd i) (unit i) (sq i))

theorem affinity_nonneg (p : ℕ) : 0≤affinity p := by unfold affinity; positivity

/-- The spread of the two distinct square-root weights gives the exact
deficit from a uniform distribution. It vanishes at the prime three. -/
theorem deficit (odd : p≠2) :
    1-affinity p=2*((classes p:ℝ)-2)*(sqrt p-sqrt 2)^2/((classes p:ℝ)*pairs p) := by
  obtain ⟨count,total⟩ := sizes odd
  have positive : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have one : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have labels : 0<(classes p:ℝ) := by exact_mod_cast (by unfold classes; omega : 0<classes p)
  have mass : (pairs p:ℝ)=2*(sqrt p)^2+((classes p:ℝ)-2)*(sqrt 2)^2 := by
    rw [Real.sq_sqrt positive.le,Real.sq_sqrt (by norm_num),count,total]
    ring
  have pop : 0<(pairs p:ℝ) := total ▸ mul_pos positive (by linarith)
  unfold affinity
  field_simp [labels.ne',pop.ne']
  rw [mass]
  ring

/-- Every odd prime from eleven onward has affinity at most 1−1/(2p). -/
theorem deficit_lower (large : 11≤p) : 1/(2*(p:ℝ))≤1-affinity p := by
  have odd : p≠2 := by omega
  rw [deficit odd]
  obtain ⟨count,total⟩ := sizes odd
  have hp : (11:ℝ)≤p := by exact_mod_cast large
  have pos : (0:ℝ)<p := by linarith
  have small : 2*(p:ℝ)≤classes p := by
    rw [count]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hp) pos.le,hp]
  have cap : 0<(classes p:ℝ) := by linarith
  have mass : 0<(pairs p:ℝ) := total ▸ mul_pos pos (by linarith)
  have root : 2*sqrt 2≤sqrt p := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt (by norm_num),Real.sq_sqrt pos.le]
    linarith
  have gap : (sqrt p)^2≤(2*(sqrt p-sqrt 2))^2 :=
    (sq_le_sq₀ (by positivity) (by linarith [Real.sqrt_nonneg (p:ℝ)])).mpr (by linarith)
  rw [Real.sq_sqrt pos.le,mul_pow] at gap
  apply (div_le_div_iff₀ (by positivity : 0<2*(p:ℝ)) (mul_pos cap mass)).mpr
  rw [total]
  have first : (classes p:ℝ)*((p:ℝ)-1)≤(p:ℝ)*((classes p:ℝ)-2) := by linarith
  have step := mul_le_mul_of_nonneg_left first pos.le
  have last := mul_le_mul_of_nonneg_left gap (by nlinarith : 0≤(p:ℝ)*((classes p:ℝ)-2))
  nlinarith only [step,last]

/-- The preceding odd prime seven fails the same one-over-2p bound. -/
theorem seven : 1-affinity 7 < 1/(2*(7:ℝ)) := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [deficit (by decide : 7≠2)]
  norm_num only [classes,pairs,Nat.reduceSub,Nat.reduceDiv,Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat]
  have cross : (51/14:ℝ)<sqrt 7*sqrt 2 := by
    apply (sq_lt_sq₀ (by norm_num) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt (by norm_num),Real.sq_sqrt (by norm_num)]
    norm_num
  nlinarith only [cross,Real.sq_sqrt (by norm_num : (0:ℝ)≤7),Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

end PrimeFactors.PrimeSquareGuessAffinity
