import PrimeFactors.FiveSquareGuessRanks
import PrimeFactors.JointSumGuessFloor

/-! A lower bound on the rank of every sum-guess list using the pairwise
minimum of finite multiplicities. The bound composes across coprime moduli,
including tables with different kinds of local weights. -/
namespace PrimeFactors.GuessTableOverlap

open Finset PrimeSquareSumWeights CoprimeGuessTables IndependentGuessRanks
open scoped Classical
open private PrimeFactors.FiveSquareGuessRanks.rank_identity PrimeFactors.FiveSquareGuessRanks.rankSum
  PrimeFactors.FiveSquareGuessRanks.overlap from PrimeFactors.FiveSquareGuessRanks
open private PrimeFactors.JointSumGuessFloor.sum_labels from PrimeFactors.JointSumGuessFloor

noncomputable def overlap {α : Type*} [Fintype α] (w : α→ℕ) : ℝ :=
  ∑ a,∑ b,(min (w a) (w b):ℝ)

noncomputable def tableMass {α : Type*} [Fintype α] (w : α→ℕ) : ℝ := ∑ a,(w a:ℝ)

/-- A lower bound for relative one-based guess rank before division by
the nonzero table size and mass. -/
def Share {α : Type*} [Fintype α] (w : α→ℕ) (c : ℝ) : Prop :=
  c*(Fintype.card α:ℝ)*tableMass w ≤ overlap w

theorem from_uniform {α : Type*} [Fintype α] (w : α→ℕ) {c : ℝ}
    (small : ∀ a,c*tableMass w ≤ (Fintype.card α:ℝ)*w a) : Share w c := by
  unfold Share overlap
  by_cases empty : IsEmpty α
  · haveI := empty
    simp
  haveI : Nonempty α := not_isEmpty_iff.mp empty
  have pos : (0:ℝ)<Fintype.card α := by exact_mod_cast Fintype.card_pos
  have each (a b : α) : c*tableMass w/(Fintype.card α:ℝ)≤min (w a:ℝ) (w b:ℝ) :=
    le_min ((div_le_iff₀ pos).mpr (by simpa only [mul_comm] using small a))
      ((div_le_iff₀ pos).mpr (by simpa only [mul_comm] using small b))
  have bound := sum_le_sum (s:=univ) (fun a _ => sum_le_sum (s:=univ) (fun b _ => each a b))
  simp only [sum_const,card_univ,nsmul_eq_mul] at bound
  calc
    _ = (Fintype.card α:ℝ)*((Fintype.card α:ℝ)*(c*tableMass w/(Fintype.card α:ℝ))) := by field_simp; ring
    _ ≤ _ := bound

theorem rank_floor {α : Type*} [Fintype α] (w : α→ℕ) {c : ℝ} (one : c≤1) (share : Share w c)
    (positive : 0<tableMass w) (e : Fin (Fintype.card α) ≃ α) :
    c*((Fintype.card α:ℝ)+1)/2 ≤ meanRank (fun a => (w a:ℝ)) e := by
  have rank := (PrimeFactors.FiveSquareGuessRanks.rank_identity (w ∘ e)).1
  have inner (a : α) := e.sum_comp (fun b => min (w a) (w b))
  have outer := e.sum_comp (fun a => ∑ b, min (w a) (w b))
  simp only [PrimeFactors.FiveSquareGuessRanks.overlap,PrimeFactors.FiveSquareGuessRanks.rankSum,
    Function.comp_apply,e.sum_comp w,inner,outer] at rank
  have ranks : tableMass w+overlap w ≤ 2*∑ i,((i.val:ℝ)+1)*w (e i) := by
    unfold tableMass overlap
    exact_mod_cast rank
  change c*_/2 ≤ _/(tableMass w)
  rw [le_div_iff₀ positive,div_mul_eq_mul_div,div_le_iff₀ (by norm_num : (0:ℝ)<2)]
  have extra := mul_le_mul_of_nonneg_right one positive.le
  unfold Share at share
  linarith only [ranks,share,extra]

theorem product {α β : Type*} [Fintype α] [Fintype β] (w : α→ℕ) (v : β→ℕ)
    {c d : ℝ} (cn : 0≤c) (dn : 0≤d) (first : Share w c) (second : Share v d) :
    Share (fun z : α×β => w z.1*v z.2) (c*d) := by
  have mass : tableMass (fun z : α×β => w z.1*v z.2)=tableMass w*tableMass v := by
    simp only [tableMass,Fintype.sum_prod_type,Nat.cast_mul,←mul_sum,←sum_mul]
  have pair (a a' : α) (b b' : β) :
      (min (w a) (w a'):ℝ)*(min (v b) (v b'):ℝ) ≤
        (min (w a*v b) (w a'*v b'):ℝ) := by
    exact_mod_cast le_min (Nat.mul_le_mul (min_le_left ..) (min_le_left ..))
      (Nat.mul_le_mul (min_le_right ..) (min_le_right ..))
  have bound := sum_le_sum (s:=univ) (fun a _ => sum_le_sum (s:=univ) (fun b _ =>
    sum_le_sum (s:=univ) (fun a' _ => sum_le_sum (s:=univ) (fun b' _ => pair a a' b b'))))
  have crossed (a : α) (b : β) :
      (∑ x,∑ y,(min (w a) (w x):ℝ)*(min (v b) (v y):ℝ))=
        (∑ x,(min (w a) (w x):ℝ))*(∑ y,(min (v b) (v y):ℝ)) := by
    simp_rw [←mul_sum]; rw [←sum_mul]
  unfold Share at first second ⊢
  rw [mass,Fintype.card_prod,Nat.cast_mul]
  have p : 0≤tableMass w := by unfold tableMass; positivity
  have q : 0≤tableMass v := by unfold tableMass; positivity
  have non : 0≤overlap w := (show 0≤c*(Fintype.card α:ℝ)*tableMass w by positivity).trans first
  have mul := mul_le_mul first second (by positivity) non
  have left : overlap w*overlap v ≤ overlap (fun z : α×β => w z.1*v z.2) := by
    simpa only [overlap,Fintype.sum_prod_type,crossed,←mul_sum,←sum_mul,Nat.cast_mul] using bound
  exact (le_of_eq (by ring)).trans (mul.trans left)

theorem congr {α β : Type*} [Fintype α] [Fintype β] (w : α→ℕ) (v : β→ℕ)
    (e : α≃β) (eq : ∀ a,w a=v (e a)) {c : ℝ} : Share w c ↔ Share v c := by
  unfold Share tableMass overlap
  simp_rw [eq]
  rw [Fintype.card_congr e,e.sum_comp (fun b => (v b:ℝ))]
  have row (a : β) := e.sum_comp (fun b => (min (v a) (v b):ℝ))
  simp_rw [row]
  rw [e.sum_comp (fun a => ∑ b,min (v a:ℝ) (v b:ℝ))]

/-- The share bound composes at coprime positive moduli with the same
fixed product residue. -/
theorem crt {a b : ℕ} [NeZero a] [NeZero b] (cop : a.Coprime b) (n : ℕ)
    {c d : ℝ} (cn : 0≤c) (dn : 0≤d)
    (first : Share (fun s : Labels a n => weight n s.val) c)
    (second : Share (fun s : Labels b n => weight n s.val) d) :
    Share (fun s : Labels (a*b) n => weight n s.val) (c*d) := by
  let r := ZMod.chineseRemainder cop
  let e : Labels (a*b) n ≃ Labels a n × Labels b n :=
    (r.toEquiv.subtypeEquiv (p:=AdmissibleSum (n:ZMod (a*b)))
      (q:=fun z => AdmissibleSum (n:ZMod a) z.1 ∧ AdmissibleSum (n:ZMod b) z.2) (by
        intro s
        rw [←positive_iff,CombinedSumWeights.weight_crt cop n s]
        simp only [Nat.pos_iff_ne_zero,mul_ne_zero_iff]
        exact and_congr ((Nat.pos_iff_ne_zero.symm).trans (positive_iff _))
          ((Nat.pos_iff_ne_zero.symm).trans (positive_iff _)))).trans (Equiv.subtypeProdEquivProd ..)
  have weights (s : Labels (a*b) n) : weight n s.val=weight n (e s).1.val*weight n (e s).2.val :=
    CombinedSumWeights.weight_crt cop n s.val
  exact (congr _ _ e weights).mpr (product _ _ cn dn first second)

end PrimeFactors.GuessTableOverlap
