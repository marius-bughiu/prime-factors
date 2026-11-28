import PrimeFactors.FiveSquarePrimeSupply

/-! Expected ranks of one fixed list of attained sum labels on the actual
conditioned population of balanced prime pairs. The hypothesis is the
endpoint estimate for the five-prime modulus. -/

namespace PrimeFactors.FiveSquareActualRanks

open Finset PrimeResidueRankTransfer FiveSquareGuessRanks FiveSquarePrimeSupply
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open PrimeProductRegion (K)
open PrimeSquareSumWeights (weight Pairs)
open scoped Classical

open private PrimeFactors.FiveSquareGuessRanks.labelFintype from PrimeFactors.FiveSquareGuessRanks
attribute [local instance 2000] PrimeFactors.FiveSquareGuessRanks.labelFintype

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

abbrev Order := Fin (Fintype.card GlobalLabels) ≃ GlobalLabels

/-- One-based mean over canonical distinct 1,024-bit prime pairs whose
product has 2,048 bits and is one modulo 7,239,457,225. -/
noncomputable def actual (e : Order) := primeMean X B K (rankOf (m:=m) e)

private theorem mean_cast {α : Type*} [Fintype α] (w : α → ℕ)
    (e : Fin (Fintype.card α) ≃ α) :
    (( ((∑ i,(i.val+1)*w (e i):ℕ):ℚ) / ((∑ s,w s:ℕ):ℚ) : ℚ) : ℝ) =
      IndependentGuessRanks.meanRank (fun s => (w s:ℝ)) e := by
  unfold IndependentGuessRanks.meanRank IndependentGuessRanks.total
  push_cast
  rfl

theorem local_mean (e : Order) : residueMean (rankOf (m:=m) e)=(mean e:ℝ) := by
  rw [residueMean_rankOf]
  exact (mean_cast (fun s : GlobalLabels => weight 1 s.val) e).symm

private theorem mean_le_card {α : Type*} [Fintype α] (w : α → ℝ) (nn : ∀ s,0≤w s)
    (e : Fin (Fintype.card α) ≃ α) :
    IndependentGuessRanks.meanRank w e≤Fintype.card α := by
  have mass : 0≤IndependentGuessRanks.total w := sum_nonneg (fun x _ => nn x)
  by_cases zero : IndependentGuessRanks.total w=0
  · simp only [IndependentGuessRanks.meanRank,zero,div_zero,Nat.cast_nonneg]
  rw [IndependentGuessRanks.meanRank,div_le_iff₀ (lt_of_le_of_ne mass (Ne.symm zero))]
  unfold IndependentGuessRanks.total
  rw [←e.sum_comp w,mul_sum]
  apply sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast i.isLt : (i.val:ℝ)+1≤Fintype.card α) (nn _)

private theorem error_bound {l u f y x : ℝ} (lp : 0<l) (up : 0<u) (fp : 0<f)
    (scale : f*u≤(f+1)*l) (yn : 0≤y) (low : l/u*y≤x) (high : x≤u/l*y) :
    |x-y|≤y/f := by
  have fp' : 0<f+1 := by linarith
  have lower : f/(f+1)≤l/u := (div_le_div_iff₀ fp' up).mpr (by linarith only [scale])
  have upper : u/l≤(f+1)/f := (div_le_div_iff₀ lp fp).mpr (by linarith only [scale])
  have a := (mul_le_mul_of_nonneg_right lower yn).trans low
  have b := high.trans (mul_le_mul_of_nonneg_right upper yn)
  have loss : f/(f+1)*y=y-y/(f+1) := by field_simp; ring
  have gain : (f+1)/f*y=y+y/f := by field_simp; ring
  rw [loss] at a
  rw [gain] at b
  have smaller : y/(f+1)≤y/f := div_le_div_of_nonneg_left yn fp (by linarith)
  exact abs_le.mpr ⟨by linarith only [a,smaller],by linarith only [b]⟩

/-- The same label order has nearly the same mean in the prime population
and in the uniform modular pair population. This holds for every order. -/
theorem every_order {li : ℕ→ℝ} (h : Endpoints li) (e : Order) :
    |actual e-(mean e:ℝ)|<1/1000 := by
  obtain ⟨l,u,lp,scale,cells⟩ := cell_bounds h
  have one : Pairs 1 m := ⟨(1,1),by simp⟩
  have up := lp.trans_le ((cells one).1.trans (cells one).2)
  obtain ⟨low,high⟩ := mean_bounds X B K (rankOf (m:=m) e) lp cells
  rw [local_mean] at low high
  have nn : 0≤(mean e:ℝ) := by
    rw [←local_mean]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have Fpos : (0:ℝ)<F := by positivity
  have scale' : (F:ℝ)*u≤((F:ℝ)+1)*l := by exact_mod_cast scale
  have bound := error_bound (by exact_mod_cast lp) (by exact_mod_cast up) Fpos scale' nn low high
  have size : (mean e:ℝ)≤41767264 := by
    rw [←local_mean,residueMean_rankOf]
    refine (mean_le_card _ (fun _ => Nat.cast_nonneg _) e).trans_eq ?_
    exact_mod_cast label_count
  apply bound.trans_lt
  apply (div_lt_iff₀ Fpos).mpr
  exact size.trans_lt (by norm_num [F])

/-- The optimum modular order also achieves the displayed actual interval.
Every actual order has mean strictly greater than the lower endpoint. -/
theorem optimum_interval {li : ℕ→ℝ} (h : Endpoints li) :
    (∀ e : Order, (470695147/48:ℝ)-1/1000 < actual e) ∧
    ∃ e : Order, (mean e:ℚ)=470695147/48 ∧ |actual e-(470695147/48:ℝ)|<1/1000 := by
  constructor
  · intro e
    have lo : (470695147/48:ℝ)≤(mean e:ℝ) := by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr (optimum.2 ⟨e,rfl⟩)
    have near := (abs_lt.mp (every_order h e)).1
    linarith only [lo,near]
  · obtain ⟨e,eq⟩ := optimum.1
    have local_eq : (mean e:ℝ)=470695147/48 := by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using congrArg (fun a : ℚ => (a:ℝ)) eq
    exact ⟨e,eq,local_eq ▸ every_order h e⟩

end PrimeFactors.FiveSquareActualRanks
