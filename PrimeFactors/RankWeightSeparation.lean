import PrimeFactors.FiveSquarePrimeSupply

/-! Conditions under which unequal residue-pair multiplicities force unequal
frequencies of the corresponding sum labels in a finite prime population.
Labels of equal multiplicity may have different frequencies. -/

namespace PrimeFactors.RankWeightSeparation

open Finset PrimeSquareSumWeights PrimeResidueRankTransfer
open scoped Classical

theorem sizes_separate {l u F a b : ℕ} (pos : 0 < l) (ratio : F*u ≤ (F+1)*l)
    (small : a < F) (sizes : a < b) : a*u < b*l := by
  by_cases h : u ≤ l
  · exact (Nat.mul_le_mul_left a h).trans_lt (Nat.mul_lt_mul_of_pos_right sizes pos)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge h)
  have dp : 0 < d := by omega
  have gap : F*d ≤ l := by nlinarith only [ratio]
  have diff := (Nat.mul_lt_mul_of_pos_right small dp).trans_le gap
  have step := Nat.mul_le_mul_right l (Nat.succ_le_of_lt sizes)
  nlinarith only [diff,step]

/-- Sums of possibly nonconstant masses over two fibers preserve the strict
order of their sizes whenever the smaller size is below F. Only the lower
bound in the larger fiber and the upper bound in the smaller are needed. -/
theorem mass_order {α : Type*} (A B : Finset α) (c : α → ℕ) {l u F : ℕ}
    (pos : 0 < l) (ratio : F*u ≤ (F+1)*l) (smaller : A.card < B.card) (small : A.card < F)
    (upper : ∀ i∈A, c i ≤ u) (lower : ∀ i∈B, l ≤ c i) :
    (∑ i∈A,c i) < ∑ i∈B,c i := by
  have top := sum_le_sum upper
  have bottom := sum_le_sum lower
  simp only [sum_const,nsmul_eq_mul] at top bottom
  exact top.trans_lt ((sizes_separate pos ratio small smaller).trans_le bottom)

variable {m : ℕ} [NeZero m]

/-- Number of sorted distinct prime pairs with the specified sum label in
the product-one population. -/
noncomputable def primeCount (X B K : ℕ) (s : ZMod m) :=
  ((population m X B K).filter fun v => ((v.1+v.2:ℕ):ZMod m)=s).card

private noncomputable def fiber (s : ZMod m) := univ.filter fun v : Pairs 1 m => sumOf v=s

private theorem fiber_size (s : ZMod m) : (fiber s).card = weight 1 s := by
  simp only [fiber, weight, Nat.card_eq_fintype_card, Fintype.card_subtype]

private theorem fiber_mass (X B K : ℕ) (s : ZMod m) :
    2 * primeCount X B K s = ∑ v∈fiber s, cell X B K v.val := by
  have h := twice_score X B K (fun a => if a=s then 1 else 0)
  simpa only [primeCount,fiber,mul_ite,mul_one,mul_zero,←sum_filter,sum_const,nsmul_eq_mul,
    Nat.cast_id] using h

/-- Each ordered residue-pair cell contributes its actual number of prime
pairs. Grouping by their sum gives twice the count of sorted prime pairs. -/
theorem prime_count_bounds {X B K l u : ℕ}
    (cells : ∀ v : Pairs 1 m, l ≤ cell X B K v.val ∧ cell X B K v.val ≤ u)
    (s : ZMod m) :
    weight 1 s * l ≤ 2*primeCount X B K s ∧ 2*primeCount X B K s ≤ weight 1 s * u := by
  rw [fiber_mass,←fiber_size]
  have bot := sum_le_sum (s:=fiber s) (fun v _ => (cells v).1)
  have top := sum_le_sum (s:=fiber s) (fun v _ => (cells v).2)
  simpa only [sum_const,nsmul_eq_mul] using And.intro bot top

theorem prime_label_order {X B K l u F : ℕ} (pos : 0 < l) (ratio : F*u ≤ (F+1)*l)
    (cells : ∀ v : Pairs 1 m, l ≤ cell X B K v.val ∧ cell X B K v.val ≤ u)
    {s t : ZMod m} (sizes : weight 1 s < weight 1 t) (small : weight 1 s < F) :
    primeCount X B K s < primeCount X B K t := by
  have low := (prime_count_bounds cells s).2
  have high := (prime_count_bounds cells t).1
  have h := low.trans_lt ((sizes_separate pos ratio small sizes).trans_le high)
  omega

open private PrimeFactors.FiveSquareGuessRanks.labelFintype from PrimeFactors.FiveSquareGuessRanks
attribute [local instance 2000] PrimeFactors.FiveSquareGuessRanks.labelFintype
set_option maxRecDepth 4096
set_option exponentiation.threshold 4096

open PrimeProductRegion (K)
open WideResiduePrimeSupply (B)
open FullRangeResidueEstimates (X)

/-- The possible positive weights in the five-prime example. Membership of
every attained label is checked by the compressed 32-leaf CRT histogram. -/
def fiveWeights : List ℕ :=
  [32,80,112,176,208,272,280,440,520,616,680,728,952,1144,1496,1540,1768,1820,
   2380,2860,3740,4004,4420,5236,6188,9724,10010,13090,15470,24310,34034,85085]

private theorem supported_of_sum {α : Type*} [Fintype α] (w : α → ℕ)
    (zero : (∑ s, if w s ∈ fiveWeights then 0 else 1) = (0:ℕ)) (s : α) :
    w s ∈ fiveWeights := by
  classical
  have small := Finset.single_le_sum (f:=fun a => if w a ∈ fiveWeights then 0 else 1)
    (fun a _ => Nat.zero_le _) (mem_univ s)
  by_contra missing
  simp only [missing,if_false,zero] at small
  omega

theorem five_supported (s : FiveSquareGuessRanks.GlobalLabels) : weight 1 s.val ∈ fiveWeights := by
  let missing (w : ℕ) := if w ∈ fiveWeights then 0 else 1
  have empty : FiveSquareGuessRanks.compressed [5,7,11,13,17] missing = 0 := by decide +kernel
  exact supported_of_sum _ ((FiveSquareGuessRanks.global_histogram missing).trans empty) s

/-- Conversely, each listed weight occurs on at least one actual residue
label. This certifies the support without enumerating forty million labels. -/
theorem five_support_exact (w : ℕ) :
    (∃ s : FiveSquareGuessRanks.GlobalLabels, weight 1 s.val = w) ↔ w ∈ fiveWeights := by
  constructor
  · rintro ⟨s,rfl⟩
    exact five_supported s
  · intro member
    have rows : ∀ a∈fiveWeights, 0 < FiveSquareGuessRanks.compressed [5,7,11,13,17]
        (fun v => if v=a then 1 else 0) := by decide +kernel
    have pos := rows w member
    rw [←FiveSquareGuessRanks.global_histogram] at pos
    by_contra! missing
    simp [missing] at pos

theorem five_weight_bound (s : FiveSquareGuessRanks.GlobalLabels) : weight 1 s.val ≤ 85085 :=
  (by decide +kernel : ∀ a∈fiveWeights, a≤85085) _ (five_supported s)

/-- The smallest ratio of different entries in the support table is 35/34.
The entries 272 and 280 attain it. -/
theorem five_gap :
    (∀ a∈fiveWeights, ∀ b∈fiveWeights, a<b → 35*a≤34*b) ∧
    272∈fiveWeights ∧ 280∈fiveWeights ∧ 35*272=34*280 := by decide +kernel

/-- A spread strictly smaller than 35/34 suffices to order all distinct
groups, without needing the much tighter analytic prime-count estimate. -/
theorem five_label_order {l u x b k : ℕ} (spread : 34*u < 35*l)
    (cells : ∀ v : Pairs 1 FiveSquarePrimeSupply.m,
      l ≤ cell x b k v.val ∧ cell x b k v.val ≤ u)
    {s t : FiveSquareGuessRanks.GlobalLabels} (sizes : weight 1 s.val < weight 1 t.val) :
    primeCount x b k s.val < primeCount x b k t.val := by
  have nz : 0 < weight 1 s.val :=
    (by decide +kernel : ∀ n∈fiveWeights, 0<n) _ (five_supported s)
  have gap := five_gap.1 _ (five_supported s) _ (five_supported t) sizes
  have lhs := Nat.mul_lt_mul_of_pos_right spread nz
  have rhs := Nat.mul_le_mul_right l gap
  have cross : weight 1 s.val*u < weight 1 t.val*l := by nlinarith only [lhs,rhs]
  have lower := (prime_count_bounds cells t.val).1
  have upper := (prime_count_bounds cells s.val).2
  omega

/-- For the full-width prime population, strict local layers are strictly
ordered in actual frequency under the explicit prime-count hypotheses.
No comparison is implied inside a tied local layer. -/
theorem five_full_width {li : ℕ → ℝ} (supply : FiveSquarePrimeSupply.Endpoints li)
    {s t : FiveSquareGuessRanks.GlobalLabels} (sizes : weight 1 s.val < weight 1 t.val) :
    primeCount X B K s.val < primeCount X B K t.val := by
  obtain ⟨l,u,pos,ratio,cells⟩ := FiveSquarePrimeSupply.cell_bounds supply
  apply prime_label_order pos ratio cells sizes
  exact (five_weight_bound s).trans_lt (by decide +kernel : 85085 < FiveSquarePrimeSupply.F)

end PrimeFactors.RankWeightSeparation
