import PrimeFactors.DyadicMenuPopulationOptimum

/-! For fixed products 3 or 7 modulo 8, and for products 5 modulo 8,
every attainable sum has equal modular weight. Count how many distinct
attainable guesses fit in a given budget, including budgets above support. -/
namespace PrimeFactors.DyadicFlatSumMenus

open Finset PrimeSquareSumWeights DyadicSumMenuBudget DyadicMenuPopulationOptimum
open scoped Classical
set_option exponentiation.threshold 4096

private theorem flat {α : Type*} [Fintype α] (w : α→ℕ) (c B : ℕ)
    (constant : ∀ s, 0<w s → w s=c) :
    IsGreatest {n : ℕ | ∃ A : Finset α, A.card≤B ∧ n=∑ s∈A,w s}
      (c*min B (univ.filter (fun s => 0<w s)).card) := by
  let P := univ.filter fun s => 0<w s
  have score (A : Finset α) : (∑ s∈A,w s)=c*(A∩P).card := by
    calc
      _ = ∑ s∈A,if s∈P then c else 0 := by
        apply sum_congr rfl
        intro s _
        simp only [P,mem_filter,mem_univ,true_and]
        by_cases pos : 0<w s
        · rw [if_pos pos]
          exact constant s pos
        · rw [if_neg pos]
          exact Nat.eq_zero_of_not_pos pos
      _ = _ := by rw [←sum_filter,filter_mem_eq_inter]; simp [mul_comm]
  constructor
  · obtain ⟨A,sub,card⟩ := exists_subset_card_eq (min_le_right B P.card)
    refine ⟨A,card ▸ min_le_left ..,?_⟩
    rw [score,inter_eq_left.mpr sub,card]
  · rintro _ ⟨A,ha,rfl⟩
    rw [score]
    exact Nat.mul_le_mul_left _ (le_min ((card_le_card inter_subset_left).trans ha)
      (card_le_card inter_subset_right))

private theorem support (e N : ℕ) :
    (univ.filter (fun s : ZMod (2^e) => 0<weight N s)).card=
      Fintype.card (CoprimeGuessTables.Labels (2^e) N) := by
  change _=Fintype.card {s : ZMod (2^e) // AdmissibleSum (N:ZMod (2^e)) s}
  rw [Fintype.card_subtype]
  apply congrArg Finset.card
  exact filter_congr (fun s _ => CoprimeGuessTables.positive_iff s)

/-- For either 3 or 7 modulo eight, each additional attainable label adds
four ordered pairs, up to the entire support of size 2^(e-3). -/
theorem three {e N : ℕ} (large : 3≤e) (cl : N%4=3) (B : ℕ) :
    IsGreatest {n : ℕ | ∃ A : Finset (ZMod (2^e)), A.card≤B ∧ n=∑ s∈A,weight N s}
      (4*min B (2^(e-3))) := by
  have result := flat (weight (m:=2^e) N) 4 B (DyadicSumPeak.three_weight large cl)
  rwa [support,(DyadicSumPeak.three_peak large cl).2] at result

/-- For 5 modulo eight, every attainable label adds eight ordered pairs,
up to the entire support of size 2^(e-4). -/
theorem five {e N : ℕ} (large : 5≤e) (cl : N%8=5) (B : ℕ) :
    IsGreatest {n : ℕ | ∃ A : Finset (ZMod (2^e)), A.card≤B ∧ n=∑ s∈A,weight N s}
      (8*min B (2^(e-4))) := by
  have result := flat (weight (m:=2^e) N) 8 B (DyadicSumPeak.five_weight large cl)
  rwa [support,(DyadicSumPeak.five_peak large cl).2] at result

theorem actual_three_161 (r : U 161) (cl : r.val.val%4=3) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints (2^161) li) :
    |bestActual r (2^32)-1/(2:ℝ)^126|≤1/(2:ℝ)^272 := by
  have top := three (by decide : 3≤161) cl (2^32)
  have result := optimum_161 r (2^32) _ top h
  norm_num at result ⊢
  exact result

theorem actual_five_161 (r : U 161) (cl : r.val.val%8=5) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints (2^161) li) :
    |bestActual r (2^32)-1/(2:ℝ)^125|≤1/(2:ℝ)^271 := by
  have top := five (by decide : 5≤161) cl (2^32)
  have result := optimum_161 r (2^32) _ top h
  norm_num at result ⊢
  exact result

end PrimeFactors.DyadicFlatSumMenus
