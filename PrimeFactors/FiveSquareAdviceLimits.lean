import PrimeFactors.FactorOrbitAdviceFloor
import PrimeFactors.FiveSquareFactorGuessing

/-! Rank and fixed-prefix limits on all balanced full-width prime products.
The known product remainder selects an arbitrary menu of 2^24 orders. Each
actual prime product can then receive any one of those messages, even if a
helper has unrestricted knowledge of its exact prime factors. -/
namespace PrimeFactors.FiveSquareAdviceLimits

open Finset FactorOrbitAdviceFloor FiveSquareAllPrimeRanks
open FiveSquarePrimeSupply (m Endpoints)
open FiveSquareFactorGuessing (T)
open FiveSquarePolicy (U)
open private PrimeFactors.FiveSquareFactorGuessing.lift PrimeFactors.FiveSquareFactorGuessing.error
  PrimeFactors.FiveSquareFactorGuessing.uniform_by_product PrimeFactors.FiveSquareFactorGuessing.label_bound
  from PrimeFactors.FiveSquareFactorGuessing
open scoped Classical
set_option maxRecDepth 4096
attribute [local irreducible] CoprimeGuessTables.modulus Fintype.card

abbrev Codes := 2^24
abbrev Policy := ∀ n : U, Menu n Codes
abbrev Selector := ℕ×ℕ → Fin Codes

private theorem pos : 0<Codes := by decide +kernel

private noncomputable def best (P : Policy) (a b : U) := bestRank pos (P (a*b)) a
noncomputable def chosen {B : ℕ} (P : ∀ n : U, Menu n B) (k : Fin B) (a b : U) := rank (P (a*b)) k a
def hit (r : ℕ) : ℕ := if r≤100 then 1 else 0

private theorem hit_small (r : ℕ) : hit r≤2^33 := by unfold hit; split_ifs <;> decide

private theorem symmetric (P : Policy) (a b : U) : best P a b=best P b a := by
  unfold best
  rw [mul_comm b a]
  simpa only [mul_div_cancel_left] using (bestRank_partner pos (P (a*b)) a).symm

private theorem size (P : Policy) (a b : U) : best P a b≤2^33 := by
  apply (bestRank_le pos _ _ ⟨0,pos⟩).trans
  exact (Nat.succ_le_of_lt (Fin.isLt _)).trans
    ((PrimeFactors.FiveSquareFactorGuessing.label_bound (a*b)).trans
      (FiveSquarePolicy.unit_count.1.trans_le (by decide : T≤2^33)))

private theorem row (P : Policy) (n a : U) : best P a (a⁻¹*n)=bestRank pos (P n) a :=
  congrArg (fun u => bestRank pos (P u) a) (mul_inv_cancel_left a n)

private theorem average_constant (q : ℚ) : (∑ _ : U,q)/(T:ℚ)=q := by
  simp only [sum_const,card_univ,nsmul_eq_mul,FiveSquarePolicy.unit_count.1,T,Nat.cast_ofNat]
  ring

private theorem uniform_rank (P : Policy) : (3861593/65536:ℝ)≤uniform (PrimeFactors.FiveSquareFactorGuessing.lift (best P)) := by
  let g (n : U) := ((∑ a : U,bestRank pos (P n) a : ℕ):ℚ)/T
  have transfer := PrimeFactors.FiveSquareFactorGuessing.uniform_by_product (best P) g
    (fun n => by simp only [g,row])
  have each (n : U) : (3861593/65536:ℚ)≤g n := by
    have h := bestRank_floor pos (P n)
    rw [FiveSquarePolicy.unit_count.1] at h
    convert h using 1
    norm_num [Codes,T]
  rw [transfer]
  have cmp := div_le_div_of_nonneg_right (sum_le_sum (s:=univ) (fun n _ => each n))
    (by norm_num : (0:ℚ)≤T)
  rw [average_constant] at cmp
  simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr cmp

private theorem prefix_ratio {A : ℕ} (bound : A ≤ 2*Codes*100) :
    (A:ℚ)/T ≤ 131072/153153 := by
  apply (div_le_iff₀ (by norm_num : (0:ℚ)<T)).mpr
  have h : (A:ℚ) ≤ 2*Codes*100 := by exact_mod_cast bound
  exact h.trans_eq (by norm_num [Codes,T])

private theorem prefix_card {α : Type*} [Fintype α] (f : α → ℕ) :
    (univ.filter (fun a => f a≤100)).card = ∑ a,hit (f a) := by simp [hit]

private theorem uniform_prefix (P : Policy) :
    uniform (PrimeFactors.FiveSquareFactorGuessing.lift (fun a b => hit (best P a b)))≤(131072/153153:ℝ) := by
  let g (n : U) := ((univ.filter (fun a : U => bestRank pos (P n) a≤100)).card:ℚ)/T
  have transfer := PrimeFactors.FiveSquareFactorGuessing.uniform_by_product (fun a b => hit (best P a b)) g
    (fun n => by
      apply congrArg (fun k : ℕ => (k:ℚ)/T)
      exact (prefix_card _).trans (sum_congr rfl (fun a _ => congrArg hit (row P n a).symm)))
  have each (n : U) : g n≤(131072/153153:ℚ) := prefix_ratio (bestRank_prefix pos (P n) 100)
  have cmp := div_le_div_of_nonneg_right (sum_le_sum (s:=univ) (fun n _ => each n)) (by norm_num : (0:ℚ)≤T)
  rw [average_constant] at cmp
  rw [transfer]
  simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr cmp

noncomputable def averagePrime (f : ℕ×ℕ→ℕ) : ℝ :=
  ((∑ z∈MixedPrefixSample.eligible,f z:ℕ):ℝ)/MixedPrefixSample.eligible.card

private theorem monotone {f g : ℕ×ℕ→ℕ} (le : ∀ z,f z≤g z) : averagePrime f≤averagePrime g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Nat.cast_le.mpr (sum_le_sum (fun z _ => le z))

private theorem lift_mono {f g : U→U→ℕ} (le : ∀ a b,f a b≤g a b) (a b : ZMod m) :
    PrimeFactors.FiveSquareFactorGuessing.lift f a b≤PrimeFactors.FiveSquareFactorGuessing.lift g a b := by
  unfold PrimeFactors.FiveSquareFactorGuessing.lift
  split_ifs <;> first | exact le _ _ | exact le_rfl

/-- Actual rank when the message can depend on the complete prime pair. -/
noncomputable def primeMean {B : ℕ} (P : ∀ n : U, Menu n B) (select : ℕ×ℕ → Fin B) := averagePrime (fun z =>
  PrimeFactors.FiveSquareFactorGuessing.lift (chosen P (select z)) z.1 z.2)

/-- Fraction of the full prime-pair population whose chosen list has the
true orbit among its first one hundred positions. -/
noncomputable def primePrefix {B : ℕ} (P : ∀ n : U, Menu n B) (select : ℕ×ℕ → Fin B) := averagePrime (fun z =>
  PrimeFactors.FiveSquareFactorGuessing.lift (fun a b => hit (chosen P (select z) a b)) z.1 z.2)

theorem bits24 {li : ℕ→ℝ} (h : Endpoints li) (P : Policy) (select : Selector) :
    589232/10000 < primeMean P select ∧ primePrefix P select < 855824/1000000 := by
  have floor := uniform_rank P
  have small := uniform_prefix P
  have rank_err := (abs_le.mp (PrimeFactors.FiveSquareFactorGuessing.error h (best P) (symmetric P) (size P))).1
  have hit_err := (abs_le.mp (PrimeFactors.FiveSquareFactorGuessing.error h (fun a b => hit (best P a b))
    (fun a b => congrArg hit (symmetric P a b)) (fun a b => hit_small _))).2
  have rank_order : actual (PrimeFactors.FiveSquareFactorGuessing.lift (best P)) ≤ primeMean P select :=
    monotone (fun z => lift_mono (fun a b => bestRank_le pos _ _ (select z)) z.1 z.2)
  have hit_order : primePrefix P select ≤ actual (PrimeFactors.FiveSquareFactorGuessing.lift (fun a b => hit (best P a b))) := by
    apply monotone
    intro z
    apply lift_mono
    intro a b
    have le : best P a b≤chosen P (select z) a b := bestRank_le pos _ _ (select z)
    unfold hit
    split_ifs <;> omega
  constructor <;> linarith only [floor,small,rank_err,hit_err,rank_order,hit_order]

end PrimeFactors.FiveSquareAdviceLimits
