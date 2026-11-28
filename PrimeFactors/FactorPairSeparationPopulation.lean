import PrimeFactors.FactorPairSeparationDepth
import PrimeFactors.FactorClueWidthProfile
import PrimeFactors.ChebyshevPrimeSample

/-! Population frequencies when the low bits of the true sum are supplied.
The finite failure count uses only the diagonal of unit pairs modulo 2^(j+1). -/
namespace PrimeFactors.FactorPairSeparationPopulation

open Finset FactorPairSeparationDepth FactorClueWidthProfile
open MixedPrefixSample (eligible)
open PrimeResidueRankTransfer (cell)
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open PrimeProductRegion (K)
open private PrimeFactors.FullPopulationFavoredSums.mem_eligible from PrimeFactors.FullPopulationFavoredSums
open private PrimeFactors.FiveSquareAllPrimeRanks.actual_weighted from PrimeFactors.FiveSquareAllPrimeRanks
open private PrimeFactors.ExtendedProductCosts.unit_of_prime from PrimeFactors.ExtendedProductCosts
open private PrimeFactors.QuarticLocalPopulation.relative PrimeFactors.QuarticLocalPopulation.bmor_cells
  from PrimeFactors.QuarticLocalPopulation
open scoped Classical
set_option exponentiation.threshold 4096
attribute [local irreducible] eligible cell

/-- Below the two boundary branches, k+j supplied sum bits suffice precisely
when the two factors differ within their first j+1 bits. -/
theorem determines_iff_different {p q k j : ℕ} (ord : p<q) (room : j+3<k) :
    Determines p q k (k+j) ↔ ¬p ≡ q [MOD 2^(j+1)] := by
  obtain ⟨t,ht⟩ := exists_gap ord
  obtain ⟨u,hu,gap⟩ := (gap_iff ord.le).mp ht
  have ze : (q:ℤ)-p=2^t*(u:ℤ) := by
    rw [←Nat.cast_sub ord.le]; exact_mod_cast gap
  have zo : Odd (u:ℤ) := by exact_mod_cast hu
  rw [determines_iff (by omega) ze zo,Nat.modEq_iff_dvd' ord.le,gap]
  have power : (2:ℕ)^(j+1) ∣ 2^t*u ↔ j+1≤t := by
    rw [(hu.coprime_two_right.pow_right (j+1)).symm.dvd_mul_right,
      Nat.pow_dvd_pow_iff_le_right (by decide : 1<(2:ℕ))]
  rw [power]
  unfold depth
  split_ifs <;> omega

/-- Full-width unordered prime pairs where every pair of compatible modular
factor endings is the true unordered pair at k bits. -/
noncomputable def sufficient (k e : ℕ) := eligible.filter fun v => Determines v.1 v.2 k e

private theorem sufficient_eq {k j : ℕ} (room : j+3<k) :
    sufficient k (k+j)=eligible.filter fun v => ¬v.1 ≡ v.2 [MOD 2^(j+1)] := by
  apply filter_congr
  rintro ⟨p,q⟩ good
  exact determines_iff_different (PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp good).2.1 room

attribute [local irreducible] sufficient

private def diag {d : ℕ} (a b : ZMod d) : ℕ := if a=b then 1 else 0

private theorem diag_mean (j : ℕ) :
    (∑ v : MaximalFactorCluePopulation.Unit j × MaximalFactorCluePopulation.Unit j,
      (diag v.1.val v.2.val:ℝ))/Fintype.card (MaximalFactorCluePopulation.Unit j ×
        MaximalFactorCluePopulation.Unit j)=1/(2:ℝ)^j := by
  have row (a : MaximalFactorCluePopulation.Unit j) :
      (∑ b : MaximalFactorCluePopulation.Unit j,(diag a.val b.val:ℝ))=1 := by
    simp [diag,←Units.ext_iff]
  rw [Fintype.sum_prod_type]
  simp only [row,sum_const,card_univ,nsmul_eq_mul,mul_one,Fintype.card_prod,
    MaximalFactorCluePopulation.unit_count,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  field_simp

private theorem filter_fraction {α : Type*} (s : Finset α) (P : α→Prop) [DecidablePred P]
    (pos : s.card≠0) :
    ((s.filter (fun v => ¬ P v)).card:ℝ)/s.card=1-((s.filter P).card:ℝ)/s.card := by
  have total : ((s.filter P).card:ℝ) + (s.filter (fun v => ¬ P v)).card=s.card := by
    exact_mod_cast filter_card_add_filter_neg_card_eq_card P (s:=s)
  have nz : (s.card:ℝ)≠0 := by exact_mod_cast pos
  field_simp
  linarith only [total]

private theorem diag_fraction (s : Finset (ℕ×ℕ)) (d : ℕ) (pos : s.card≠0) :
    ((s.filter (fun v => ¬v.1 ≡ v.2 [MOD d])).card:ℝ)/s.card =
      1-((∑ v∈s,diag (d:=d) v.1 v.2:ℕ):ℝ)/s.card := by
  rw [show (∑ v∈s,diag (d:=d) v.1 v.2)=(s.filter (fun v => v.1 ≡ v.2 [MOD d])).card by
    simp [diag,ZMod.natCast_eq_natCast_iff]]
  exact filter_fraction s (fun v => v.1 ≡ v.2 [MOD d]) pos

private theorem share_complement {k j : ℕ} (room : j+3<k) :
    ((sufficient k (k+j)).card:ℝ)/eligible.card =
      1-FiveSquareAllPrimeRanks.actual (diag (d:=2^(j+1))) := by
  have size := MixedPrefixSample.denominator ChebyshevPrimeSample.prime_count
  rw [sufficient_eq room,FiveSquareAllPrimeRanks.actual]
  exact diag_fraction eligible (2^(j+1)) (by omega)

private theorem of_cells {j k F l u : ℕ} (room : j+3<k) (cap : 2^(j+1)≤2^161)
    (lp : 0<l) (fp : 0<F) (scale : F*u≤(F+1)*l)
    (weights : ∀ v : MaximalFactorCluePopulation.Unit j × MaximalFactorCluePopulation.Unit j,
      l≤cell X B K (v.1.val,v.2.val) ∧ cell X B K (v.1.val,v.2.val)≤u) :
    |((sufficient k (k+j)).card:ℝ)/eligible.card-(1-1/(2:ℝ)^j)|≤(1/(2:ℝ)^j)/F := by
  let w (v : MaximalFactorCluePopulation.Unit j × MaximalFactorCluePopulation.Unit j) :=
    (cell X B K (v.1.val,v.2.val):ℝ)
  let c (v : MaximalFactorCluePopulation.Unit j × MaximalFactorCluePopulation.Unit j) :=
    (diag v.1.val v.2.val:ℝ)
  have err := PrimeFactors.QuarticLocalPopulation.relative w c (l:=(l:ℝ)) (u:=(u:ℝ)) (f:=(F:ℝ))
    (by exact_mod_cast lp) (by exact_mod_cast fp) (by exact_mod_cast scale)
    (fun v => ⟨Nat.cast_le.mpr (weights v).1,Nat.cast_le.mpr (weights v).2⟩) (fun v => Nat.cast_nonneg _)
  rw [show (∑ v,c v)/Fintype.card _=1/(2:ℝ)^j from diag_mean j] at err
  rw [share_complement room,sub_sub_sub_cancel_left,abs_sub_comm,
    PrimeFactors.FiveSquareAllPrimeRanks.actual_weighted diag (fun a b => by simp [diag,eq_comm])
      (PrimeFactors.ExtendedProductCosts.unit_of_prime cap)]
  exact err

/-- For j extra sum bits, the modulus-2^(j+1) endpoint estimates alone
give a relative error of at most 2^-146 on the failure fraction 2^-j. -/
theorem share {k j : ℕ} (jp : 1≤j) (limit : j≤160) (room : j+3<k) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints (2^(j+1)) li) :
    |((sufficient k (k+j)).card:ℝ)/eligible.card-(1-1/(2:ℝ)^j)|≤1/(2:ℝ)^(146+j) := by
  have low : 3≤2^(j+1) := (by decide : 3≤2^2).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have cap : 2^(j+1)≤2^161 := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨l,u,lp,scale,weights⟩ := ExtendedModulusPrimeSupply.cell_bounds low cap h
  have estimate := of_cells room cap lp (by decide : 0<2^146) scale weights
  apply estimate.trans_eq
  push_cast
  rw [pow_add]
  ring

theorem bits_168 {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints 512 li) :
    |((sufficient 160 168).card:ℝ)/eligible.card-255/256|≤1/(2:ℝ)^154 := by
  simpa only [show (1:ℝ)-1/2^8=255/256 by norm_num] using
    share (k:=160) (j:=8) (by decide) (by decide) (by decide) h

theorem bits_180 {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints (2^21) li) :
    |((sufficient 160 180).card:ℝ)/eligible.card-(1-1/(2:ℝ)^20)|≤1/(2:ℝ)^166 :=
  share (k:=160) (j:=20) (by decide) (by decide) (by decide) h

/-- Modulus 16 also has an unconditional published estimate. Lean takes
that estimate and the logarithmic integral identity as explicit inputs. -/
theorem bits_163_bmor {li : ℕ→ℝ} (h : QuarticLocalPopulation.BmorEndpoints li) :
    |((sufficient 160 163).card:ℝ)/eligible.card-7/8|≤1/8320 := by
  obtain ⟨l,u,lp,scale,weights⟩ := PrimeFactors.QuarticLocalPopulation.bmor_cells h
  have estimate := of_cells (k:=160) (j:=3) (by decide) (by decide) lp (by decide : 0<1040) scale weights
  norm_num at estimate ⊢
  exact estimate

end PrimeFactors.FactorPairSeparationPopulation
