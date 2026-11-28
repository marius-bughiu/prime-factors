import PrimeFactors.ProductIntervalCellSpread
import PrimeFactors.PartitionedResidueMeans
import PrimeFactors.PrimeProductBandCounts
import PrimeFactors.ExtendedProductCosts

/-! Quantifying the extra dependence on public leading product bits.
The prime population fixes the frequency of each observed band, including
any bands with no prime pairs. Within them we compare unit-pair costs. -/
namespace PrimeFactors.ProductBandCostTransfer

open Finset
open PrimeProductBandCounts (Band)
open ExtendedModulusPrimeSupply (Endpoints)
open ProductIntervalCellSpread (E)
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open PrimeProductRegion (K)
open private PrimeFactors.ExtendedProductCosts.lift PrimeFactors.ExtendedProductCosts.lift_sym
  PrimeFactors.ExtendedProductCosts.lift_units PrimeFactors.ExtendedProductCosts.unit_of_prime
  from PrimeFactors.ExtendedProductCosts
open private PrimeFactors.ExtendedModulusPrimeSupply.room_161 from PrimeFactors.ExtendedModulusPrimeSupply
open scoped Classical
set_option maxRecDepth 4096
set_option exponentiation.threshold 4096

variable {d : ℕ} [NeZero d]
private abbrev U (d : ℕ) := (ZMod d)ˣ
abbrev Cost (d k : ℕ) := Band k→U d→U d→ℕ

private noncomputable def weights (k : ℕ) (i : Band k) (v : U d×U d) :=
  PrimeProductBandCounts.count k i ((v.1:ZMod d),(v.2:ZMod d))

private noncomputable def score (k : ℕ) (f : Cost d k) (i : Band k) (v : U d×U d) : ℝ := f i v.1 v.2

noncomputable def mixture (k : ℕ) (f : Cost d k) := PartitionedResidueMeans.mixture (weights k) (score k f)

noncomputable def actual (k : ℕ) (f : Cost d k) := PrimeProductBandCounts.actual k
  (fun i => PrimeFactors.ExtendedProductCosts.lift (f i))

private abbrev lower := 2^850*(2^850-1)

private theorem floor (low : 3≤d) (cap : d≤2^161) {li : ℕ→ℝ} (h : Endpoints d li)
    {k : ℕ} (hk : k≤2047) (v : U d×U d) : lower≤∑ i,weights k i v := by
  simp only [weights,PrimeProductBandCounts.sum_count hk]
  exact ExtendedModulusPrimeSupply.lower_of_cap low cap (by decide +kernel)
    PrimeFactors.ExtendedModulusPrimeSupply.room_161 h v.1.isUnit v.2.isUnit

private theorem positive (low : 3≤d) (cap : d≤2^161) {li : ℕ→ℝ} (h : Endpoints d li)
    {k : ℕ} (hk : k≤2047) : 0<PartitionedResidueMeans.population (weights (d:=d) k) :=
  (Nat.mul_pos (Fintype.card_pos (α:=U d×U d)) (by decide +kernel : 0<lower)).trans_le
    (PartitionedResidueMeans.population_lower _ (floor low cap h hk))

private theorem row (k : ℕ) (f : Cost d k) (i : Band k) :
    (∑ v,score k f i v)/(Fintype.card (U d×U d):ℝ)=ExtendedProductCosts.uniform (f i) := by
  simp only [score,ExtendedProductCosts.uniform,Nat.cast_sum]

theorem mixture_le (k : ℕ) (low : 3≤d) (cap : d≤2^161) {li : ℕ→ℝ} (h : Endpoints d li)
    (hk : k≤2047) (f : Cost d k) {q : ℝ} (le : ∀ i,ExtendedProductCosts.uniform (f i)≤q) :
    mixture k f≤q := by
  apply PartitionedResidueMeans.mixture_le _ _ (positive low cap h hk)
  simpa only [row] using le

theorem le_mixture (k : ℕ) (low : 3≤d) (cap : d≤2^161) {li : ℕ→ℝ} (h : Endpoints d li)
    (hk : k≤2047) (f : Cost d k) {q : ℝ} (le : ∀ i,q≤ExtendedProductCosts.uniform (f i)) :
    q≤mixture k f := by
  apply PartitionedResidueMeans.le_mixture _ _ (positive low cap h hk)
  simpa only [row] using le

private theorem spread (low : 3≤d) (cap : d≤2^161) {li : ℕ→ℝ} (h : Endpoints d li)
    (k : ℕ) (i : Band k) (v w : U d×U d) : weights k i v≤weights k i w+2*E := by
  change PrimeProductBandCounts.count k i _≤PrimeProductBandCounts.count k i _+2*E
  apply ProductIntervalCellSpread.difference_spread low (cap.trans (by decide +kernel)) h
  · exact Nat.le_add_right _ _
  · unfold PrimeProductBandCounts.edge
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  exacts [v.1.isUnit,v.2.isUnit,w.1.isUnit,w.2.isUnit]

/-- For k extra public prefix bits, each band contributes one absolute
count error; no division by the size of a potentially very small band. -/
theorem close (k : ℕ) (low : 3≤d) (cap : d≤2^161) {li : ℕ→ℝ} (h : Endpoints d li)
    (hk : k≤2047) (f : Cost d k) (sym : ∀ i a b,f i a b=f i b a) {C : ℕ}
    (bound : ∀ i a b,f i a b≤C) :
    |actual k f-mixture k f|≤(2:ℝ)^k*(2*E)*(C:ℝ)/(lower:ℝ) := by
  have observed : actual k f=PartitionedResidueMeans.actual (weights k) (score k f) := by
    rw [actual,PrimeProductBandCounts.actual_weighted hk _ (fun i => PrimeFactors.ExtendedProductCosts.lift_sym (sym i))
      (PrimeFactors.ExtendedProductCosts.unit_of_prime cap)]
    simp only [PartitionedResidueMeans.actual,PartitionedResidueMeans.population,
      PartitionedResidueMeans.rowPopulation,weights,score,Nat.cast_sum,PrimeFactors.ExtendedProductCosts.lift_units]
  rw [observed]
  have bounded (i : Band k) (v : U d×U d) : 0≤score k f i v ∧ score k f i v≤(C:ℝ) :=
    ⟨Nat.cast_nonneg _,Nat.cast_le.mpr (bound i v.1 v.2)⟩
  have result := PartitionedResidueMeans.transfer_of_floor (weights k) (score k f) (spread low cap h k)
    bounded (by decide +kernel : 0<lower) (floor low cap h hk)
  simpa only [mixture,PrimeProductBandCounts.Band,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_mul] using result

theorem close64 (low : 3≤d) (cap : d≤2^161) {li : ℕ→ℝ} (h : Endpoints d li) (f : Cost d 64)
    (sym : ∀ i a b,f i a b=f i b a) {C : ℕ} (bound : ∀ i a b,f i a b≤C) :
    |actual 64 f-mixture 64 f|≤(C:ℝ)/(2:ℝ)^81 := by
  have enough : (2:ℝ)^64*(2*E)/lower≤1/2^81 := by norm_num [lower,E,ExtendedModulusPrimeSupply.D,B]
  have mul := mul_le_mul_of_nonneg_right enough (Nat.cast_nonneg C : 0≤(C:ℝ))
  exact (close 64 low cap h (by decide) f sym bound).trans (by linarith only [mul])

end PrimeFactors.ProductBandCostTransfer
