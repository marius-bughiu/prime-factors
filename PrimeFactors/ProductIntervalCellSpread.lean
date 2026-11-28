import PrimeFactors.ExtendedModulusPrimeSupply

/-! Conditional unit-cell count differences for any upper product
threshold, and for intervals of products above the full-width cutoff. -/
namespace PrimeFactors.ProductIntervalCellSpread

open Finset PrimeResidueRankTransfer ThresholdPairCount
open WideResiduePrimeSupply (B)
open FullRangeResidueEstimates (X)
open PrimeProductRegion (K)
open ExtendedModulusPrimeSupply (D Endpoints)
open private PrimeFactors.ExtendedModulusPrimeSupply.suffix PrimeFactors.ExtendedModulusPrimeSupply.upper
  from PrimeFactors.ExtendedModulusPrimeSupply
open private PrimeFactors.PrimeProductRegion.cutoff from PrimeFactors.PrimeProductRegion
open scoped Classical
set_option maxRecDepth 4096
set_option exponentiation.threshold 4096

abbrev E := 2*D*B+B
variable {d : ℕ} [NeZero d]

private theorem left_cut {t p : ℕ} (start : K≤t) (lo : X<p) (hi : p≤B) :
    X≤min (t/p) B :=
  le_min ((PrimeFactors.PrimeProductRegion.cutoff lo hi).1.trans (Nat.div_le_div_right start))
    (by decide +kernel)

/-- Above the top factor endpoint the row is empty; clipping the cutoff
to B leaves that empty row available to the same endpoint estimate. -/
private theorem slice {t p : ℕ} (start : K≤t) (lo : X<p) (hi : p≤B) (a : ZMod d) :
    (tail B X a).filter (fun q => t<p*q)=tail B (min (t/p) B) a := by
  ext q
  have positive := (by decide +kernel : 0<X).trans lo
  have eq : t<p*q ↔ t/p<q := by rw [Nat.div_lt_iff_lt_mul positive,Nat.mul_comm q p]
  simp only [mem_filter,mem_tail,eq]
  have baseline := left_cut start lo hi
  constructor
  · rintro ⟨⟨_,top,P,r⟩,past⟩
    exact ⟨(min_le_left _ _).trans_lt past,top,P,r⟩
  · rintro ⟨past,top,P,r⟩
    exact ⟨⟨baseline.trans_lt past,top,P,r⟩,by omega⟩

/-- For each absolute threshold t at or above 2^2047, any two ordered
unit cells have counts differing by at most E. -/
theorem threshold_spread (low : 3≤d) (domain : d≤X) {li : ℕ→ℝ} (h : Endpoints d li)
    {t : ℕ} (start : K≤t) {v w : ZMod d×ZMod d} (a : IsUnit v.1) (b : IsUnit v.2)
    (c : IsUnit w.1) (f : IsUnit w.2) : cell X B t v≤cell X B t w+E := by
  apply ThresholdPairCount.spread _ _ _ _ (PrimeFactors.ExtendedModulusPrimeSupply.upper _)
    (PrimeFactors.ExtendedModulusPrimeSupply.upper _) (PrimeFactors.ExtendedModulusPrimeSupply.upper _)
  · intro p hp
    obtain ⟨lo,hi,_,_⟩ := mem_tail.mp hp
    rw [slice start lo hi,slice start lo hi]
    exact PrimeFactors.ExtendedModulusPrimeSupply.suffix low domain h _ _ b f
      (left_cut start lo hi) (min_le_right _ _)
  · intro p hp
    obtain ⟨lo,hi,_,_⟩ := mem_tail.mp hp
    rw [slice start lo hi,slice start lo hi]
    exact PrimeFactors.ExtendedModulusPrimeSupply.suffix low domain h _ _ a c
      (left_cut start lo hi) (min_le_right _ _)

/-- Distinct ordered primes in the prescribed coordinate classes and
width range whose product lies in the half-open interval (lo,hi]. -/
noncomputable def bandPairs (lo hi : ℕ) (v : ZMod d×ZMod d) :=
  ((tail B X v.1) ×ˢ (tail B X v.2)).filter
    (fun z => lo<z.1*z.2 ∧ z.1*z.2≤hi ∧ z.1≠z.2)

private theorem nested (A C : Finset ℕ) {lo hi : ℕ} (order : lo≤hi) :
    distinctRegion hi A C ⊆ distinctRegion lo A C := by
  intro z hz
  simp only [distinctRegion,region,mem_filter] at hz ⊢
  exact ⟨⟨hz.1.1,order.trans_lt hz.1.2⟩,hz.2⟩

private theorem conditions {P Q : Prop} {lo hi t : ℕ} :
    (P ∧ lo<t ∧ t≤hi ∧ Q) ↔ (((P ∧ lo<t) ∧ Q) ∧ ¬((P ∧ hi<t) ∧ Q)) := by
  constructor
  · rintro ⟨p,left,right,q⟩
    exact ⟨⟨⟨p,left⟩,q⟩,fun h => (not_lt_of_ge right) h.1.2⟩
  · rintro ⟨⟨⟨p,left⟩,q⟩,no⟩
    exact ⟨p,left,le_of_not_gt (fun h => no ⟨⟨p,h⟩,q⟩),q⟩

private theorem count_between (A C : Finset ℕ) {lo hi : ℕ} (order : lo≤hi) :
    ((A ×ˢ C).filter (fun z => lo<z.1*z.2 ∧ z.1*z.2≤hi ∧ z.1≠z.2)).card =
      (distinctRegion lo A C).card-(distinctRegion hi A C).card := by
  have eq : (A ×ˢ C).filter (fun z => lo<z.1*z.2 ∧ z.1*z.2≤hi ∧ z.1≠z.2)=
      distinctRegion lo A C \ distinctRegion hi A C := by
    ext z
    simpa only [mem_sdiff,distinctRegion,region,mem_filter] using
      (conditions (P:=z∈A ×ˢ C) (Q:=z.1≠z.2) (lo:=lo) (hi:=hi) (t:=z.1*z.2))
  rw [eq,card_sdiff (nested A C order)]

attribute [local irreducible] tail

omit [NeZero d] in
/-- The threshold difference counts exactly the interval, including the
upper endpoint and excluding the lower. -/
theorem band_count (v : ZMod d×ZMod d) {lo hi : ℕ} (order : lo≤hi) :
    (bandPairs lo hi v).card=cell X B lo v-cell X B hi v := by
  unfold bandPairs cell
  exact count_between _ _ order

omit [NeZero d] in
private theorem decreases (v : ZMod d×ZMod d) {lo hi : ℕ} (order : lo≤hi) :
    cell X B hi v≤cell X B lo v := by
  unfold cell
  exact card_le_card (nested _ _ order)

attribute [local irreducible] cell bandPairs

/-- The threshold at each end contributes one copy of the error. The
cells may be empty, and no lower bound on the interval length is needed. -/
theorem difference_spread (low : 3≤d) (domain : d≤X) {li : ℕ→ℝ} (h : Endpoints d li)
    {lo hi : ℕ} (start : K≤lo) (order : lo≤hi) {v w : ZMod d×ZMod d}
    (a : IsUnit v.1) (b : IsUnit v.2) (c : IsUnit w.1) (f : IsUnit w.2) :
    cell X B lo v-cell X B hi v≤cell X B lo w-cell X B hi w+2*E := by
  have diff {A B C D Z : ℕ} (lo : A≤B+Z) (hi : D≤C+Z) (order : D≤B) : A-C≤B-D+2*Z := by omega
  exact diff (threshold_spread low domain h start a b c f)
    (threshold_spread low domain h (start.trans order) c f a b) (decreases w order)

/-- The same bound on the cardinalities of the two actual sets of ordered
prime pairs. -/
theorem band_spread (low : 3≤d) (domain : d≤X) {li : ℕ→ℝ} (h : Endpoints d li)
    {lo hi : ℕ} (start : K≤lo) (order : lo≤hi) {v w : ZMod d×ZMod d}
    (a : IsUnit v.1) (b : IsUnit v.2) (c : IsUnit w.1) (f : IsUnit w.2) :
    (bandPairs lo hi v).card≤(bandPairs lo hi w).card+2*E := by
  rw [band_count v order,band_count w order]
  exact difference_spread low domain h start order a b c f

end PrimeFactors.ProductIntervalCellSpread
