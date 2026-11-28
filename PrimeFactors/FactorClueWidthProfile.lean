import PrimeFactors.DyadicClueMeanPopulation
import PrimeFactors.MaximalFactorCluePopulation

/-! How the number of extra fixed sum bits varies as the same factor is
revealed to different dyadic precisions. The gap of distinct factors has
one exact power of two, giving just one width of maximum relative gain. -/
namespace PrimeFactors.FactorClueWidthProfile

open Finset DyadicFactorClueGain
open MixedPrefixSample (eligible)
open private PrimeFactors.DyadicClueMeanPopulation.canonical from PrimeFactors.DyadicClueMeanPopulation

/-- Additional low sum bits when the actual first factor supplies k low bits. -/
def gain (k p q : ℕ) : ℕ := extra k (p%2^k) (p*q)

/-- The factors agree modulo 2^t and differ in the next bit. -/
def GapAt (p q t : ℕ) : Prop := q ≡ p+2^t [MOD 2^(t+1)]

private theorem zero_pow {i j : ℕ} (le : j ≤ i) : (2:ℕ)^i ≡ 0 [MOD 2^j] :=
  Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 le)

private theorem shift_zero (p : ℕ) {i j : ℕ} (le : j ≤ i) : p+2^i ≡ p [MOD 2^j] := by
  simpa only [Nat.add_zero] using (zero_pow le).add_left p

private theorem half_ne (p i : ℕ) : ¬ p+2^i ≡ p [MOD 2^(i+1)] := by
  intro eq
  have zero : (2:ℕ)^i ≡ 0 [MOD 2^(i+1)] := Nat.ModEq.add_left_cancel' p (by simpa only [Nat.add_zero] using eq)
  have := (Nat.pow_dvd_pow_iff_le_right (by decide : 1<(2:ℕ))).mp (Nat.modEq_zero_iff_dvd.mp zero)
  omega

/-- GapAt states that t is the exact exponent of two in the integer gap. -/
theorem gap_iff {p q t : ℕ} (ord : p≤q) : GapAt p q t ↔ ∃ u, Odd u ∧ q-p=2^t*u := by
  have addGap : p+(q-p)=q := Nat.add_sub_of_le ord
  constructor
  · intro h
    have eq : q-p ≡ 2^t [MOD 2^(t+1)] := Nat.ModEq.add_left_cancel' p (addGap.symm ▸ h)
    have zero := (eq.of_dvd (pow_dvd_pow 2 (Nat.le_succ t))).trans (zero_pow (le_refl t))
    obtain ⟨u,hu⟩ := Nat.modEq_zero_iff_dvd.mp zero
    refine ⟨u,Nat.odd_iff.mpr ?_,hu⟩
    have final : 2^t*u ≡ 2^t*1 [MOD 2^t*2] := by simpa only [hu,pow_succ (2:ℕ) t,mul_one] using eq
    exact Nat.ModEq.mul_left_cancel' (by positivity : (2:ℕ)^t ≠ 0) final
  · rintro ⟨u,odd,hu⟩
    have low : u ≡ 1 [MOD 2] := Nat.odd_iff.mp odd
    have eq : q-p ≡ 2^t [MOD 2^(t+1)] := by simpa only [hu,pow_succ (2:ℕ) t,mul_one] using low.mul_left' (2^t)
    simpa only [GapAt,addGap] using eq.add_left p

theorem exists_gap {p q : ℕ} (ord : p<q) : ∃ t, GapAt p q t := by
  obtain ⟨t,u,odd,eq⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : q-p≠0)
  exact ⟨t,(gap_iff ord.le).mpr ⟨u,odd,eq⟩⟩

private theorem level {p q k j : ℕ} (hk : 1≤k) (odd : Odd p) :
    j≤gain k p q ↔ j≤k+1 ∧ q ≡ p+2^k [MOD 2^j] := by
  rw [gain,PrimeFactors.DyadicClueMeanPopulation.canonical odd,extra_iff hk,
    show p^2+p*2^k=p*(p+2^k) by ring]
  exact and_congr_right fun _ => ⟨Nat.ModEq.cancel_left_of_coprime (odd.coprime_two_right.pow_right j).symm,
    fun eq => eq.mul_left p⟩

/-- The gain climbs with k up to a single peak at the exact gap exponent,
then drops by one and stays constant for all larger widths. -/
theorem profile {p q k t : ℕ} (hk : 1≤k) (odd : Odd p) (gap : GapAt p q t) :
    gain k p q = if k=t then t+1 else min k t := by
  change q ≡ p+2^t [MOD 2^(t+1)] at gap
  have low {j : ℕ} (jt : j≤t) : q ≡ p [MOD 2^j] :=
    (gap.of_dvd (pow_dvd_pow 2 (by omega : j≤t+1))).trans (shift_zero p jt)
  have ge {j : ℕ} (jk : j≤k) (jt : j≤t) : j≤gain k p q :=
    (level hk odd).mpr ⟨by omega,(low jt).trans (shift_zero p jk).symm⟩
  rcases lt_trichotomy k t with lt|rfl|gt
  · rw [if_neg lt.ne,min_eq_left lt.le]
    have lower := ge (le_refl k) lt.le
    have upper : ¬k+1≤gain k p q := fun bad => half_ne p k (((level hk odd).mp bad).2.symm.trans (low lt))
    omega
  · rw [if_pos rfl]
    exact le_antisymm ((level hk odd).mp (le_refl _)).1 ((level hk odd).mpr ⟨le_refl _,gap⟩)
  · rw [if_neg gt.ne',min_eq_right gt.le]
    have lower := ge gt.le (le_refl t)
    have upper : ¬t+1≤gain k p q := fun bad => half_ne p t
      (gap.symm.trans (((level hk odd).mp bad).2.trans (shift_zero p gt)))
    omega

/-- Equal factors have zero gap and no finite exact gap exponent. -/
theorem diagonal {k p : ℕ} (hk : 1≤k) (odd : Odd p) : gain k p p=k := by
  have lower := (level (q:=p) hk odd).mpr ⟨Nat.le_succ k,(shift_zero p (le_refl k)).symm⟩
  have upper : ¬k+1≤gain k p p := fun bad => half_ne p k (((level hk odd).mp bad).2.symm)
  omega

/-- Reading only the gain at width K distinguishes all gap exponents through
K and pools the larger ones in one bin. -/
def decoded (K g : ℕ) := if g=K then K+1 else if g=K+1 then K else g

theorem decode {p q K t : ℕ} (hK : 1≤K) (odd : Odd p) (gap : GapAt p q t) :
    decoded K (gain K p q)=min t (K+1) := by
  rw [profile hK odd gap]
  unfold decoded
  split_ifs <;> omega

/-- Two pairs have identical gain records at every width up to K iff their
exact gap exponents agree after truncation at K+1. -/
theorem same_record {p q p' q' K t t' : ℕ} (hK : 1≤K) (op : Odd p) (op' : Odd p')
    (a : GapAt p q t) (b : GapAt p' q' t') :
    (∀ k, 1≤k → k≤K → gain k p q=gain k p' q') ↔ min t (K+1)=min t' (K+1) := by
  constructor
  · intro all
    rw [←decode hK op a,←decode hK op' b,all K hK le_rfl]
  · intro same k lo hi
    rw [profile lo op a,profile lo op' b]
    split_ifs <;> omega

/-- A bounded example with gap 8. Supplying a fourth bit adds nothing to
the total fixed precision compared with supplying the third bit. -/
theorem control : ([1,2,3,4,5].map fun k => gain k 71 79)=[1,2,4,3,3] := by
  have gap : GapAt 71 79 3 := by unfold GapAt; decide
  have atK (k : ℕ) (lo : 1≤k) := profile lo (by decide : Odd 71) gap
  simp only [List.map_cons,List.map_nil]
  rw [atK 1 (by decide),atK 2 (by decide),atK 3 (by decide),atK 4 (by decide),atK 5 (by decide)]
  decide

open MaximalFactorCluePopulation (precisionLocus locus)
open scoped Classical
attribute [local irreducible] eligible locus precisionLocus

private theorem incompatible {i j p q : ℕ} (lt : i<j) (a : p ≡ q+2^i [MOD 2^(i+1)])
    (b : p ≡ q+2^j [MOD 2^(j+1)]) : False :=
  half_ne q i (a.symm.trans ((b.of_dvd (pow_dvd_pow 2 (by omega : i+1≤j+1))).trans (shift_zero q lt)))

/-- The full-width populations attaining the maximum at different positive
widths are disjoint, even if selecting a width were free. -/
theorem disjoint_maxima {i j : ℕ} (ip : 1 ≤ i) (jp : 1≤j) (ne : i≠j) :
    Disjoint (precisionLocus i) (precisionLocus j) := by
  rw [MaximalFactorCluePopulation.precision_eq ip, MaximalFactorCluePopulation.precision_eq jp]
  apply disjoint_left.mpr
  rintro ⟨p,q⟩ hi hj
  have l := (MaximalFactorCluePopulation.mem_locus.mp hi).2
  have r := (MaximalFactorCluePopulation.mem_locus.mp hj).2
  exact (lt_or_gt_of_ne ne).elim (fun h => incompatible h l r) (fun h => incompatible h r l)

/-- Success of at least one positive width from a prespecified finite menu. -/
noncomputable def anyWidth (W : Finset ℕ) := W.biUnion precisionLocus

/-- Relative transfer error for the sum of the disjoint frequencies. The
published endpoint hypotheses are required separately at the menu widths. -/
theorem any_width_share (W : Finset ℕ) (widths : ∀ k∈W, 1≤k ∧ k≤160) {li : ℕ→ℝ}
    (endpoints : ∀ k∈W, ExtendedModulusPrimeSupply.Endpoints (2^(k+1)) li) :
    |((anyWidth W).card:ℝ)/eligible.card - (∑ k∈W,1/(2:ℝ)^k)| ≤
      (∑ k∈W,1/(2:ℝ)^k)/(2:ℝ)^146 := by
  have dis : (W : Set ℕ).PairwiseDisjoint precisionLocus :=
    fun i hi j hj ne => disjoint_maxima (widths i hi).1 (widths j hj).1 ne
  rw [anyWidth,card_biUnion dis,Nat.cast_sum,sum_div,←sum_sub_distrib,sum_div]
  exact (abs_sum_le_sum_abs ..).trans (sum_le_sum fun k hk =>
    MaximalFactorCluePopulation.precision_close (widths k hk).1 (widths k hk).2 (endpoints k hk))

/-- A policy may choose the width from the entire public product, before
the true suffix at that width is supplied. -/
noncomputable def selected (W : Finset ℕ) (choose : ℕ→ℕ) := eligible.filter fun v =>
  choose (v.1*v.2) ∈ W ∧ v ∈ precisionLocus (choose (v.1*v.2))

/-- No such policy can capture more than the union of all possible maxima.
This concerns attainment of the maximum for the chosen width. -/
theorem selected_upper (W : Finset ℕ) (choose : ℕ→ℕ) (widths : ∀ k∈W, 1≤k ∧ k≤160)
    {li : ℕ→ℝ} (endpoints : ∀ k∈W, ExtendedModulusPrimeSupply.Endpoints (2^(k+1)) li) :
    ((selected W choose).card:ℝ)/eligible.card ≤
      (∑ k∈W,1/(2:ℝ)^k) + (∑ k∈W,1/(2:ℝ)^k)/(2:ℝ)^146 := by
  have sub : selected W choose ⊆ anyWidth W := by
    intro v hv
    obtain ⟨inside,hit⟩ := (mem_filter.mp hv).2
    exact mem_biUnion.mpr ⟨_,inside,hit⟩
  have ordered : ((selected W choose).card:ℝ)/eligible.card ≤ ((anyWidth W).card:ℝ)/eligible.card :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card sub)) (Nat.cast_nonneg _)
  exact ordered.trans (sub_le_iff_le_add'.mp (abs_le.mp (any_width_share W widths endpoints)).2)

end PrimeFactors.FactorClueWidthProfile
