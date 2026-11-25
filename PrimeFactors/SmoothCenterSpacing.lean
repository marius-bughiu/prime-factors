import PrimeFactors.SmoothSumSelector
import Mathlib.Data.List.Chain

/-! Spacing and conditioning of the 647 possible 2,3-smooth factor sums.
The rational approximation 1054/665 to log₂(3) supplies a proposed order.
All comparisons certifying that order use only integer arithmetic. -/

namespace PrimeFactors.SmoothCenterSpacing
open Finset SmoothSumSelector

set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

/-- The left endpoint of the factor-sum range. -/
def X : ℕ := 2^1024

/-- A cheap shift proposed from the rational approximation, verified below for the whole range. -/
def fastCenter (b : ℕ) : ℕ := 2^(1024-(1054*b)/665)*3^b

/-- 359 is the inverse of 389 = 1054 mod 665. Only 18 rotation indices are omitted. -/
private def exponents : List ℕ := ((List.range 665).map (fun r => (359*r)%665)).filter (·<647)

noncomputable def centers : List ℕ := exponents.map fastCenter

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
private theorem shifts_valid : ∀ b : Fin 647, X≤fastCenter b ∧ fastCenter b<2^1025 := by decide +kernel

/-- The rational shift equals the canonical log₂ construction at every legal exponent. -/
theorem fast_correct {b : ℕ} (hb : b<647) : fastCenter b = SmoothSumSelector.candidate b := by
  obtain ⟨lo,hi⟩ := shifts_valid ⟨b,hb⟩
  exact (contains (s:=fastCenter b) (a:=1024-(1054*b)/665) (b:=b) lo hi rfl).2.symm

theorem candidate_mem {b : ℕ} (hb : b<647) : candidate b ∈ centers := by
  rw [←fast_correct hb]
  apply List.mem_map.mpr ⟨b,?_,rfl⟩
  apply List.mem_filter.mpr
  refine ⟨List.mem_map.mpr ⟨(389*b)%665,List.mem_range.mpr (Nat.mod_lt _ (by decide)),?_⟩,
    by simpa⟩
  rw [Nat.mul_mod_mod,←Nat.mul_assoc,show 359*389=210*665+1 by decide,Nat.add_mul,one_mul]
  rw [show 210*665*b = (210*b)*665 by ring,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt (by omega)]

theorem mem_iff {s : ℕ} : s ∈ centers ↔ ∃ b<647, candidate b=s := by
  refine ⟨?_,?_⟩
  · intro hs
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hs
    have lt : b<647 := by simpa using (List.mem_filter.mp hb).2
    exact ⟨b,lt,(fast_correct lt).symm⟩
  · rintro ⟨b,h,rfl⟩
    exact candidate_mem h

private def gap (a b : ℕ) : Prop := 977*a+X < 977*b
private instance (a b : ℕ) : Decidable (gap a b) := inferInstanceAs (Decidable (_ < _))
private instance : IsTrans ℕ gap := ⟨by intro a b c ab bc; unfold gap at *; omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
private theorem ordered : List.Chain' gap centers := by decide +kernel

private theorem spaced : List.Pairwise gap centers := (List.chain'_iff_pairwise (l:=centers) (R:=gap)).mp ordered

/-- Every two distinct legal centers, in increasing order, are more than X/977 apart. -/
theorem separation {a b : ℕ} (ha : a ∈ centers) (hb : b ∈ centers) (ab : a<b) :
    977*a+X < 977*b := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ha
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hb
  rcases lt_trichotomy i j with h|h|h
  · exact List.pairwise_iff_get.mp spaced i j h
  · subst j; omega
  · have g := List.pairwise_iff_get.mp spaced j i h
    unfold gap at g
    omega

/-- A certified small nonzero discrepancy rules out every exact smooth sum. -/
theorem nearby_not_exact {b S : ℕ} (hb : b<647) (ne : S≠candidate b)
    (lo : candidate b ≤ S+2^437) (hi : S ≤ candidate b+2^437)
    (j : ℕ) (hj : j<647) : S≠candidate j := by
  intro eq
  have mem : S∈centers := eq ▸ candidate_mem hj
  have tiny : 977*2^437<X := by decide +kernel
  rcases lt_or_gt_of_ne ne with less|larger
  · have sep := separation mem (candidate_mem hb) less
    omega
  · have sep := separation (candidate_mem hb) mem larger
    omega

/-- Using 976 in place of 977 would invalidate the gap guarantee. -/
theorem sharp_denominator : ∃ a ∈ centers, ∃ b ∈ centers, a<b ∧ 976*b≤976*a+X := by
  refine ⟨candidate 359,candidate_mem (by decide),candidate 53,candidate_mem (by decide),?_⟩
  rw [←fast_correct (show 359<647 by decide),←fast_correct (show 53<647 by decide)]
  decide +kernel

/-- The product screen is allowed to enlarge each end of its sum window by this amount. -/
def guard : ℕ := 2^1012

private def wide (a b : ℕ) : Bool := 9*(a+guard)^2 < 8*(b-guard)^2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
private theorem ledger : (centers.zipWith wide (centers.drop 56)).all id = true := by decide +kernel

private theorem zip_at {α : Type} {d : ℕ} (l : List α) (f : α → α → Bool)
    (all : (l.zipWith f (l.drop d)).all id = true) (i : ℕ) (hi : d+i<l.length) :
    f (l[i]'(by omega)) (l[d+i]'hi)=true := by
  have within : i<(l.zipWith f (l.drop d)).length := by
    rw [List.length_zipWith,List.length_drop]
    omega
  have atI := List.all_eq_true.mp all _ (List.getElem_mem within)
  simpa only [id_eq,List.getElem_zipWith,List.getElem_drop] using atI

private theorem center_mono (items : List ℕ) (order : items.Pairwise gap) {i j : ℕ}
    (near : i≤j) (hj : j < items.length) : items[i]'(near.trans_lt hj) ≤ items[j]'hj := by
  rcases eq_or_lt_of_le near with eq|lt
  · subst j; exact le_rfl
  · have g := List.pairwise_iff_getElem.mp order i j (near.trans_lt hj) hj lt
    unfold gap at g
    omega

private theorem far_of_ledger (items : List ℕ) (order : items.Pairwise gap)
    (proof : (items.zipWith wide (items.drop 56)).all id = true) (i j : ℕ)
    (hj : j < items.length) (apart : i+56≤j) :
    9*(items[i]'(by omega)+guard)^2 < 8*(items[j]'hj-guard)^2 := by
  have near : 56+i≤j := by omega
  have at56 := zip_at items wide proof i (near.trans_lt hj)
  have mono := center_mono items order near hj
  exact (of_decide_eq_true at56).trans_le
    (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.sub_le_sub_right mono guard) 2))

attribute [local irreducible] centers

/-- Public range tests on a proposed sum with an additive error tolerance. -/
def possible (N H c : ℕ) : Prop := 4*N≤(c+H)^2 ∧ 2*(c-H)^2≤9*N

private theorem index_span {N H i j : ℕ} (hH : H≤guard) (hi : i<centers.length)
    (hj : j<centers.length) (a : possible N H centers[i]) (b : possible N H centers[j]) :
    j < i+56 := by
  apply lt_of_not_ge
  intro apart
  have past := far_of_ledger centers spaced ledger i j hj apart
  obtain ⟨low,_⟩ := a
  obtain ⟨_,high⟩ := b
  have l := low.trans (Nat.pow_le_pow_left (Nat.add_le_add_left hH _) 2)
  have h := (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.sub_le_sub_left hH centers[j]) 2)).trans high
  omega

/-- For every public N, at most 56 distinct centers pass the balanced range test,
even if every candidate sum is broadened by up to 2^1012 on each side. -/
theorem balanced_card (N H : ℕ) (hH : H≤guard) (C : Finset ℕ)
    (valid : ∀ c ∈ C, c ∈ centers ∧ possible N H c) : C.card ≤ 56 := by
  classical
  choose idx eq using fun c : C => List.mem_iff_get.mp (valid c c.property).1
  let f (c : C) := (idx c).val
  have inj : Function.Injective f := by
    intro x y same
    have i := Fin.ext same
    exact Subtype.ext ((eq x).symm.trans (by rw [i,eq y]))
  let positions := Finset.univ.image f
  have span i (hi : i ∈ positions) j (hj : j ∈ positions) : j < i+56 := by
    obtain ⟨x,_,rfl⟩ := mem_image.mp hi
    obtain ⟨y,_,rfl⟩ := mem_image.mp hj
    apply index_span hH (idx x).isLt (idx y).isLt
    · simpa only [f,←List.get_eq_getElem,eq] using (valid x x.property).2
    · simpa only [f,←List.get_eq_getElem,eq] using (valid y y.property).2
  have bound : positions.card≤56 := by
    by_cases h : positions.Nonempty
    · let s := positions.min' h
      have inside : positions ⊆ Ico s (s+56) := fun j hj =>
        mem_Ico.mpr ⟨positions.min'_le _ hj,span s (positions.min'_mem h) j hj⟩
      simpa only [Nat.card_Ico,Nat.add_sub_cancel_left] using card_le_card inside
    · simp [Finset.not_nonempty_iff_eq_empty.mp h]
  simpa only [positions,card_image_of_injective _ inj,card_univ,Fintype.card_coe] using bound

/-- Only one center can lie close enough to the square-root boundary to make
a tolerance H≤X/65536 unstable. T is the publicly computable boundary 2√N. -/
theorem exceptional_unique {a b : ℕ} (ha : a∈centers) (hb : b∈centers) {T H : ℝ}
    (narrow : 65536*H ≤ X) (a0 : T-H≤a) (a1 : (a:ℝ)≤T+H+X/1024)
    (b0 : T-H≤b) (b1 : (b:ℝ)≤T+H+X/1024) : a=b := by
  have positive : 0<(X:ℝ) := by unfold X; positivity
  rcases lt_trichotomy a b with lt|eq|gt
  · have sep : 977*(a:ℝ)+(X:ℝ)<977*b := by exact_mod_cast separation ha hb lt
    linarith only [sep,a0,b1,narrow,positive]
  · exact eq
  · have sep : 977*(b:ℝ)+(X:ℝ)<977*a := by exact_mod_cast separation hb ha gt
    linarith only [sep,b0,a1,narrow,positive]

private theorem away_ratio {S D T L : ℝ} (dp : 0≤D) (tp : 0≤T)
    (cap : S≤2*L) (away : L≤1024*(S-T)) (disc : D^2=S^2-T^2) : S≤33*D := by
  have condition : 2048*T≤2047*S := by linarith only [cap,away]
  have square := mul_self_le_mul_self (show 0≤2048*T by positivity) condition
  have sqle : S^2≤(33*D)^2 := by
    nlinarith only [square,disc,sq_nonneg S]
  nlinarith only [sqle,dp,sq_nonneg (S-33*D)]

/-- Any two larger-factor values from the same nonexceptional sum band differ
by at most 34H. The two pairs may be real, so this also bounds the full
continuous inverse image used for an integer factor window. -/
theorem outside_width {L T H C p q r s : ℝ} (product : p*q=r*s) (boundary : T^2=4*p*q)
    (tp : 0≤T) (pp : 0<p) (rp : 0≤r) (pq : p≤q) (qs : q≤s)
    (maxq : q≤L) (outside : T+H+L/1024≤C) (left : C-H≤p+q)
    (right : r+s≤C+H) : s-q ≤ 34*H := by
  have qpos := pp.trans_le pq
  have ratio := away_ratio (S:=p+q) (D:=q-p) (T:=T) (L:=L)
    (sub_nonneg.mpr pq) tp (by linarith only [pq,maxq])
    (by linarith only [outside,left]) (by nlinarith only [boundary])
  have cross := mul_le_mul_of_nonneg_left qs rp
  have rle : r≤p := by
    apply le_of_mul_le_mul_right (a:=q) _ qpos
    linarith only [cross,product]
  have slope : q≤17*(q-r) := by linarith only [ratio,rle]
  have secant : q*((r+s)-(p+q))=(q-r)*(s-q) := by linear_combination -product
  have h := mul_le_mul_of_nonneg_right slope (sub_nonneg.mpr qs)
  have span : (r+s)-(p+q)≤2*H := by linarith only [right,left]
  apply le_of_mul_le_mul_left (a:=q) _ qpos
  nlinarith only [h,secant,mul_le_mul_of_nonneg_left span qpos.le]

end PrimeFactors.SmoothCenterSpacing
