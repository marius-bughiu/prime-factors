import PrimeFactors.ChebyshevQuarticScale
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Matrix.Notation

namespace PrimeFactors.ProjectedSweepBudget
open Finset

set_option exponentiation.threshold 4096

/-- Number of levels tested when the full interval of multiples of M in
[C-S,C+S] is scanned. The two integer divisions round down, including at
negative endpoints. -/
noncomputable def levelCount (C : ℤ) (S M : ℕ) : ℕ :=
  (((S:ℤ)+C)/(M:ℤ)+((S:ℤ)-C)/(M:ℤ)+1).toNat

theorem levelCount_lower (C : ℤ) (S M : ℕ) (pos : 0<M) :
    2*S/M ≤ levelCount C S M := by
  have pm : 0<(M:ℤ) := by exact_mod_cast pos
  have a := Int.emod_lt_of_pos ((S:ℤ)+C) pm
  have b := Int.emod_lt_of_pos ((S:ℤ)-C) pm
  have ea := Int.emod_add_ediv ((S:ℤ)+C) (M:ℤ)
  have eb := Int.emod_add_ediv ((S:ℤ)-C) (M:ℤ)
  have lt : 2*(S:ℤ)/(M:ℤ) < (((S:ℤ)+C)/(M:ℤ)+((S:ℤ)-C)/(M:ℤ)+2)*(1:ℤ) := by
    rw [mul_one, Int.ediv_lt_iff_lt_mul pm]
    nlinarith only [a,b,ea,eb]
  have cast : ((2*S/M:ℕ):ℤ) = 2*(S:ℤ)/(M:ℤ) := by push_cast; rfl
  unfold levelCount
  omega

/-- Two arbitrary residues are permitted at each query, which in particular
allows swapping the putative factors. -/
structure Query where
  exponent : ℕ
  allowed : exponent ≤ 600
  u : ℕ
  v : ℕ
  constant : ℤ
  coeff : Fin 4 → ℤ
  nonzero : ∃ i, coeff i ≠ 0

noncomputable def Query.spread (q : Query) (weight : Fin 4 → ℕ) : ℕ :=
  ∑ i, (q.coeff i).natAbs*weight i

noncomputable def Query.levels (q : Query) (weight : Fin 4 → ℕ) : ℕ :=
  levelCount q.constant (q.spread weight) (360*(2^q.exponent)^4)

/-- One accounting unit is charged per block of up to 65,536 positions.
Taking the maximum charges at least one lattice even for empty intervals. -/
noncomputable def Query.blocks (q : Query) (weight : Fin 4 → ℕ) : ℕ := (q.levels weight+65535)/65536

noncomputable def Query.work (q : Query) (weight : Fin 4 → ℕ) : ℕ := max 1 (q.blocks weight)

private theorem blocks_cover (q : Query) (weight : Fin 4 → ℕ) :
    q.levels weight ≤ 65536*q.blocks weight := by unfold Query.blocks; omega

private theorem spread_lower (q : Query) (weight : Fin 4 → ℕ) {w : ℕ}
    (low : ∀ i, w ≤ weight i) : w ≤ q.spread weight := by
  obtain ⟨i,hi⟩ := q.nonzero
  exact (low i).trans ((Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr hi)).trans
    (Finset.single_le_sum (fun j _ => Nat.zero_le ((q.coeff j).natAbs*weight j)) (mem_univ i)))

private theorem levels_at_small_radius (q : Query) (weight : Fin 4 → ℕ) {w goal : ℕ}
    (low : ∀ i, w ≤ weight i) (mass : 360*2^1009 ≤ 2*w)
    (small : q.exponent ≤ goal) (budget : 16+goal+3*q.exponent ≤ 1009) :
    2^(goal-q.exponent) ≤ q.blocks weight := by
  have bound : 65536*2^(goal-q.exponent)*(360*(2^q.exponent)^4) ≤ 360*2^1009 := by
    calc
      _ = 360*(2:ℕ)^(16+(goal-q.exponent)+q.exponent*4) := by
        rw [pow_add, pow_add, pow_mul]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
  have h := (Nat.le_div_iff_mul_le (by positivity : 0<360*(2^q.exponent)^4)).mpr
    (bound.trans (mass.trans (Nat.mul_le_mul_left 2 (spread_lower q weight low))))
  have hl := h.trans (levelCount_lower q.constant (q.spread weight) _ (by positivity))
  have last := hl.trans (blocks_cover q weight)
  omega

private theorem radix_cost (q : Query) (weight : Fin 4 → ℕ) {w : ℕ}
    (low : ∀ i, w ≤ weight i) (mass : 360*2^1009 ≤ 2*w) :
    2^249 ≤ q.work weight*2^q.exponent := by
  by_cases small : q.exponent ≤ 248
  · have h := (levels_at_small_radius q weight low mass (goal:=249) (by omega)
      (by omega)).trans (le_max_right 1 (q.blocks weight))
    have := Nat.mul_le_mul_right (2^q.exponent) h
    rwa [← pow_add, Nat.sub_add_cancel (by omega : q.exponent ≤ 249)] at this
  · have h : 1 ≤ q.work weight := le_max_left ..
    exact (Nat.pow_le_pow_right (by decide) (by omega : 249 ≤ q.exponent)).trans
      (Nat.le_mul_of_pos_left _ h)

/-- All lifts of one residue to the 600-bit word. -/
noncomputable def lifts (e u : ℕ) : Finset ℕ := (range (2^(600-e))).image (fun j => u+2^e*j)

theorem mem_lifts {e u x : ℕ} (he : e ≤ 600) (bound : x<2^600) (same : x%2^e=u) :
    x ∈ lifts e u := by
  apply mem_image.mpr
  refine ⟨x/2^e, mem_range.mpr ((Nat.div_lt_iff_lt_mul (by positivity)).mpr ?_), ?_⟩
  · rwa [← pow_add, Nat.sub_add_cancel he]
  · rw [← same, Nat.mod_add_div]

noncomputable def Query.covered (q : Query) : Finset ℕ := lifts q.exponent q.u ∪ lifts q.exponent q.v

private theorem lifts_card (e u : ℕ) : (lifts e u).card ≤ 2^(600-e) := by
  simpa [lifts] using (Finset.card_image_le (s:=range (2^(600-e))) (f:=fun j => u+2^e*j))

private theorem coverage_budget (q : Query) (cost k : ℕ) (hk : k ≤ 601)
    (price : 2^k ≤ cost*2^q.exponent) : q.covered.card ≤ 2^(601-k)*cost := by
  have h := (card_union_le (lifts q.exponent q.u) (lifts q.exponent q.v)).trans
    (Nat.add_le_add (lifts_card ..) (lifts_card ..))
  refine h.trans ?_
  apply Nat.le_of_mul_le_mul_left (c:=2^q.exponent) _ (by positivity)
  calc
    _ = 2*(2:ℕ)^(q.exponent+(600-q.exponent)) := by rw [pow_add]; ring
    _ = 2^601 := by rw [Nat.add_sub_of_le q.allowed]; exact (pow_succ' (2:ℕ) 600).symm
    _ = 2^(601-k)*2^k := by rw [← pow_add, Nat.sub_add_cancel hk]
    _ ≤ 2^(601-k)*(cost*2^q.exponent) := Nat.mul_le_mul_left _ price
    _ = _ := by ring

noncomputable def oddWords : Finset ℕ := (range (2^599)).image (fun i => 2*i+1)

theorem mem_oddWords {x : ℕ} : x ∈ oddWords ↔ x<2^600 ∧ Odd x := by
  rw [show (2:ℕ)^600=2*2^599 by decide +kernel]
  constructor
  · intro hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    have h := mem_range.mp hi
    exact ⟨by omega,i,by omega⟩
  · rintro ⟨hx,i,hi⟩
    exact mem_image.mpr ⟨i,mem_range.mpr (by omega),by omega⟩

private theorem oddWords_card : oddWords.card = 2^599 := by
  rw [oddWords,card_image_of_injective _ (fun x y eq => by change 2*x+1=2*y+1 at eq; omega),card_range]

private theorem schedule_budget {ι : Type*} (schedule : Finset ι) (q : ι → Query) (cost : ι → ℕ)
    (k : ℕ) (hk : 2 ≤ k ∧ k ≤ 601) (price : ∀ i ∈ schedule, 2^k ≤ cost i*2^(q i).exponent)
    (covers : oddWords ⊆ schedule.biUnion (fun i => (q i).covered)) :
    2^(k-2) ≤ ∑ i ∈ schedule, cost i := by
  have h := (card_le_card covers).trans (card_biUnion_le.trans (sum_le_sum
    (fun i hi => coverage_budget (q i) (cost i) k hk.2 (price i hi))))
  rw [oddWords_card, ← Finset.mul_sum] at h
  apply Nat.le_of_mul_le_mul_left (c:=2^(601-k)) _ (by positivity)
  rwa [← pow_add, show (601-k)+(k-2)=599 by omega]

/-- Every complete sweep of the odd 600-bit remainders has this cost even
when queries use different dyadic radii and their covered sets overlap. -/
theorem full_sweep {ι : Type*} (schedule : Finset ι) (q : ι → Query) (weight : Fin 4 → ℕ)
    {w : ℕ} (low : ∀ i, w ≤ weight i) (mass : 360*2^1009 ≤ 2*w)
    (covers : oddWords ⊆ schedule.biUnion (fun i => (q i).covered)) :
    2^247 ≤ ∑ i ∈ schedule, (q i).work weight := by
  exact schedule_budget schedule q _ 249 (by decide) (fun i _ => radix_cost (q i) weight low mass) covers

/-- Counting each lattice separately from every scanned block charges one
additional operation when both are performed. -/
noncomputable def Query.separateWork (q : Query) (weight : Fin 4 → ℕ) : ℕ := 1+q.blocks weight

private theorem additive_price (q : Query) (weight : Fin 4 → ℕ) {w : ℕ}
    (low : ∀ i, w ≤ weight i) (mass : 360*(2*65536+1)*(2^248)^4 ≤ 2*w) :
    2^250 ≤ q.separateWork weight*2^q.exponent := by
  have weak := (show 360*2^1009 ≤ 360*(2*65536+1)*(2^248)^4 by decide +kernel).trans mass
  have pos : 0<360*(2^q.exponent)^4 := by positivity
  have bench := (levelCount_lower q.constant (q.spread weight) (360*(2^q.exponent)^4)
    (by positivity)).trans (blocks_cover q weight)
  have need (n : ℕ) (bound : n*(360*(2^q.exponent)^4) ≤ 360*(2*65536+1)*(2^248)^4) :
      n ≤ 65536*q.blocks weight :=
    ((Nat.le_div_iff_mul_le pos).mpr (bound.trans (mass.trans (Nat.mul_le_mul_left _ (spread_lower q weight low))))).trans bench
  by_cases small : q.exponent ≤ 247
  · have h := levels_at_small_radius q weight low weak (goal:=250) (by omega) (by omega)
    have h' : 2^(250-q.exponent) ≤ q.separateWork weight := by unfold Query.separateWork; omega
    have full := Nat.mul_le_mul_right (2^q.exponent) h'
    rwa [← pow_add, Nat.sub_add_cancel (by omega : q.exponent ≤ 250)] at full
  by_cases large : 250 ≤ q.exponent
  · exact (Nat.pow_le_pow_right (by decide) large).trans
      (Nat.le_mul_of_pos_left _ (by unfold Query.separateWork; omega))
  rcases (by omega : q.exponent=248 ∨ q.exponent=249) with eq|eq
  · have h := need 131073 (by rw [eq]; decide +kernel)
    have h' : 4 ≤ q.separateWork weight := by unfold Query.separateWork; omega
    rw [eq]
    exact le_trans (show 2^250 ≤ 4*2^248 by decide +kernel) (Nat.mul_le_mul_right (2^248) h')
  · have h := need 1 (by rw [eq]; decide +kernel)
    have h' : 2 ≤ q.separateWork weight := by unfold Query.separateWork; omega
    rw [eq]
    exact le_trans (show 2^250 ≤ 2*2^249 by decide +kernel) (Nat.mul_le_mul_right (2^249) h')

/-- The same product-only equal-width windows as the current positive scanner,
specialized to two 1,024-bit factors. -/
noncomputable def windowWeights (N : ℕ) : Fin 4 → ℕ :=
  let first := 2^1023
  let last := 2^1024-1
  let L := max first ((N+last-1)/last)
  let U := min last (N/first)
  let s := max 1 ((U+N/U-(1+(4*N-1).sqrt)+3)/4)
  let H := max 1 ((U-L+1)/2)
  ![2*s,H,2*s^2,2*H*s]

private theorem fresh_mass : ∀ i, 360*(2*65536+1)*(2^248)^4 ≤ 2*windowWeights ChebyshevQuarticScale.fresh i := by
  let k : ℕ := 316654078353932669430896568039437646948995827324355950320885992018878621339882034859352160800370012849546508284505165782514386059318538454140190240579600679710842127862944181242520006361222093577810698295926626034770148286024885798179904628489506435612856553841327654419558392803832226047978898967565521689258
  have sq : k=(4*ChebyshevQuarticScale.fresh-1).sqrt := Nat.eq_sqrt.mpr (by decide +kernel)
  unfold windowWeights
  rw [← sq]
  decide +kernel

/-- The fresh product satisfies the width hypothesis using its public digits. -/
theorem fresh_full_sweep {ι : Type*} (schedule : Finset ι) (q : ι → Query)
    (covers : oddWords ⊆ schedule.biUnion (fun i => (q i).covered)) :
    2^247 ≤ ∑ i ∈ schedule, (q i).work (windowWeights ChebyshevQuarticScale.fresh) := by
  apply full_sweep schedule q _ (w:=180*2^1009) _ (by decide +kernel) covers
  intro i
  have := (show 360*2^1009 ≤ 360*(2*65536+1)*(2^248)^4 by decide +kernel).trans (fresh_mass i)
  omega

/-- Counting lattices and blocks separately gives the stronger fresh bound. -/
theorem fresh_separate_sweep {ι : Type*} (schedule : Finset ι) (q : ι → Query)
    (covers : oddWords ⊆ schedule.biUnion (fun i => (q i).covered)) :
    2^248 ≤ ∑ i ∈ schedule, (q i).separateWork (windowWeights ChebyshevQuarticScale.fresh) := by
  apply schedule_budget schedule q _ 250 (by decide) _ covers
  intro i _
  apply additive_price (q i) _ (w:=180*(2*65536+1)*(2^248)^4) _ (by decide +kernel)
  intro j
  have := fresh_mass j
  omega

end PrimeFactors.ProjectedSweepBudget
