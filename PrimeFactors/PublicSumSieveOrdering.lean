import PrimeFactors.PublicSumSieveControl
import PrimeFactors.FiniteFilterWork

/-! On the published 7,273-position window, order the same thirteen tests
by their exact passing fractions over full periods. Work counts one lookup
for each surviving position presented to the next test. -/

open private PrimeFactors.PublicSumSieveControl.rows PrimeFactors.PublicSumSieveControl.packed
  PrimeFactors.PublicSumSieveControl.packed_iff PrimeFactors.PublicSumSieveControl.pop
  PrimeFactors.PublicSumSieveControl.pop_eq PrimeFactors.PublicSumSieveControl.row_certificate
  PrimeFactors.PublicSumSieveControl.repeated_iff from PrimeFactors.PublicSumSieveControl

namespace PrimeFactors.PublicSumSieveOrdering

open LevelMaskCertificate FiniteFilterWork

abbrev Row := ℕ × ℕ
abbrev ascendingOrder := PrimeFactors.PublicSumSieveControl.rows
private abbrev packed := PrimeFactors.PublicSumSieveControl.packed

/-- Reorder the verified row indices, reusing the original masks. -/
noncomputable def densityOrder : List Row :=
  [1,3,8,10,11,12,9,7,6,5,4,2,0].map (fun i => ascendingOrder[i]!)

theorem same_rows : densityOrder.Perm ascendingOrder := by
  apply List.isPerm_iff.mp
  decide +kernel

theorem prime_order : densityOrder.map Prod.fst = [5,11,29,37,41,43,31,23,19,17,13,7,3] := by
  decide +kernel

/-- Number of acceptable positions over one whole residue period. -/
noncomputable def periodHits (r : Row) : ℕ := (List.range r.1).countP r.2.testBit

/-- Cross multiplication compares the exact rational fractions of passing residues. -/
theorem densities_increasing :
    densityOrder.Pairwise (fun r s => periodHits r * s.1 < periodHits s * r.1) := by
  decide +kernel

/-- One scalar lookup using the position modulo the prime. -/
def lookup (r : Row) (i : ℕ) : Bool := r.2.testBit (i%r.1)

/-- Enumerate the surviving positions. The original packed mask clips the padding. -/
noncomputable def positions (ls : List Row) : List ℕ :=
  (List.range 8192).filter (packed ls).testBit

private theorem positions_length (ls : List Row) : (positions ls).length =
    PrimeFactors.PublicSumSieveControl.pop 10 (packed ls) := by
  rw [PrimeFactors.PublicSumSieveControl.pop_eq, positions, List.countP_eq_length_filter]
  rfl

private theorem append_bit (ls : List Row) (r : Row) (i : ℕ) :
    (packed (ls++[r])).testBit i =
      ((repeatWord r.1 r.2 12).testBit i && (packed ls).testBit i) := by
  induction ls with
  | nil => exact Nat.testBit_and ..
  | cons a rest ih =>
    simp only [List.cons_append, packed, PrimeFactors.PublicSumSieveControl.packed,
      Nat.testBit_and] at ih ⊢
    rw [ih, Bool.and_left_comm]

private theorem extend (ls : List Row) (r : Row) (sub : ls ⊆ ascendingOrder) (hr : r ∈ ascendingOrder) :
    (positions ls).filter (lookup r) = positions (ls++[r]) := by
  rw [positions, positions, List.filter_filter]
  apply List.filter_congr
  intro i _
  rw [append_bit]
  by_cases bit : (packed ls).testBit i = true
  · have hi := ((PrimeFactors.PublicSumSieveControl.packed_iff ls sub i).mp bit).1
    obtain ⟨_,small,room,_⟩ := PrimeFactors.PublicSumSieveControl.row_certificate r hr
    have eq := PrimeFactors.PublicSumSieveControl.repeated_iff small 12 i
    have h : i < r.1*2^12 := hi.trans_le room
    simp only [h, true_and] at eq
    simp only [lookup,bit,Bool.and_true]
    exact Bool.eq_iff_iff.mpr eq.symm
  · simp [Bool.eq_false_iff.mpr bit]

/-- Prefix sizes are exactly the counts of scalar lookups charged at each test. -/
private theorem work_from (ls prior : List Row) (hs : ls ⊆ ascendingOrder) (hp : prior ⊆ ascendingOrder) :
    work (positions prior) (ls.map lookup) =
      ((List.range ls.length).map (fun k => (positions (prior++ls.take k)).length)).sum := by
  induction ls generalizing prior with
  | nil => simp [work]
  | cons r rest ih =>
    have hr := hs (by simp : r ∈ r::rest)
    have sub : rest ⊆ ascendingOrder := fun _ h => hs (List.mem_cons_of_mem _ h)
    have both : prior++[r] ⊆ ascendingOrder := List.append_subset.mpr ⟨hp, by simpa using hr⟩
    simp only [List.map_cons, work, List.length_cons, List.range_succ_eq_map, List.sum_cons,
      List.map_map, List.take_zero, List.append_nil, extend prior r hp hr, ih _ sub both]
    simp [Function.comp_def,List.append_assoc]

noncomputable def stageSizes (ls : List Row) : List ℕ :=
  (List.range (ls.length+1)).map (fun k => (positions (ls.take k)).length)

theorem density_sizes : stageSizes densityOrder =
    [7273,2909,1323,638,310,143,75,37,13,5,2,2,1,1] := by
  simp only [stageSizes,positions_length]
  decide +kernel

private theorem work_plus_last (ls : List Row) (sub : ls ⊆ ascendingOrder) :
    work (positions []) (ls.map lookup) + (positions ls).length = (stageSizes ls).sum := by
  rw [work_from ls [] sub (by simp),stageSizes,List.range_succ,List.map_append,List.sum_append]
  simp

private theorem packed_perm {xs ys : List Row} (h : xs.Perm ys) : packed xs = packed ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [packed, PrimeFactors.PublicSumSieveControl.packed] at ih ⊢; rw [ih]
  | swap =>
    simp only [packed, PrimeFactors.PublicSumSieveControl.packed, ←Nat.and_assoc]
    rw [Nat.and_comm (repeatWord ..) (repeatWord ..)]
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

/-- All thirteen tests give the same positions in either order. -/
theorem same_positions : positions densityOrder = positions ascendingOrder := by
  simp only [positions, packed_perm same_rows]

/-- Filtering in density order also leaves exactly the known sum. -/
theorem final_sum (s : ℕ) :
    s ∈ (positions densityOrder).map (fun i => 1295590+4*i) ↔ s=1310542 := by
  rw [same_positions]
  change s ∈ PublicSumSieveControl.stage 13 ↔ _
  rw [PublicSumSieveControl.mem_stage, PublicSumSieveControl.through43]

/-- Both totals count the complete scalar sieve, including checks on the final survivor. -/
theorem scalar_work : work (positions []) (ascendingOrder.map lookup) = 16226 ∧
    work (positions []) (densityOrder.map lookup) = 12731 := by
  have ascending : stageSizes ascendingOrder =
      [7273,4849,1939,1108,505,271,141,72,38,14,7,6,3,1] := by
    simpa only [stageSizes,positions, PublicSumSieveControl.stage,List.length_map] using
      PublicSumSieveControl.stage_counts
  have last : (positions ascendingOrder).length=1 := by rw [positions_length]; decide +kernel
  have a := work_plus_last ascendingOrder (fun _ h => h)
  have b := work_plus_last densityOrder same_rows.subset
  rw [ascending,last] at a
  rw [density_sizes,same_positions,last] at b
  norm_num at a b
  omega

/-- In the actual prefix window, the two adjacent tests are ranked the other way.
Prime 41 passes 24 fewer positions than 37 among the 638 reaching them. -/
theorem partial_period_reversal :
    (positions (densityOrder.take 3)).length = 638 ∧
    (positions (densityOrder.take 4)).length = 310 ∧
    (positions (densityOrder.take 3 ++ [ascendingOrder[11]!])).length = 286 ∧
    periodHits ascendingOrder[10]! * 41 < periodHits ascendingOrder[11]! * 37 := by
  simp only [positions_length]
  decide +kernel

/-- Interchanging 37 and 41 saves exactly 24 scalar lookups, for any continuation. -/
theorem reversal_saves_24 (rest : List (ℕ → Bool)) :
    work (positions (densityOrder.take 3)) (lookup ascendingOrder[10]! :: lookup ascendingOrder[11]! :: rest) =
      work (positions (densityOrder.take 3)) (lookup ascendingOrder[11]! :: lookup ascendingOrder[10]! :: rest) + 24 := by
  have sub : densityOrder.take 3 ⊆ ascendingOrder :=
    fun _ h => same_rows.subset (List.mem_of_mem_take h)
  have c := swap_cost (positions (densityOrder.take 3)) (lookup ascendingOrder[10]!)
    (lookup ascendingOrder[11]!) rest
  rw [extend _ _ sub (by decide +kernel), extend _ _ sub (by decide +kernel)] at c
  have a : (positions (densityOrder.take 3 ++ [ascendingOrder[10]!])).length = 310 :=
    partial_period_reversal.2.1
  have b := partial_period_reversal.2.2.1
  omega

end PrimeFactors.PublicSumSieveOrdering
