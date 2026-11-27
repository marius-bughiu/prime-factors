import PrimeFactors.PrimitiveIntervalCandidateBand

/-! Exact endpoints for the factor-sum interval of a supplied reading. Two
integer square roots and a residue adjustment suffice to reach any candidate. -/
namespace PrimeFactors.PrimitiveIntervalBandEndpoints

open Finset PrimitiveIntervalMoment PrimitiveIntervalCandidateBand

def radicand (n b : ℕ) (v : ℤ) : ℤ := v+2*n-2*b-1

/-- The least nonnegative integer whose square is at least z. The subtraction
of one includes a lower endpoint that is already an exact square. -/
def lowerRoot (z : ℤ) : ℕ := if z ≤ 0 then 0 else (z-1).toNat.sqrt+1

def lower (n b : ℕ) (v : ℤ) (e : ℕ) : ℕ :=
  max (2*b+2) (b+1+lowerRoot (radicand n b v-e))

def upper (n b : ℕ) (v : ℤ) (e : ℕ) : ℕ :=
  min (4*b+2) (b+1+(radicand n b v+e).toNat.sqrt)

/-- First integer of the required residue at or beyond the lower bound.
It can exceed the upper bound, in which case there are no candidates. -/
def first (n b : ℕ) (v : ℤ) (e : ℕ) : ℕ :=
  let l := lower n b v e
  l + ((n+1)%4+4-l%4)%4

def count (n b : ℕ) (v : ℤ) (e : ℕ) : ℕ :=
  let l := first n b v e
  let u := upper n b v e
  if 0 ≤ radicand n b v+e ∧ l ≤ u then (u-l)/4+1 else 0

private theorem upperRoot_iff (x : ℕ) (z : ℤ) :
    (x:ℤ)^2 ≤ z ↔ 0 ≤ z ∧ x ≤ z.toNat.sqrt := by
  by_cases h : 0 ≤ z
  · lift z to ℕ using h
    rw [Int.toNat_natCast,Nat.le_sqrt']
    exact ⟨fun le => ⟨by positivity,by exact_mod_cast le⟩,fun h => by exact_mod_cast h.2⟩
  · exact ⟨fun le => (h ((sq_nonneg _).trans le)).elim,fun good => (h good.1).elim⟩

theorem lowerRoot_iff (x : ℕ) (z : ℤ) : lowerRoot z ≤ x ↔ z ≤ (x:ℤ)^2 := by
  by_cases h : z ≤ 0
  · simp only [lowerRoot,if_pos h,zero_le,true_iff]
    exact h.trans (sq_nonneg _)
  · rw [lowerRoot,if_neg h]
    have bounds := upperRoot_iff x (z-1)
    omega

/-- The supplied error bound is equivalent to two inequalities for the
nonnegative distance x from B+1. -/
theorem square_window {n b s e : ℕ} {v : ℤ} (side : b+1 ≤ s) :
    |value n b s-v| ≤ e ↔
      radicand n b v-e ≤ ((s-(b+1):ℕ):ℤ)^2 ∧
      ((s-(b+1):ℕ):ℤ)^2 ≤ radicand n b v+e := by
  have eq : value n b s-v = ((s-(b+1):ℕ):ℤ)^2-radicand n b v := by
    unfold value radicand
    push_cast [Nat.cast_sub side]
    ring
  rw [eq,abs_le]
  omega

/-- Intersect the two roots with the prior sum interval and the public
residue class. A negative upper radicand explicitly gives an empty set. -/
theorem mem_endpoints {n b s e : ℕ} {v : ℤ} :
    s ∈ candidates n b v e ↔ 0 ≤ radicand n b v+e ∧
      lower n b v e ≤ s ∧ s ≤ upper n b v e ∧ s%4=(n+1)%4 := by
  rw [mem_candidates,lower,upper,max_le_iff,le_min_iff]
  constructor
  · rintro ⟨⟨l,u⟩,r,err⟩
    obtain ⟨bot,top⟩ := (square_window (by omega : b+1 ≤ s)).mp err
    have lb := (lowerRoot_iff ..).mpr bot
    obtain ⟨pos,ub⟩ := (upperRoot_iff ..).mp top
    exact ⟨pos,⟨l,by omega⟩,⟨u,by omega⟩,r⟩
  · rintro ⟨pos,⟨l,lb⟩,⟨u,ub⟩,r⟩
    refine ⟨⟨l,u⟩,r,(square_window (by omega : b+1 ≤ s)).mpr ?_⟩
    exact ⟨(lowerRoot_iff ..).mp (by omega),(upperRoot_iff ..).mpr ⟨pos,by omega⟩⟩

theorem negative_empty {n b e : ℕ} {v : ℤ} (neg : radicand n b v+e < 0) :
    candidates n b v e = ∅ :=
  Finset.eq_empty_iff_forall_not_mem.mpr fun _ hs => (not_le_of_gt neg) (mem_endpoints.mp hs).1

/-- Zero-based random access to the set. The candidate at rank k is
first+4k. The formula checks rank validity without enumerating a Finset. -/
theorem mem_rank {n b s e : ℕ} {v : ℤ} :
    s ∈ candidates n b v e ↔ ∃ k < count n b v e, s=first n b v e+4*k := by
  rw [mem_endpoints]
  let l := lower n b v e
  let f := first n b v e
  let u := upper n b v e
  have align : l ≤ f ∧ f < l+4 ∧ f%4=(n+1)%4 := by dsimp only [f,first,l]; omega
  change (0 ≤ radicand n b v+e ∧ l ≤ s ∧ s ≤ u ∧ s%4=(n+1)%4) ↔
    ∃ k < (if 0 ≤ radicand n b v+e ∧ f ≤ u then (u-f)/4+1 else 0), s=f+4*k
  split_ifs with h
  · constructor
    · rintro ⟨_,lo,hi,res⟩
      refine ⟨(s-f)/4,by omega,by omega⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨h.1,by omega,by omega,by omega⟩
  · constructor
    · rintro ⟨p,lo,hi,res⟩
      exact (h ⟨p,by omega⟩).elim
    · omega

theorem card_eq_count (n b : ℕ) (v : ℤ) (e : ℕ) :
    (candidates n b v e).card = count n b v e := by
  have eq : candidates n b v e = (range (count n b v e)).image (fun k => first n b v e+4*k) := by
    ext s
    rw [mem_rank,mem_image]
    simp only [mem_range,eq_comm (a:=s)]
  rw [eq,card_image_of_injective _ (by intro i j h; dsimp only at h; omega),card_range]

/-- On the 39-bit synthetic reading, each root is checked between its
adjacent integer squares. The range has five ranks, beginning at 1,310,538. -/
theorem control39 :
    lower 419636024497 458058 (-112538867588) 16000000=1310536 ∧
    upper 419636024497 458058 (-112538867588) 16000000=1310554 ∧
    first 419636024497 458058 (-112538867588) 16000000=1310538 ∧
    count 419636024497 458058 (-112538867588) 16000000=5 := by
  have l : Nat.sqrt 726716265288=852476 := (Nat.eq_sqrt'.mpr (by decide +kernel)).symm
  have u : Nat.sqrt 726748265289=852495 := (Nat.eq_sqrt'.mpr (by decide +kernel)).symm
  have a : radicand 419636024497 458058 (-112538867588)=726732265289 := by decide +kernel
  have bot : lower 419636024497 458058 (-112538867588) 16000000=1310536 := by
    rw [lower,a,lowerRoot,if_neg (by decide +kernel),
      show ((726732265289:ℤ)-(16000000:ℕ)-1).toNat=726716265288 by decide +kernel,l]
    decide +kernel
  have top : upper 419636024497 458058 (-112538867588) 16000000=1310554 := by
    rw [upper,a,show ((726732265289:ℤ)+(16000000:ℕ)).toNat=726748265289 by decide +kernel,u]
    decide +kernel
  have start : first 419636024497 458058 (-112538867588) 16000000=1310538 := by
    rw [first,bot]
  refine ⟨bot,top,start,?_⟩
  rw [count,start,top]
  decide +kernel

end PrimeFactors.PrimitiveIntervalBandEndpoints
