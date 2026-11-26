import PrimeFactors.ReciprocalSumSlice
import PrimeFactors.NearSmoothExclusion

/-! Retain the proved whole-band saving under clipping to a terminal interval.
The same full-block masks can be reused when the leftmost block is partial. -/
namespace PrimeFactors.ReciprocalSumTail

open Finset ReciprocalSumSlice

/-- Exactly those discarded sites that belonged to the caller's ordinary wheel. -/
noncomputable def cut (n L t : ℤ) := ordinary L t ∩ removed n t

private theorem shape {n t : ℤ} (large : (2:ℤ)^24≤t) (ceil : n<(t+1)^2)
    {i : ℕ} (ii : i<blockCount t) :
    0<blockStart t i ∧ blockStart t i+843≤t ∧ 2401*n≤2500*(blockStart t i)^2 := by
  have bound : 49*(t+1)≤50*blockStart t i := by unfold blockStart blockCount at *; omega
  have square := pow_le_pow_left₀ (by omega : 0≤49*(t+1)) bound 2
  exact ⟨by omega, by unfold blockStart; omega,by nlinarith only [square,ceil]⟩

private theorem subset_ordinary {L A B t : ℤ} (lo : L≤A) (hi : B≤t) :
    ordinary A B ⊆ ordinary L t := by
  intro x hx
  obtain ⟨xb,flag⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨Icc_subset_Icc lo hi xb,flag⟩

/-- Every full block inside the requested suffix contributes at least 384
distinct discarded sites. -/
theorem full_blocks {n t L : ℤ} (large : 2^24≤t) (ceil : n<(t+1)^2) {k : ℕ}
    (cap : k≤blockCount t) (fit : 844*(k:ℤ)≤t+1-L) : 384*k ≤ (cut n L t).card := by
  let blocks := (range k).biUnion (dropped n t)
  have inside : blocks⊆cut n L t := by
    intro x hx
    obtain ⟨i,hi,drop⟩ := mem_biUnion.mp hx
    have ii := mem_range.mp hi
    have inRange := subset_ordinary (by unfold blockStart; omega : L≤blockStart t i)
      (by unfold blockStart; omega : blockStart t i+843≤t) (mem_sdiff.mp drop).1
    exact mem_inter.mpr ⟨inRange,mem_biUnion.mpr ⟨i,mem_range.mpr (ii.trans_le cap),drop⟩⟩
  have disjoint : (↑(range k) : Set ℕ).PairwiseDisjoint (dropped n t) := by
    intro i _ j _ ne
    apply disjoint_left.mpr
    intro x hx hy
    have ix := mem_Icc.mp (mem_filter.mp (mem_sdiff.mp hx).1).1
    have jx := mem_Icc.mp (mem_filter.mp (mem_sdiff.mp hy).1).1
    unfold blockStart at ix jx
    omega
  apply le_trans _ (card_le_card inside)
  change 384*k≤((range k).biUnion (dropped n t)).card
  rw [card_biUnion disjoint]
  calc
    384*k = ∑ _i ∈ range k,(384:ℕ) := by simp [Nat.mul_comm]
    _ ≤ _ := by
      apply sum_le_sum
      intro i hi
      obtain ⟨pos,_,near⟩ := shape large ceil ((mem_range.mp hi).trans_le cap)
      let a := blockStart t i
      let kept := oddSites a (a+843) (lanes n (lower n (a+843)) (upper n a))
      have upper := position_bound pos (by omega : a≤a+843) near (by omega)
      change kept.card≤36 at upper
      have cost := card_le_card_sdiff_add_card (s:=ordinary a (a+843)) (t:=kept)
      rw [ordinary_full] at cost
      change 384 ≤ (ordinary a (a+843) \ kept).card
      omega

/-- Certify a concrete integer percentage by checking only the endpoints and
the number of complete blocks. Each ordinary site is odd, and each full block
contributes 384 distinct discards. No large interval enumeration is needed. -/
theorem percentage_of_margin {n t L : ℤ} {k z : ℕ} (large : 2^24≤t)
    (ceil : n<(t+1)^2) (cap : k≤blockCount t) (fit : 844*(k:ℤ)≤t+1-L)
    (margin : (z:ℤ)*(t-L+2) < 2*100*384*(k:ℤ)) :
    z*(ordinary L t).card < 100*(cut n L t).card := by
  let pick (x : ℤ) := x/2
  have subset : ∀ x∈ordinary L t, pick x∈Icc (L/2) ((t-1)/2) := by
    intro x hx
    obtain ⟨inside,odd,_⟩ := mem_filter.mp hx
    obtain ⟨lo,hi⟩ := mem_Icc.mp inside
    apply mem_Icc.mpr
    dsimp [pick]
    omega
  have unique : Set.InjOn pick (ordinary L t : Set ℤ) := by
    intro x hx y hy same
    have a := (mem_filter.mp hx).2.1
    have b := (mem_filter.mp hy).2.1
    dsimp [pick] at same
    omega
  have count := card_le_card_of_injOn pick subset unique
  rw [Int.card_Icc] at count
  have odds : 2*((ordinary L t).card:ℤ)≤t-L+2 := by omega
  have budget : (384:ℤ)*k≤(cut n L t).card := by
    exact_mod_cast full_blocks large ceil cap fit
  have paid := mul_le_mul_of_nonneg_left odds (Int.natCast_nonneg z)
  have result : (z:ℤ)*(ordinary L t).card < 100*(cut n L t).card := by
    nlinarith only [paid,margin,budget]
  exact_mod_cast result

/-- A terminal fragment inside the last block inherits its at-most-36
remaining odd positions. -/
theorem last_fragment {n t L : ℤ} (large : 2^24≤t) (ceil : n<(t+1)^2) (short : t-L≤843) :
    (ordinary L t \ cut n L t).card ≤ 36 := by
  let a := blockStart t 0
  have ii : 0<blockCount t := by unfold blockCount; omega
  obtain ⟨pos,_,near⟩ := shape large ceil ii
  have eq : a+843=t := by unfold a blockStart; simp; omega
  have sub : ordinary L t \ cut n L t ⊆ oddSites a (a+843) (lanes n (lower n (a+843)) (upper n a)) := by
    intro x hx
    obtain ⟨ordinaryX,no⟩ := mem_sdiff.mp hx
    by_contra missing
    have inc : ordinary L t ⊆ ordinary a (a+843) :=
      subset_ordinary (by unfold a blockStart; push_cast; omega) eq.ge
    have drop : x∈dropped n t 0 := mem_sdiff.mpr ⟨inc ordinaryX,missing⟩
    exact no (mem_inter.mpr ⟨ordinaryX,mem_biUnion.mpr ⟨0,mem_range.mpr ii,drop⟩⟩)
  exact (card_le_card sub).trans (position_bound pos (by omega) near (by omega))

/-- The result applies to every terminal subinterval. If clipping leaves
fewer than 39 potential divisors, all of them fit the stated direct budget. -/
theorem terminal (n : ℕ) (large : 2^2047≤n) (L : ℤ) (lo : (bandLow n:ℤ)≤L) :
    (ordinary L n.sqrt).card≤38 ∨
      6*(ordinary L n.sqrt).card<100*(cut n L n.sqrt).card := by
  by_cases small : (ordinary L n.sqrt).card≤38
  · exact Or.inl small
  right
  let t : ℤ := n.sqrt
  have big : (2:ℤ)^24≤t := by
    have h : 2^24≤n.sqrt := Nat.le_sqrt'.mpr ((by decide +kernel : (2^24:ℕ)^2≤2^2047).trans large)
    dsimp only [t]; exact_mod_cast h
  have ceil : (n:ℤ)<(t+1)^2 := by dsimp only [t]; exact_mod_cast Nat.lt_succ_sqrt' n
  change 6*(ordinary L t).card<100*(cut n L t).card
  by_cases allfit : 844*(blockCount t:ℤ)≤t+1-L
  · have all : removed n t ⊆ ordinary L t := by
      intro x hx
      obtain ⟨i,hi,mem⟩ := mem_biUnion.mp hx
      have ii := mem_range.mp hi
      exact subset_ordinary (by unfold blockStart; omega : L≤blockStart t i)
        (by unfold blockStart; omega : blockStart t i+843≤t) (mem_sdiff.mp mem).1
    have rate := (target n large).2
    have part := card_le_card (subset_ordinary lo (le_refl t))
    rw [cut,inter_eq_right.mpr all]
    exact (Nat.mul_le_mul_left 6 part).trans_lt rate
  · by_cases short : t-L≤843
    · have bound := last_fragment (n:=(n:ℤ)) big ceil short
      have counts := card_sdiff_add_card_eq_card (s:=cut n L t) (t:=ordinary L t) inter_subset_left
      change ¬ (ordinary L t).card≤38 at small
      omega
    · let k : ℕ := ((t+1-L)/844).toNat
      have bounded : k≤blockCount t := by unfold k; omega
      have available : 844*(k:ℤ)≤t+1-L := by unfold k; omega
      have discarded := full_blocks (n:=(n:ℤ)) big ceil bounded available
      have raw : (ordinary L t).card≤(Icc L t).card := filter_subset _ _ |> card_le_card
      rw [Int.card_Icc] at raw
      unfold k at discarded
      omega

set_option exponentiation.threshold 4096 in
/-- The exact public lower bound for two 1024-bit primes dominates the
ratio-only lower bound. The upper endpoint is still the integer square root. -/
theorem width_lower (n : ℕ) : bandLow n ≤ NearSmoothExclusion.smallest n := by
  let C := (2:ℕ)^1024-1
  let L := NearSmoothExclusion.smallest n
  have cap : 0<C := by decide +kernel
  have scale : 2^1023≤L := le_max_left _ _
  have quotient : (n-1)/C+1 ≤ L := le_max_right _ _
  have bound : n-1<L*C := (Nat.div_lt_iff_lt_mul cap).mp (by omega)
  have size : C ≤ 2*L := (show C≤2*2^1023 by decide +kernel).trans (Nat.mul_le_mul_left _ scale)
  have full := Nat.mul_le_mul_left L size
  have smaller : (n-1)/2 < L^2 := by rw [pow_two]; nlinarith only [bound,full, Nat.div_mul_le_self (n-1) 2]
  exact Nat.sqrt_lt'.mpr smaller

/-- Whole-clipped-band statement with the actual public equal-width floor. -/
theorem equal_width (n : ℕ) (large : 2^2047≤n) :
    let L : ℤ := NearSmoothExclusion.smallest n
    (ordinary L n.sqrt).card≤38 ∨ 6*(ordinary L n.sqrt).card<100*(cut n L n.sqrt).card := by
  apply terminal n large
  exact_mod_cast width_lower n

set_option exponentiation.threshold 4096 in
/-- For genuine equal-width prime pairs, the smaller prime is in the
ordinary clipped interval and is absent from the set of removed positions. -/
theorem keeps_prime {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p≤q)
    (side : 2^1023≤p) (cap : q<2^1024) (large : 2^2047≤p*q) :
    let n := p*q
    let L : ℤ := NearSmoothExclusion.smallest n
    (p:ℤ) ∈ ordinary L n.sqrt ∧ (p:ℤ) ∉ cut n L n.sqrt := by
  dsimp only
  have den : 0<(2:ℕ)^1024-1 := by decide +kernel
  have input_pos := Nat.mul_pos pp.pos qp.pos
  have low : NearSmoothExclusion.smallest (p*q)≤p := by
    apply max_le side
    have top := Nat.mul_le_mul_left p (by omega : q≤2^1024-1)
    exact (Nat.div_lt_iff_lt_mul den).mpr (by omega)
  have high : p≤(p*q).sqrt := Nat.le_sqrt.mpr (Nat.mul_le_mul_left p order)
  have pbig := (show 211 < (2:ℕ)^1023 by decide +kernel).trans_le side
  have zero : ((p:ℕ):ZMod 211)≠0 := by
    intro h
    have dv := (ZMod.natCast_zmod_eq_zero_iff_dvd p 211).mp h
    rcases (Nat.dvd_prime pp).mp dv with h | h <;> omega
  have oddp := pp.eq_two_or_odd.resolve_left (by omega)
  have oddq := qp.eq_two_or_odd.resolve_left (by omega)
  have as_odd (z : ℕ) (parity : z%2=1) : Odd (z:ℤ) := by
    refine ⟨(z/2 : ℕ),?_⟩
    omega
  constructor
  · apply mem_filter.mpr
    exact ⟨mem_Icc.mpr ⟨by exact_mod_cast low,by exact_mod_cast high⟩,by exact_mod_cast oddp,
      mem_erase.mpr ⟨by simpa only [Int.cast_natCast] using zero,mem_univ _⟩⟩
  · intro droppedP
    have big : 2^24≤(p*q).sqrt := Nat.le_sqrt'.mpr ((by decide +kernel : (2^24:ℕ)^2≤2^2047).trans large)
    apply safe (n:=((p*q:ℕ):ℤ)) (q:=(q:ℤ)) (t:=((p*q).sqrt:ℤ))
      (by exact_mod_cast big) (by exact_mod_cast (Nat.le_sqrt'.mp le_rfl : (p*q).sqrt^2≤p*q))
      (by exact_mod_cast Nat.lt_succ_sqrt' (p*q)) (by simp) (as_odd p oddp) (as_odd q oddq)
    exact (mem_inter.mp droppedP).2

end PrimeFactors.ReciprocalSumTail
