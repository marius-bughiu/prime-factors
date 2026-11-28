import PrimeFactors.CircleMarkJacobiMaskEdge

/-! Represent an interval of odd candidates by sums of two small sets of
coordinates. The quotient and remainder of the candidate offset supply the
two indices. Trimming at zero keeps every selected coordinate positive. -/
namespace PrimeFactors.CircleMarkDigitCoordinates

open Finset CircleMarkMidcutReadout
open scoped Classical

def radix (k : ℕ) := k.sqrt+1

noncomputable def blocks (k m : ℕ) (J : Finset ℕ) :=
  (J.filter fun j => 2*(m*j)<k).image (fun j => k-2*(m*j))

noncomputable def offsets (k : ℕ) (I : Finset ℕ) :=
  (I.filter fun i => 2*i<k+1).image (fun i => k+1-2*i)

noncomputable def menu (k m : ℕ) (J I : Finset ℕ) := blocks k m J ∪ offsets k I

private theorem block_mem {k m x : ℕ} {J : Finset ℕ} (h : x∈blocks k m J) :
    ∃j∈J, 2*(m*j)<k ∧ x+2*(m*j)=k := by
  obtain ⟨j,hj,eqn⟩ := mem_image.mp h
  obtain ⟨jm,jl⟩ := mem_filter.mp hj
  exact ⟨j,jm,jl,by omega⟩

private theorem offset_mem {k x : ℕ} {I : Finset ℕ} (h : x∈offsets k I) :
    ∃i∈I, 2*i<k+1 ∧ x+2*i=k+1 := by
  obtain ⟨i,hi,eqn⟩ := mem_image.mp h
  obtain ⟨im,il⟩ := mem_filter.mp hi
  exact ⟨i,im,il,by omega⟩

theorem coord {k m x : ℕ} {J I : Finset ℕ} (h : x∈menu k m J I) : 0<x ∧ x≤k+1 := by
  rcases mem_union.mp h with a|b
  · obtain ⟨j,_,lt,eq⟩ := block_mem a; omega
  · obtain ⟨i,_,lt,eq⟩ := offset_mem b; omega

theorem size {m : ℕ} (k : ℕ) {J I : Finset ℕ} (bj : J⊆range m) (bi : I⊆range m) :
    (menu k m J I).card≤2*m := by
  have block : (blocks k m J).card≤m := card_image_le.trans
    ((card_filter_le ..).trans ((card_le_card bj).trans_eq (card_range m)))
  have off : (offsets k I).card≤m := card_image_le.trans
    ((card_filter_le ..).trans ((card_le_card bi).trans_eq (card_range m)))
  exact (card_union_le ..).trans (by omega)

/-- A complementary pair exists precisely when both queried sets contain the
two digits of s=(2k+1−p)/2. No primality hypothesis is used in this encoding. -/
theorem pair_iff {p k m s : ℕ} {J I : Finset ℕ} (mp : 0<m) (cap : I⊆range m)
    (low : k+1<p) (code : p+2*s=2*k+1) :
    (∃x∈menu k m J I, ∃y∈menu k m J I, x<y ∧ x+y=p) ↔ s/m∈J ∧ s%m∈I := by
  have decode {x y : ℕ} (xb : x∈blocks k m J) (yo : y∈offsets k I) (eq : x+y=p) :
      s/m∈J ∧ s%m∈I := by
    obtain ⟨j,jm,_,jx⟩ := block_mem xb
    obtain ⟨i,im,_,iy⟩ := offset_mem yo
    have il : i<m := mem_range.mp (cap im)
    have words : s=i+m*j := by omega
    rw [words,Nat.add_mul_div_left _ _ mp,Nat.div_eq_of_lt il,zero_add,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt il]
    exact ⟨jm,im⟩
  constructor
  · rintro ⟨x,xm,y,ym,_,eq⟩
    rcases mem_union.mp xm with a|a <;> rcases mem_union.mp ym with b|b
    · obtain ⟨j,_,_,jx⟩ := block_mem a
      obtain ⟨i,_,_,iy⟩ := block_mem b
      omega
    · exact decode a b eq
    · exact decode b a (by omega)
    · obtain ⟨j,_,_,jx⟩ := offset_mem a
      obtain ⟨i,_,_,iy⟩ := offset_mem b
      omega
  · rintro ⟨jm,im⟩
    let j := s/m
    let i := s%m
    have sj : i+m*j=s := Nat.mod_add_div ..
    have jb : 2*(m*j)<k := by omega
    have ib : 2*i<k+1 := by omega
    let x := k-2*(m*j)
    let y := k+1-2*i
    have xm : x∈menu k m J I := mem_union_left _ (mem_image.mpr ⟨j,mem_filter.mpr ⟨jm,jb⟩,rfl⟩)
    have ym : y∈menu k m J I := mem_union_right _ (mem_image.mpr ⟨i,mem_filter.mpr ⟨im,ib⟩,rfl⟩)
    have eq : x+y=p := by dsimp [x,y]; omega
    have ne : x≠y := by dsimp [x,y]; omega
    rcases lt_or_gt_of_ne ne with a|b
    · exact ⟨x,xm,y,ym,a,eq⟩
    · exact ⟨y,ym,x,xm,b,by omega⟩

/-- Both digits fit in one base chosen from the product alone. -/
theorem digits {p k : ℕ} (low : k+1<p) (high : p≤2*k+1) (odd : Odd p) :
    let s := (2*k+1-p)/2
    p+2*s=2*k+1 ∧ s/radix k<radix k ∧ s%radix k<radix k := by
  let s := (2*k+1-p)/2
  obtain ⟨a,pa⟩ := odd
  have pos : 0<radix k := Nat.succ_pos _
  have span : s<radix k*radix k := (show s≤k by dsimp [s]; omega).trans_lt (Nat.lt_succ_sqrt _)
  exact ⟨by omega,(Nat.div_lt_iff_lt_mul pos).mpr span,Nat.mod_lt _ pos⟩

set_option exponentiation.threshold 8192 in
theorem full_dimensions {p q : ℕ} (order : p<q) (hi : q<2^1024) :
    radix (cutoff (p*q))≤2^512 := by
  have kq := (CircleMarkMidcutReadout.between order).2
  have top : cutoff (p*q)<2^1024 := by omega
  have sq : (2:ℕ)^1024=(2^512)*(2^512) := by decide +kernel
  exact Nat.sqrt_lt.mpr (sq ▸ top)

end PrimeFactors.CircleMarkDigitCoordinates
