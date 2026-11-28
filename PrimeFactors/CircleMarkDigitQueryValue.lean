import PrimeFactors.CircleMarkMaskDigitReadout

/-! Exact character-sum values for a digit query. Opposite parity forces
every complementary pair to use one block and one offset, and division with
remainder fixes both coordinates. -/
namespace PrimeFactors.CircleMarkDigitQueryValue

open Finset CircleMarkDigitCoordinates CircleMarkJacobiMask CircleMarkMidcutReadout
open CircleMarkMaskDigitReadout CircleMarkSparseMaskProbe
open scoped Classical
open private PrimeFactors.CircleMarkDigitCoordinates.block_mem
  PrimeFactors.CircleMarkDigitCoordinates.offset_mem from PrimeFactors.CircleMarkDigitCoordinates
open private PrimeFactors.CircleMarkMaskDigitReadout.safe from PrimeFactors.CircleMarkMaskDigitReadout
open CircleMarkDigitCoordinates (block_mem offset_mem)
open CircleMarkMaskDigitReadout (safe)

private theorem canonical_pair {p k m s : ℕ} {J I : Finset ℕ} (mp : 0<m) (cap : I⊆range m)
    (code : p+2*s=2*k+1) {z : ℕ×ℕ} (hz : z∈pairs p (menu k m J I)) :
    let a := k-2*(m*(s/m))
    let b := k+1-2*(s%m)
    z = (min a b,max a b) := by
  obtain ⟨⟨xm,ym⟩,lt,zz⟩ := (show (z.1∈menu k m J I ∧ z.2∈menu k m J I) ∧
      z.1<z.2 ∧ z.1+z.2=p from by
    obtain ⟨mem,h⟩ := mem_filter.mp hz
    exact ⟨mem_product.mp mem,h⟩)
  let a := k-2*(m*(s/m))
  let b := k+1-2*(s%m)
  have identify {x y : ℕ} (xb : x∈blocks k m J) (yo : y∈offsets k I) (xy : x+y=p) :
      x=a ∧ y=b := by
    obtain ⟨j,_,_,jx⟩ := block_mem xb
    obtain ⟨i,ii,_,iy⟩ := offset_mem yo
    have il := mem_range.mp (cap ii)
    have digits : s=i+m*j := by omega
    have jv : s/m=j := by rw [digits,Nat.add_mul_div_left _ _ mp,Nat.div_eq_of_lt il,zero_add]
    have iv : s%m=i := by rw [digits,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt il]
    dsimp only [a,b]
    rw [jv,iv]
    omega
  rcases mem_union.mp xm with xb|xo <;> rcases mem_union.mp ym with yb|yo
  · obtain ⟨j,_,_,jx⟩ := block_mem xb
    obtain ⟨i,_,_,iy⟩ := block_mem yb
    omega
  · obtain ⟨x,y⟩ := identify xb yo zz
    change z=(min a b,max a b)
    exact Prod.ext (by omega) (by omega)
  · obtain ⟨y,x⟩ := identify yb xo (by omega)
    change z=(min a b,max a b)
    exact Prod.ext (by omega) (by omega)
  · obtain ⟨j,_,_,jx⟩ := offset_mem xo
    obtain ⟨i,_,_,iy⟩ := offset_mem yo
    omega

/-- The indicator of the requested two-digit rectangle counts its unordered
complementary pairs exactly, including when either index set is empty. -/
theorem pair_count {p k m s : ℕ} {J I : Finset ℕ} (mp : 0<m) (cap : I⊆range m)
    (low : k+1<p) (code : p+2*s=2*k+1) :
    (pairs p (menu k m J I)).card = if s/m∈J ∧ s%m∈I then 1 else 0 := by
  have one : (pairs p (menu k m J I)).card ≤ 1 := by
    apply card_le_one.mpr
    intro z hz w hw
    exact (canonical_pair mp cap code hz).trans (canonical_pair mp cap code hw).symm
  have non : (pairs p (menu k m J I)).Nonempty ↔ s/m∈J ∧ s%m∈I := by
    rw [←pair_iff mp cap low code]
    constructor
    · rintro ⟨z,hz⟩
      obtain ⟨mem,lt,sum⟩ := mem_filter.mp hz
      exact ⟨z.1,(mem_product.mp mem).1,z.2,(mem_product.mp mem).2,lt,sum⟩
    · rintro ⟨x,hx,y,hy,lt,sum⟩
      exact ⟨(x,y),mem_filter.mpr ⟨mem_product.mpr ⟨hx,hy⟩,lt,sum⟩⟩
  split_ifs with hit
  · have pos := card_pos.mpr (non.mpr hit)
    omega
  · exact card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp (fun h => hit (non.mp h)))

/-- A true reading gives d(d−1) and a false reading gives d², where d is the
cardinality of the public query menu. -/
theorem exact_value {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime] (order : p<q) (bal : q<2*p)
    (op : p≠2) (oq : q≠2) (J I : Finset ℕ) (cap : I⊆range (base (p*q))) :
    let C := coordinates (p*q) J I
    let d := (C.card:ℤ)
    globalSum (p*q) (squareMask C) = if response (p*q) J I then d*(d-1) else d^2 := by
  let C := coordinates (p*q) J I
  obtain ⟨low,high,_⟩ := CircleMarkJacobiMaskEdge.bounds order bal op oq
  obtain ⟨code,_,_⟩ := digits low high (hp.out.odd_of_ne_two op)
  obtain ⟨coords,room⟩ := safe order bal op oq J I
  have loss := pair_count (J:=J) (Nat.succ_pos _) cap low code
  have test := query order bal op oq J I cap
  have r : (pairs p C).card = if response (p*q) J I then 1 else 0 := by
    simpa only [test] using loss
  change globalSum (p*q) (squareMask C) = _
  rw [exact_sum order op oq C coords room,r]
  by_cases hit : response (p*q) J I = true
  · rw [if_pos hit,if_pos hit]
    cases h : C.card with
    | zero => simp
    | succ j => simp
  · rw [if_neg hit,if_neg hit]
    simp [sq,C]

end PrimeFactors.CircleMarkDigitQueryValue
