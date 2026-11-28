import PrimeFactors.CircleMarkDigitCoordinates
import PrimeFactors.CircleMarkSparseMaskProbe
import PrimeFactors.BitMarginals

/-! Read the quotient and remainder digits of the smaller-prime offset by
asking whether a complete character sum falls below the collision-free value. -/
namespace PrimeFactors.CircleMarkMaskDigitReadout

open Finset Polynomial CircleMarkMidcutReadout CircleMarkDigitCoordinates CircleMarkJacobiMask
open scoped Classical

abbrev base (n : ℕ) := radix (cutoff n)
noncomputable abbrev coordinates (n : ℕ) (J I : Finset ℕ) := menu (cutoff n) (base n) J I

/-- The public readout is a single comparison, for two supplied index sets. -/
noncomputable def response (n : ℕ) [NeZero n] (J I : Finset ℕ) : Bool :=
  let C := coordinates n J I
  decide (globalSum n (squareMask C)<(C.card:ℤ)^2)

private theorem safe {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q) (bal : q<2*p)
    (op : p≠2) (oq : q≠2) (J I : Finset ℕ) :
    let C := coordinates (p*q) J I
    (∀x∈C, 0<x ∧ x<p) ∧ (∀x∈C,∀y∈C,x≠y → x+y<q) := by
  obtain ⟨kp,_,kq⟩ := CircleMarkJacobiMaskEdge.bounds order bal op oq
  exact ⟨fun _ hx => ⟨(coord hx).1,(coord hx).2.trans_lt kp⟩, fun x hx y hy ne => by
    have X := (coord hx).2
    have Y := (coord hy).2
    omega⟩

theorem query {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime] (order : p<q) (bal : q<2*p)
    (op : p≠2) (oq : q≠2) (J I : Finset ℕ) (il : I ⊆ range (base (p*q))) :
    let s := (2*cutoff (p*q)+1-p)/2
    response (p*q) J I=true ↔ s/base (p*q) ∈ J ∧ s%base (p*q) ∈ I := by
  obtain ⟨lo,hi,_⟩ := CircleMarkJacobiMaskEdge.bounds order bal op oq
  obtain ⟨code,_,_⟩ := digits lo hi (hp.out.odd_of_ne_two op)
  obtain ⟨coords,cap⟩ := safe order bal op oq J I
  rw [response,decide_eq_true_eq]
  exact (CircleMarkSparseMaskProbe.detect order op oq _ coords cap).trans
    (pair_iff (Nat.succ_pos _) il lo code)

/-- Nonempty menus tolerate absolute error below d/2 in the measured sum.
A collision reduces the integer total by at least the menu cardinality d. -/
theorem noisy_query {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q) (bal : q<2*p)
    (op : p≠2) (oq : q≠2) (J I : Finset ℕ) (y : ℚ) :
    let C := coordinates (p*q) J I
    let d : ℚ := C.card
    |y-(globalSum (p*q) (squareMask C):ℚ)|<d/2 →
    (y<d^2-d/2 ↔ response (p*q) J I=true) := by
  let C := coordinates (p*q) J I
  let d : ℚ := C.card
  have ⟨coords,cap⟩ := safe order bal op oq J I
  have eqn := CircleMarkSparseMaskProbe.exact_sum order op oq C coords cap
  let r := C.card - (CircleMarkSparseMaskProbe.pairs p C).card
  have rat : (globalSum (p*q) (squareMask C):ℚ)=d*(r:ℚ) := by
    change (globalSum (p*q) (squareMask C):ℚ) = (C.card:ℚ)*(r:ℚ)
    exact_mod_cast eqn
  change |y-(globalSum (p*q) (squareMask C):ℚ)|<d/2 →
    (y<d^2-d/2 ↔ decide (globalSum (p*q) (squareMask C)<(C.card:ℤ)^2)=true)
  intro err
  rw [decide_eq_true_eq,←Int.cast_lt (R:=ℚ),Int.cast_pow,Int.cast_natCast,rat]
  rw [rat,abs_lt] at err
  change y<d^2-d/2 ↔ d*(r:ℚ)<d^2
  by_cases same : r=C.card
  · have full : (r:ℚ)=d := by change (r:ℚ)=(C.card:ℚ); exact_mod_cast same
    rw [full] at err ⊢
    constructor <;> intro h <;> nlinarith only [err.1,h]
  · have cap := Nat.sub_le C.card (CircleMarkSparseMaskProbe.pairs p C).card
    have gap : (r:ℚ)+1≤d := by
      change (r:ℚ)+1≤(C.card:ℚ)
      exact_mod_cast (show r+1≤C.card by omega)
    have dp : 0<d := by linarith only [err.1,err.2]
    have more := mul_le_mul_of_nonneg_left gap dp.le
    constructor <;> intro _ <;> nlinarith only [more,dp,err.2]

/-- For an index below m, keep it just when the specified bit is set. -/
noncomputable def bitSet (m b : ℕ) := (range m).filter fun i => i.testBit b = true

/-- Read one binary digit of either the block or the within-block position. -/
noncomputable def bitAnswer (n : ℕ) [NeZero n] (block : Bool) (b : ℕ) : Bool :=
  let all := range (base n)
  let bit := bitSet (base n) b
  if block then response n bit all else response n all bit

theorem bits {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime] (order : p<q) (bal : q<2*p)
    (op : p≠2) (oq : q≠2) (b : ℕ) :
    let m := base (p*q)
    let s := (2*cutoff (p*q)+1-p)/2
    bitAnswer (p*q) true b=(s/m).testBit b ∧ bitAnswer (p*q) false b=(s%m).testBit b := by
  let m := base (p*q)
  let s := (2*cutoff (p*q)+1-p)/2
  obtain ⟨lo,hi,_⟩ := CircleMarkJacobiMaskEdge.bounds order bal op oq
  obtain ⟨_,jl,il⟩ := digits lo hi (hp.out.odd_of_ne_two op)
  have jmem : s/m∈range m := mem_range.mpr jl
  have imem : s%m∈range m := mem_range.mpr il
  have a := query order bal op oq (bitSet m b) (range m) Subset.rfl
  have z := query order bal op oq (range m) (bitSet m b) (filter_subset _ _)
  change (response (p*q) _ _=true ↔ s/m∈bitSet m b ∧ s%m∈range m) at a
  change (response (p*q) _ _=true ↔ s/m∈range m ∧ s%m∈bitSet m b) at z
  simp only [bitSet,mem_filter,jmem,imem,true_and,and_true] at a z
  exact ⟨Bool.eq_iff_iff.mpr a,Bool.eq_iff_iff.mpr z⟩

noncomputable def word (n : ℕ) [NeZero n] (block : Bool) (w : ℕ) :=
  ∑ i∈range w, 2^i*(bitAnswer n block i).toNat

/-- At most 2w Boolean readings, chosen from N before seeing any answers. -/
theorem recover {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime] (order : p<q) (bal : q<2*p)
    (op : p≠2) (oq : q≠2) (w : ℕ) (large : base (p*q)≤2^w) :
    2*cutoff (p*q)+1-2*(base (p*q)*word (p*q) true w+word (p*q) false w)=p := by
  let m := base (p*q)
  let s := (2*cutoff (p*q)+1-p)/2
  obtain ⟨lo,hi,_⟩ := CircleMarkJacobiMaskEdge.bounds order bal op oq
  obtain ⟨code,jl,il⟩ := digits lo hi (hp.out.odd_of_ne_two op)
  have J (b) : bitAnswer (p*q) true b=(s/m).testBit b := (bits order bal op oq b).1
  have I (b) : bitAnswer (p*q) false b=(s%m).testBit b := (bits order bal op oq b).2
  have qlt : s/m < 2^w := jl.trans_le large
  have rlt : s%m < 2^w := il.trans_le large
  simp only [word,J,I,sum_binary_positions,Nat.mod_eq_of_lt qlt,Nat.mod_eq_of_lt rlt]
  have recombine : s%m+m*(s/m)=s := Nat.mod_add_div ..
  change p+2*s=2*cutoff (p*q)+1 at code
  change 2*cutoff (p*q)+1-2*(m*(s/m)+s%m)=p
  omega

set_option exponentiation.threshold 8192 in
/-- Explicit numbers of readings and degree at two 1024-bit primes. -/
theorem full_width {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (lo : 2^1023≤p) (order : p<q)
    (hi : q<2^1024) :
    (2*cutoff (p*q)+1-2*(base (p*q)*word (p*q) true 512+word (p*q) false 512)=p) ∧
    ∀J I : Finset ℕ, J⊆range (base (p*q)) → I⊆range (base (p*q)) →
      (squareMask (coordinates (p*q) J I)).natDegree≤2^513 := by
  have big := (by decide +kernel : 2<2^1023).trans_le lo
  have bal : q<2*p := hi.trans_le ((by decide +kernel : (2:ℕ)^1024≤2*2^1023).trans
    (Nat.mul_le_mul_left 2 lo))
  have width := full_dimensions order hi
  refine ⟨recover order bal big.ne' (big.trans order).ne' 512 width,?_⟩
  intro J I bj bi
  rw [squareMask,natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C,sum_const,nsmul_eq_mul,mul_one,Nat.cast_id]
  exact ((size _ bj bi).trans (Nat.mul_le_mul_left 2 width)).trans_eq (by decide +kernel)

end PrimeFactors.CircleMarkMaskDigitReadout
