import PrimeFactors.QuotientSearch
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.NormNum.Prime

/-! Project a quotient-strip row `(x,e)` to the integer `a*x+b*e`.
After removing the contribution of a hypothesized zero-error row, its
first two moments must satisfy a discrete variance bound. -/

namespace PrimeFactors.QuotientStripIntegerVariance

/-- Parity of the two power sums forces the residual variance into one
congruence class modulo 2h, even for a hypothetical row deletion. -/
theorem quantized {h s t : ℤ} (parity : Even (t-s)) :
    2*h ∣ h*t-s^2-(s%h)*(h-s%h) := by
  let q := s/h
  let r := s%h
  have parts : h*q+r=s := Int.ediv_add_emod s h
  obtain ⟨v,hv⟩ := parity
  obtain ⟨w,hw⟩ := Int.even_mul_pred_self q
  refine ⟨v-q*r-h*w,?_⟩
  change h*t-s^2-r*(h-r)=2*h*(v-q*r-h*w)
  have ts : t=s+2*v := by omega
  rw [ts,←parts]
  linear_combination -h^2*hw

/-- For at most seven remaining rows, real nonnegative variance already
implies the integer lower bound in every direction. -/
theorem no_gain_through_seven {h s t : ℤ} (pos : 0<h) (small : h≤7)
    (parity : Even (t-s)) (psd : 0≤h*t-s^2) : s%h*(h-s%h) ≤ h*t-s^2 := by
  let r := s%h
  have room : r*(h-r)<2*h := by nlinarith only [sq_nonneg (2*r-h),mul_nonneg (by omega : 0≤7-h) pos.le,pos]
  obtain ⟨k,eqn⟩ := quantized (h:=h) parity
  change h*t-s^2-r*(h-r)=2*h*k at eqn
  by_contra! bad
  change h*t-s^2<r*(h-r) at bad
  have neg : k<0 := by
    by_contra! pn
    have := mul_nonneg (show 0≤2*h by omega) pn
    omega
  have reach := mul_le_mul_of_nonneg_left (show k≤-1 by omega) (show 0≤2*h by omega)
  nlinarith only [reach,room,psd,eqn]

/-- Taking any integer row out of the moments preserves the required parity. -/
theorem after_delete {s t : ℤ} (parity : Even (t-s)) (u : ℤ) :
    Even ((t-u^2)-(s-u)) := by
  obtain ⟨v,hv⟩ := parity
  obtain ⟨w,hw⟩ := Int.even_mul_pred_self u
  exact ⟨v-w,by nlinarith only [hv,hw]⟩

open Finset

/-- The sharp integer variance bound follows by summing the nonnegative
products of consecutive integers relative to the floor mean. -/
theorem projected_bound {ι : Type*} (rows : Finset ι) (val : ι → ℤ) :
    let h : ℤ := rows.card
    let s := ∑ i ∈ rows, val i
    let t := ∑ i ∈ rows, val i^2
    (s%h)*(h-s%h) ≤ h*t-s^2 := by
  let h : ℤ := rows.card
  let s := ∑ i ∈ rows, val i
  let t := ∑ i ∈ rows, val i^2
  let q := s/h
  let r := s%h
  have parts : h*q+r=s := Int.ediv_add_emod s h
  have hp : 0≤h := by dsimp [h]; positivity
  have each (v : ℤ) : 0≤(v-q)*(v-q-1) := by
    by_cases low : v≤q
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  have sum := sum_nonneg (s:=rows) (f:=fun i => (val i-q)*(val i-q-1)) (fun i _ => each (val i))
  have expand (v : ℤ) : (v-q)*(v-q-1)=v^2-(2*q+1)*v+q*(q+1) := by ring
  simp only [expand,sum_add_distrib,sum_sub_distrib,←mul_sum,sum_const,nsmul_eq_mul] at sum
  change 0≤ t-(2*q+1)*s+q*(h*q+h*1) at sum
  have scaled := mul_nonneg hp sum
  change r*(h-r)≤h*t-s^2
  rw [←parts] at scaled ⊢
  nlinarith only [scaled]

/-- Squaring an integer preserves its parity, also after summing every row. -/
theorem sums_parity {ι : Type*} (rows : Finset ι) (val : ι → ℤ) :
    Even ((∑ i ∈ rows,val i^2)-(∑ i ∈ rows,val i)) := by
  classical
  induction rows using Finset.induction_on with
  | empty => simp
  | insert i rows absent ih =>
    rw [sum_insert absent,sum_insert absent]
    convert (Int.even_mul_pred_self (val i)).add ih using 1
    ring

/-- With at most seven remaining integer rows, even a proposed deletion
that is absent from the data passes this test whenever it passes real PSD. -/
theorem small_hypothetical {ι : Type*} (rows : Finset ι) (val : ι → ℤ) (u : ℤ)
    (h : ℤ) (pos : 0<h) (small : h≤7) :
    let s := (∑ i ∈ rows,val i)-u
    let t := (∑ i ∈ rows,val i^2)-u^2
    0≤h*t-s^2 → (s%h)*(h-s%h)≤h*t-s^2 :=
  no_gain_through_seven pos small (after_delete (sums_parity rows val) u)

/-- At residual size eight the integer bound can already improve on PSD.
Here the projected data are three copies of −2 and six copies of −1, and
the tested row would contribute zero. -/
theorem first_size :
    let h : ℤ := 8
    let s : ℤ := 3*(-2) + 6*(-1)
    let t : ℤ := 3*(-2)^2 + 6*(-1)^2
    h*t-s^2=0 ∧ (s%h)*(h-s%h)=16 := by decide

/-- The six original strip moments suffice to check every integer projection
after deleting a hypothetical `(x,0)` row. Distinct row indices can have
identical first coordinates. -/
theorem zero_row {ι : Type*} [DecidableEq ι] (rows : Finset ι) (x e : ι → ℤ)
    {j : ι} (member : j ∈ rows) (zero : e j = 0) (a b : ℤ) :
    let h := (rows.card : ℤ)-1
    let s := a*((∑ i ∈ rows,x i)-x j) + b*(∑ i ∈ rows,e i)
    let t := a^2*((∑ i ∈ rows,x i^2)-(x j)^2) +
      2*a*b*(∑ i ∈ rows,x i*e i) + b^2*(∑ i ∈ rows,e i^2)
    (s%h)*(h-s%h) ≤ h*t-s^2 := by
  let L := fun i => a*x i+b*e i
  have bound := projected_bound (rows.erase j) L
  dsimp only at bound ⊢
  have count : ((rows.erase j).card : ℤ) = (rows.card : ℤ)-1 := by
    have := card_erase_add_one member
    omega
  have split (f : ι → ℤ) : (∑ i ∈ rows.erase j,f i) = (∑ i ∈ rows,f i)-f j :=
    eq_sub_of_add_eq (sum_erase_add rows f member)
  have first : (∑ i ∈ rows.erase j,L i) = a*((∑ i ∈ rows,x i)-x j)+b*(∑ i ∈ rows,e i) := by
    dsimp only [L]
    rw [sum_add_distrib,←mul_sum,←mul_sum,split x,split e,zero,sub_zero]
  have second : (∑ i ∈ rows.erase j,L i^2) = a^2*((∑ i ∈ rows,x i^2)-(x j)^2) +
      2*a*b*(∑ i ∈ rows,x i*e i) + b^2*(∑ i ∈ rows,e i^2) := by
    have expand (i : ι) : L i^2=a^2*x i^2+2*a*b*(x i*e i)+b^2*e i^2 := by dsimp [L]; ring
    simp only [expand,sum_add_distrib,←mul_sum,split,zero,mul_zero,zero_pow (by decide : 2≠0),sub_zero]
    ring
  simpa only [count,first,second] using bound

/-- All columns of the selected strip, from the tangent's ceiling through
the chord's floor in each column. -/
noncomputable def controlRows : Finset (ℤ × ℤ) :=
  (Icc 1678 1710).biUnion fun x : ℤ =>
    (Icc (-((-3574327*(2*1678-x))/(1678^2))) (3574327*(1678+1710-x)/(1678*1710))).image
      fun y => (x,y)

/-- The finite column construction is exactly the tangent/chord geometry. -/
theorem control_complete (x y : ℤ) :
    (1678 ≤ x ∧ x ≤ 1710 ∧ 3574327*(2*1678-x) ≤ y*1678^2 ∧
      y*1678*1710 ≤ 3574327*(1678+1710-x)) ↔ (x,y) ∈ controlRows := by
  have lower : -((-3574327*(2*1678-x))/(1678^2)) ≤ y ↔ 3574327*(2*1678-x) ≤ y*1678^2 := by
    rw [neg_le,Int.le_ediv_iff_mul_le (by decide)]
    constructor <;> intro h <;> linarith
  have upper : y ≤ 3574327*(1678+1710-x)/(1678*1710) ↔ y*1678*1710 ≤ 3574327*(1678+1710-x) := by
    rw [Int.le_ediv_iff_mul_le (by decide),mul_assoc]
  simp only [controlRows,mem_biUnion,mem_Icc,mem_image,Prod.mk.injEq]
  constructor
  · rintro ⟨lo,hi,l,r⟩
    exact ⟨x,⟨lo,hi⟩,y,⟨lower.mpr l,upper.mpr r⟩,rfl,rfl⟩
  · rintro ⟨_,⟨lo,hi⟩,_,⟨l,r⟩,rfl,rfl⟩
    exact ⟨lo,hi,lower.mp l,upper.mp r⟩

/-- The eleven rows have different first coordinates. -/
theorem control_points : controlRows =
    {(1686,2120), (1690,2115), (1694,2110), (1697,2106), (1698,2105), (1701,2101),
     (1702,2100), (1705,2096), (1706,2095), (1709,2091), (1710,2090)} := by decide +kernel

/-- All six moments are from distinct integer rows in the actual strip. -/
theorem control_moments :
    let e := fun z : ℤ × ℤ => z.1*z.2-3574327
    controlRows.card=11 ∧ (∑ z ∈ controlRows,z.1)=18698 ∧
    (∑ z ∈ controlRows,z.1^2)=31783792 ∧ (∑ z ∈ controlRows,e z)= -3245 ∧
    (∑ z ∈ controlRows,z.1*e z)= -5532400 ∧ (∑ z ∈ controlRows,(e z)^2)=1812797 := by
  rw [control_points]
  decide +kernel

/-- The real covariance after subtracting the hypothetical row (1709,0)
is positive definite. Projecting to the integer 39*x+e contradicts the
discrete bound. The true smaller prime lies outside this strip. -/
theorem control_separates :
    let h : ℤ := 10
    let x : ℤ := 18698-1709
    let xx : ℤ := 31783792-1709^2
    let e : ℤ := -3245
    let xe : ℤ := -5532400
    let ee : ℤ := 1812797
    let A := h*xx-x^2
    let B := h*xe-x*e
    let C := h*ee-e^2
    let s := 39*x+e
    let t := 39^2*xx+2*39*xe+ee
    (3574327 : ℕ)=1567*2281 ∧ Nat.Prime 1567 ∧ Nat.Prime 2281 ∧ Nat.Prime 1709 ∧
    (1709,2091) ∈ controlRows ∧ 0<A ∧ 0<C ∧ A*C-B^2=4580 ∧
    s%h=6 ∧ h*t-s^2=4 ∧ (s%h)*(h-s%h)=24 := by
  rw [control_points]
  decide +kernel

/-- Applying the projection bound to the moments alone rules out 1709 as
the first coordinate of a zero-error row. -/
theorem control_excludes {z : ℤ × ℤ} (member : z ∈ controlRows)
    (zero : z.1*z.2-3574327=0) : z.1 ≠ 1709 := by
  intro candidate
  let err := fun w : ℤ × ℤ => w.1*w.2-3574327
  have bound := zero_row controlRows Prod.fst err member zero 39 1
  obtain ⟨hc,hx,hxx,he,hxe,hee⟩ := control_moments
  dsimp only [err] at bound
  rw [hc,hx,hxx,he,hxe,hee,candidate] at bound
  norm_num at bound

end PrimeFactors.QuotientStripIntegerVariance
