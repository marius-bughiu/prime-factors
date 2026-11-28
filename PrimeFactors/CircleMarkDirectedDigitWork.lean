import PrimeFactors.CircleMarkDirectedDigitQueries
import Mathlib.Data.Int.AbsoluteValue

/-! Counting complete rows in ascending block-index order and identifying the
ordinary descending odd trial candidates contributed by each row. -/
namespace PrimeFactors.CircleMarkDirectedDigitWork

open Finset Polynomial CircleMarkDigitCoordinates CircleMarkMaskDigitReadout
open CircleMarkDirectedDigitQueries CircleMarkJacobiMask CircleMarkMidcutReadout
open scoped Classical
open private PrimeFactors.CircleMarkDigitCoordinates.offset_mem from PrimeFactors.CircleMarkDigitCoordinates
open private PrimeFactors.CircleMarkDirectedDigitQueries.geometry from PrimeFactors.CircleMarkDirectedDigitQueries
open CircleMarkDigitCoordinates (offset_mem)
open CircleMarkDirectedDigitQueries (geometry)

def rowAt (n j : ℕ) := cutoff n-2*(base n*j)
def candidate (k t : ℕ) := 2*k+1-2*t
def gapIndex (n p : ℕ) := (2*cutoff n+1-p)/2

/-- The initial odd trial is either the integer square root or one above it. -/
theorem starting_point (n : ℕ) :
    n.sqrt ≤ candidate (cutoff n) 0 ∧ candidate (cutoff n) 0 ≤ n.sqrt+1 := by
  simp only [candidate,cutoff,mul_zero,Nat.sub_zero]
  omega

private theorem offset_room {k i : ℕ} (size : 2≤k) (idx : i<radix k) : 2*i<k+1 := by
  have spa := Nat.sqrt_le k
  change i<k.sqrt+1 at idx
  by_cases small : k.sqrt<2
  · omega
  have := Nat.mul_le_mul_right k.sqrt (by omega : 2≤k.sqrt)
  omega

private theorem offsets_image {k : ℕ} (size : 2≤k) :
    offsets k (range (radix k))=(range (radix k)).image (fun i => k+1-2*i) := by
  unfold offsets
  rw [filter_eq_self.mpr (fun _ hi => offset_room size (mem_range.mp hi))]

/-- Starting at cutoff two, all radix-many offsets survive the positivity test. -/
theorem columns_card {n : ℕ} (size : 2≤cutoff n) : (columns n (range (base n))).card = base n := by
  rw [columns,base,offsets_image size,card_image_of_injOn,card_range]
  intro i hi j hj eqn
  have := offset_room size (mem_range.mp hi)
  have := offset_room size (mem_range.mp hj)
  dsimp at eqn
  omega

/-- All block indices up through the first hit survive the positivity filter.
Their row gcds are one except at the quotient of the factor offset by the radix. -/
theorem first_row {p q j : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2)
    (before : j≤gapIndex (p*q) p / base (p*q)) :
    rowAt (p*q) j ∈ rows (p*q) ∧
      rowGcd (p*q) (range (base (p*q))) (rowAt (p*q) j) =
        if j=gapIndex (p*q) p / base (p*q) then p else 1 := by
  let n := p*q
  let k := cutoff n
  let m := base n
  let s := gapIndex n p
  change j≤s/m at before
  obtain ⟨lo,hi,_⟩ := CircleMarkJacobiMaskEdge.bounds order bal op oq
  obtain ⟨code,jl,il⟩ := digits lo hi (hp.out.odd_of_ne_two op)
  change p+2*s=2*k+1 at code
  change s/m<m at jl
  change s%m<m at il
  change k+1<p at lo
  have recomb : s%m+m*(s/m)=s := Nat.mod_add_div ..
  have bound := Nat.mul_le_mul_left m before
  have short : 2*(m*j)<k := by omega
  have row : rowAt n j∈rows n :=
    mem_image.mpr ⟨j,mem_filter.mpr ⟨mem_range.mpr (before.trans_lt jl),short⟩,rfl⟩
  refine ⟨row,?_⟩
  rw [gcd_eq order bal op oq row]
  apply if_congr _ rfl rfl
  constructor
  · rintro ⟨y,yo,eqn⟩
    obtain ⟨i,ii,_,defn⟩ := offset_mem yo
    change y+2*i=k+1 at defn
    change k-2*(m*j)+y=p at eqn
    have digit : i<m := mem_range.mp ii
    have word : s=i+m*j := by omega
    change j=s/m
    have pos : 0<m := Nat.succ_pos _
    rw [word,Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt digit,zero_add]
  · intro hit
    change j=s/m at hit
    have room : 2*(s%m)<k+1 := by omega
    refine ⟨k+1-2*(s%m),mem_image.mpr ⟨s%m,mem_filter.mpr ⟨mem_range.mpr il,room⟩,rfl⟩,?_⟩
    change k-2*(m*j)+(k+1-2*(s%m))=p
    rw [hit]
    omega

/-- The descending odd trial at index t divides N for the first time at s. -/
theorem trial_iff {p q t : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2) (before : t≤gapIndex (p*q) p) :
    candidate (cutoff (p*q)) t ∣ p*q ↔ t=gapIndex (p*q) p := by
  obtain ⟨lo,hi,large⟩ := CircleMarkJacobiMaskEdge.bounds order bal op oq
  have code := (digits lo hi (hp.out.odd_of_ne_two op)).1
  change p+2*gapIndex (p*q) p=2*cutoff (p*q)+1 at code
  let a := candidate (cutoff (p*q)) t
  have bot : p≤a := by dsimp [a,candidate]; omega
  have top : a<q := by dsimp [a,candidate]; omega
  have small := hp.out.two_le
  have cop := (hq.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega : 0<a) top)).symm
  change a∣p*q ↔ _
  rw [cop.dvd_mul_right,Nat.dvd_prime hp.out]
  dsimp only [a,candidate] at *
  omega

/-- Every complete row through the first hit contributes m root terms.
The exact overrun relative to the s+1 descending odd trials consists of the
remaining offsets in the last row, fewer than m terms. -/
theorem exact_work {n p : ℕ} (size : 2≤cutoff n) :
    let m := base n
    let s := gapIndex n p
    let terms := ∑ _j∈range (s/m+1), (columns n (range m)).card
    terms=(s/m+1)*m ∧ terms=(s+1)+(m-1-s%m) ∧ terms-(s+1)<m := by
  let m := base n
  let s := gapIndex n p
  have pos : 0<m := Nat.succ_pos _
  have il := Nat.mod_lt s pos
  have code := Nat.mod_add_div s m
  have cost : (∑ _j∈range (s/m+1), (columns n (range m)).card) = (s/m+1)*m := by
    rw [columns_card size,sum_const,card_range,nsmul_eq_mul]
    rfl
  have over : (s/m+1)*m=(s+1)+(m-1-s%m) := by
    rw [Nat.add_mul,one_mul,Nat.mul_comm (s/m) m]
    omega
  refine ⟨cost,cost.trans over,?_⟩
  change (∑ _j∈range (s/m+1), (columns n (range m)).card)-(s+1)<m
  rw [cost,over]
  omega

/-- The integer polynomial value factors into all differences and all sums. -/
theorem linear_factors (C : Finset ℕ) (x : ℕ) :
    (squareMask C).eval ((x:ℤ)^2) =
      (∏y∈C, ((x:ℤ)-y)) * ((∏y∈C, (x+y) : ℕ) : ℤ) := by
  simp only [squareMask,eval_prod,eval_sub,eval_X,eval_C,Nat.cast_prod,Nat.cast_add,←prod_mul_distrib]
  exact prod_congr rfl (fun _ _ => by ring)

/-- All differences are nonzero and smaller in magnitude than either prime,
so discarding the differences from the row product preserves its gcd. -/
theorem sums_gcd {p q x : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2)
    (row : x∈rows (p*q)) (I : Finset ℕ) :
    rowGcd (p*q) I x = (∏ y∈columns (p*q) I, (x+y)).gcd (p*q) := by
  let C := columns (p*q) I
  obtain ⟨⟨_,xp⟩,safe⟩ := geometry order bal op oq row I
  have absprod : (∏y∈C, ((x:ℤ)-y)).natAbs = ∏y∈C, ((x:ℤ)-y).natAbs :=
    map_prod Int.natAbsHom _ _
  rw [rowGcd,linear_factors,Int.natAbs_mul,Int.natAbs_natCast,absprod]
  apply Nat.Coprime.gcd_mul_left_cancel
  apply Nat.coprime_prod_left_iff.mpr
  intro y hy
  obtain ⟨yp,ne,_⟩ := safe y hy
  let d := ((x:ℤ)-y).natAbs
  have short : d<p := by
    change ((x:ℤ)-y).natAbs<p
    rw [←Nat.cast_lt (α:=ℤ),Int.natCast_natAbs,abs_lt]
    omega
  have nz : 0<d := by
    change 0<((x:ℤ)-y).natAbs
    exact Int.natAbs_pos.mpr (by omega)
  exact Nat.coprime_mul_iff_right.mpr
    ⟨(hp.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt nz short)).symm,
     (hq.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt nz (short.trans order))).symm⟩

/-- Each untrimmed offset contributes the consecutive descending odd candidate
at index m*j+i, so a complete row is one gcd of m ordinary trial candidates. -/
theorem interval_gcd {p q j : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2) (size : 2≤cutoff (p*q))
    (jl : j<base (p*q)) (short : 2*(base (p*q)*j)<cutoff (p*q)) :
    rowGcd (p*q) (range (base (p*q))) (rowAt (p*q) j) =
      (∏ i∈range (base (p*q)), candidate (cutoff (p*q)) (base (p*q)*j+i)).gcd (p*q) := by
  let n := p*q
  let m := base n
  let k := cutoff n
  change j<m at jl
  change 2*(m*j)<k at short
  have row : rowAt n j∈rows n := mem_image.mpr ⟨j,mem_filter.mpr ⟨mem_range.mpr jl,short⟩,rfl⟩
  rw [sums_gcd order bal op oq row,columns,base,offsets_image size,prod_image]
  · congr 1
    apply prod_congr rfl
    intro i hi
    have ir := offset_room size (mem_range.mp hi)
    change 2*i<k+1 at ir
    change k-2*(m*j)+(k+1-2*i)=2*k+1-2*(m*j+i)
    omega
  · intro i hi h hh eqn
    have := offset_room size (mem_range.mp hi)
    have := offset_room size (mem_range.mp hh)
    omega

/-- On 2183 two complete five-term rows include 37, the sixth trial from 47. -/
theorem example_2183 :
    let n := 2183
    let m := base n
    let s := gapIndex n 37
    candidate (cutoff n) 0=47 ∧ n.sqrt=46 ∧ m=5 ∧ s=5 ∧ (s/m+1)*m=10 ∧ s+1=6 := by
  decide +kernel

end PrimeFactors.CircleMarkDirectedDigitWork
