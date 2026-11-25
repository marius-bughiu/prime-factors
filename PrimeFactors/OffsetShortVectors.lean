import PrimeFactors.ReducedOffsetMinimum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Ring.Int.Parity

namespace PrimeFactors.OffsetShortVectors
open ReducedOffsetMinimum

/-- The positive first coordinate chooses one sign for each primitive direction. -/
def Short (p T q h : ℤ) (x : ℕ × ℕ) : Prop :=
  0<x.1 ∧ x.1.Coprime x.2 ∧ 3*(Q p T q x.1 x.2)^2≤4*h

private def area (x y : ℕ × ℕ) : ℤ := (x.1:ℤ)*y.2-(x.2:ℤ)*y.1
private def val (p T q : ℤ) (x : ℕ × ℕ) := Q p T q x.1 x.2
private def bil (p T q : ℤ) (x y : ℕ × ℕ) : ℤ :=
  p*x.1*y.1-T*((x.1:ℤ)*y.2+(x.2:ℤ)*y.1)+q*x.2*y.2

private theorem parallel {x y : ℕ × ℕ} (xp : 0<x.1) (xc : x.1.Coprime x.2)
    (yc : y.1.Coprime y.2) (zero : area x y=0) : x=y := by
  obtain ⟨a,b⟩ := x
  obtain ⟨c,d⟩ := y
  change (a:ℤ)*d-(b:ℤ)*c=0 at zero
  have eq : a*d=c*b := by exact_mod_cast (show (a:ℤ)*d=(c:ℤ)*b by linarith only [zero])
  have ac : a∣c := xc.dvd_of_dvd_mul_right (eq ▸ dvd_mul_right a d)
  have ca : c∣a := yc.dvd_of_dvd_mul_right (eq.symm ▸ dvd_mul_right c b)
  obtain rfl := Nat.dvd_antisymm ac ca
  have bd := Nat.eq_of_mul_eq_mul_left xp eq
  exact Prod.ext rfl bd.symm

private theorem gram (p T q : ℤ) (x y : ℕ × ℕ) :
    val p T q x*val p T q y-(bil p T q x y)^2=(p*q-T^2)*(area x y)^2 := by
  unfold val Q bil area
  ring

/-- Once a known primitive vector has value A with A·J<h, every primitive
vector of value at most J in the same positive half-plane equals it. -/
theorem unique_of_thin {p T q h J : ℤ} {x y : ℕ × ℕ} (det : p*q-T^2=h) (hh : 0<h)
    (xp : 0<x.1) (xc : x.1.Coprime x.2) (yc : y.1.Coprime y.2)
    (pos : 0<Q p T q x.1 x.2) (low : Q p T q y.1 y.2≤J)
    (thin : Q p T q x.1 x.2*J<h) : x=y := by
  by_contra distinct
  have nonzero : area x y≠0 := fun z => distinct (parallel xp xc yc z)
  have one : 1≤(area x y)^2 := Int.add_one_le_iff.mpr (sq_pos_of_ne_zero nonzero)
  have ident := gram p T q x y
  rw [det] at ident
  unfold val at ident
  nlinarith only [ident,mul_le_mul_of_nonneg_left low pos.le,thin,sq_nonneg (bil p T q x y),
    mul_le_mul_of_nonneg_left one hh.le]

/-- Distinct primitive short directions necessarily form an integral basis. -/
private theorem unit_area {p T q h : ℤ} (hh : 0<h) (det : p*q-T^2=h)
    {x y : ℕ × ℕ} (hx : Short p T q h x) (hy : Short p T q h y) (ne : x≠y) :
    (area x y)^2=1 := by
  obtain ⟨xp,xc,xs⟩ := hx
  obtain ⟨_,yc,ys⟩ := hy
  let A := val p T q x
  let B := val p T q y
  let C := bil p T q x y
  let D := area x y
  change 3*A^2≤4*h at xs
  change 3*B^2≤4*h at ys
  have relation : A*B-C^2=h*D^2 := (gram p T q x y).trans (by rw [det])
  have nz : D≠0 := fun z => ne (parallel xp xc yc z)
  have bounds : -1≤D ∧ D≤1 := by
    by_contra! outside
    have four : 4≤D^2 := by
      by_cases neg : D < -1
      · nlinarith only [sq_nonneg (D+2),show D≤ -2 by omega]
      · nlinarith only [sq_nonneg (D-2),show 2≤D by omega]
    nlinarith only [xs,ys,sq_nonneg (A-B),sq_nonneg C,relation,mul_le_mul_of_nonneg_left four hh.le,hh]
  change D^2=1
  rcases (show D=1 ∨ D= -1 by omega) with d|d <;> rw [d] <;> decide

private theorem expansion (p T q : ℤ) (x y z : ℕ × ℕ) :
    val p T q z*(area x y)^2=val p T q x*(area z y)^2+
      val p T q y*(area x z)^2+2*bil p T q x y*area z y*area x z := by
  unfold val Q bil area
  ring

private theorem first_coefficient (p T q : ℤ) (x y : ℕ × ℕ) :
    p*(area x y)^2=val p T q x*(y.2:ℤ)^2+val p T q y*(x.2:ℤ)^2-
      2*bil p T q x y*x.2*y.2 := by
  unfold val Q bil area
  ring

/-- Three pairwise unimodular short directions force all three values to
agree. In this case the common value is twice an integer. -/
private theorem equal_even {A B C G h u v : ℤ} (a : 3*A^2≤4*h) (b : 3*B^2≤4*h)
    (c : 3*C^2≤4*h) (gramEq : A*B-G^2=h) (u1 : u^2=1) (v1 : v^2=1)
    (expansionEq : C=A+B+2*G*u*v) : A=B ∧ ∃ l, A=2*l := by
  have signed : C-A-B=2*G*u*v := by linarith only [expansionEq]
  have squared : (C-A-B)^2=4*G^2 := by rw [signed,mul_pow,mul_pow,mul_pow,u1,v1];ring
  have heron : 4*h=2*(A*B+B*C+C*A)-(A^2+B^2+C^2) := by nlinarith only [squared,gramEq]
  have ab : (A-B)^2=0 := by
    nlinarith only [a,b,c,heron,sq_nonneg (B-C),sq_nonneg (C-A),sq_nonneg (A-B)]
  have ca : (C-A)^2=0 := by
    nlinarith only [a,b,c,heron,sq_nonneg (B-C),sq_nonneg (C-A),sq_nonneg (A-B)]
  have eab : A=B := sub_eq_zero.mp (pow_eq_zero ab)
  have eca : C=A := sub_eq_zero.mp (pow_eq_zero ca)
  exact ⟨eab,⟨-G*u*v,by nlinarith only [eab,eca,expansionEq]⟩⟩

/-- Three distinct primitive directions at the sharp cutoff contradict an
odd value represented by the first coordinate vector of the original form. -/
theorem no_three {p T q h : ℤ} (odd : Odd p) (_hp : 0<p) (hh : 0<h) (det : p*q-T^2=h)
    {x y z : ℕ × ℕ} (hx : Short p T q h x) (hy : Short p T q h y) (hz : Short p T q h z)
    (xy : x≠y) (xz : x≠z) (yz : y≠z) : False := by
  have axy := unit_area hh det hx hy xy
  have axz := unit_area hh det hx hz xz
  have azy := unit_area hh det hz hy yz.symm
  have gramEq := gram p T q x y
  rw [det,axy,mul_one] at gramEq
  have ex := expansion p T q x y z
  rw [axy,azy,axz,mul_one,mul_one,mul_one] at ex
  obtain ⟨same,l,even⟩ := equal_even hx.2.2 hy.2.2 hz.2.2 gramEq azy axz ex
  change val p T q x=val p T q y at same
  change val p T q x=2*l at even
  have coeff := first_coefficient p T q x y
  rw [axy,mul_one,← same,even] at coeff
  obtain ⟨o,ho⟩ := odd
  have ep : p=2*(l*(y.2:ℤ)^2+l*(x.2:ℤ)^2-bil p T q x y*x.2*y.2) := by linear_combination coeff
  omega

/-- A finite family of positive-first-coordinate primitive vectors of the
form with odd leading coefficient has at most two members at the sharp cutoff. -/
theorem card_le_two {p T q h : ℤ} (odd : Odd p) (hp : 0<p) (hh : 0<h) (det : p*q-T^2=h)
    (S : Finset (ℕ × ℕ)) (all_short : ∀ x ∈ S, Short p T q h x) : S.card ≤ 2 := by
  by_contra! large
  obtain ⟨x,y,z,hx,hy,hz,xy,xz,yz⟩ := Finset.two_lt_card_iff.mp large
  exact no_three odd hp hh det (all_short x hx) (all_short y hy) (all_short z hz) xy xz yz

/-- The upper bound is attained on 1891=31·61. The two primitive vectors
have distinct public offsets 6 and 7. -/
theorem sharp_example : Short 31 43 61 42 (1,1) ∧ Short 31 43 61 42 (3,2) ∧
    Q 31 43 61 1 1=6 ∧ Q 31 43 61 3 2=7 := by
  unfold Short Q
  decide +kernel

end PrimeFactors.OffsetShortVectors
