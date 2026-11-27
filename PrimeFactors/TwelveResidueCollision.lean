import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! A rational value shared by twelve residues. All operations can be
performed on the product before either of its prime factors is known. -/
namespace PrimeFactors.TwelveResidueCollision
open Finset Polynomial
open scoped Polynomial

set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

def sextic {R : Type*} [CommRing R] (x : R) : R := x^6-45*x^4+135*x^2-27
def num {R : Type*} [CommRing R] (x : R) : R := (sextic x)^2
def den {R : Type*} [CommRing R] (x : R) : R := (x^2+3)^6

/-- The two signed images of a numerator a with denominator b. -/
def pair {R : Type*} [CommRing R] (a b y : R) : R := (b*y-a)*(b*y+a)

theorem difference {R : Type*} [CommRing R] (x y : R) :
    num x*den y-num y*den x =
      -108 * pair x 1 y * pair (3*x-3) (x+3) y * pair (x-3) (x+1) y *
      pair (-3) x y * pair (-x-3) (x-1) y * pair (-3*x-3) (x-3) y := by
  unfold num sextic den pair
  ring

private def a : Fin 12 → ℤ := ![1,-1,3,-3,1,-1,0,0,-1,1,-3,3]
private def b : Fin 12 → ℤ := ![0,0,-3,3,-3,3,-3,3,-3,3,-3,3]
private def c : Fin 12 → ℤ := ![0,0,1,1,1,1,1,1,1,1,1,1]
private def d : Fin 12 → ℤ := ![1,1,3,3,1,1,0,0,-1,-1,-3,-3]

def imageNum {R : Type*} [CommRing R] (x : R) (i : Fin 12) := (a i:R)*x+b i
def imageDen {R : Type*} [CommRing R] (x : R) (i : Fin 12) := (c i:R)*x+d i

/-- The first of the twelve comparisons is ordinary equality. -/
theorem identity_branch {R : Type*} [CommRing R] (x y : R) :
    imageDen x 0 * y - imageNum x 0 = y-x := by
  simp [imageDen,imageNum,a,b,c,d]

/-- Product of all distinct exceptional factors, with each written out. -/
def mask {R : Type*} [CommRing R] (x : R) : R :=
  x*(x+1)*(x-1)*(x+3)*(x-3)*(x^2+3)*(x^2-3)*(x^2+6*x-3)*(x^2-6*x-3)

private theorem nonzero_table {K : Type*} [Field K] {x : K} (regular : mask x≠0) :
    x≠0 ∧ x+1≠0 ∧ x-1≠0 ∧ x+3≠0 ∧ x-3≠0 ∧ x^2+3≠0 ∧ x^2-3≠0 ∧
      x^2+6*x-3≠0 ∧ x^2-6*x-3≠0 := by
  simpa only [mask,mul_ne_zero_iff,and_assoc] using regular

theorem denominator_ne {K : Type*} [Field K] {x : K} (regular : mask x≠0) (i : Fin 12) :
    imageDen x i≠0 := by
  obtain ⟨a,b,c,d,e,_⟩ := nonzero_table regular
  fin_cases i <;> simp_all [imageDen,TwelveResidueCollision.c,TwelveResidueCollision.d,sub_eq_add_neg]

/-- For each distinct pair of maps, their cross difference divides a common
polynomial after multiplication by a nonzero small scalar. The finite table
contains only integer polynomial identities. -/
private def h2 : Fin 7 → ℤ := ![1,0,1,1,1,1,1]
private def h1 : Fin 7 → ℤ := ![0,1,6,2,0,-2,-6]
private def h0 : Fin 7 → ℤ := ![3,0,-3,-3,-3,-3,-3]

private def basic {R : Type*} [CommRing R] (x : R) (k : Fin 7) :=
  (h2 k:R)*x^2+(h1 k:R)*x+h0 k

private def table (i j : Fin 12) : ℤ × Fin 7 :=
  let A := a i*c j-a j*c i
  let B := a i*d j+b i*c j-a j*d i-b j*c i
  let D := b i*d j-b j*d i
  if A=0 then (B,1) else if D=3*A then (A,0) else
    (A,if B=6*A then 2 else if B=2*A then 3 else if B=0 then 4 else if B= -2*A then 5 else 6)

private theorem coeffs (i j : Fin 12) (different : i≠j) : (table i j).1 ∣ (24:ℤ) :=
  (by decide +kernel : ∀ i j : Fin 12, i≠j → (table i j).1 ∣ (24:ℤ)) i j different

private theorem table_spec : ∀ i j : Fin 12,
    a i*c j-a j*c i=(table i j).1*h2 (table i j).2 ∧
    a i*d j+b i*c j-a j*d i-b j*c i=(table i j).1*h1 (table i j).2 ∧
    b i*d j-b j*d i=(table i j).1*h0 (table i j).2 := by decide +kernel

attribute [local irreducible] table

private theorem cross {K : Type*} [Field K] (x : K) (i j : Fin 12) :
    imageNum x i * imageDen x j - imageNum x j * imageDen x i =
      ((table i j).1:K)*basic x (table i j).2 := by
  obtain ⟨p,q,r⟩ := table_spec i j
  replace p := congrArg (Int.cast : ℤ → K) p
  replace q := congrArg (Int.cast : ℤ → K) q
  replace r := congrArg (Int.cast : ℤ → K) r
  push_cast at p q r
  unfold imageNum imageDen basic
  linear_combination x^2*p+x*q+r

private theorem basic_ne {K : Type*} [Field K] {x : K} (reg : mask x≠0) (k : Fin 7) :
    basic x k≠0 := by
  obtain ⟨a,b,c,d,e,f,g,h,i⟩ := nonzero_table reg
  have l := mul_ne_zero d c
  have r := mul_ne_zero e b
  fin_cases k <;> simp [basic,h0,h1,h2] <;>
    ring_nf at f g h i l r ⊢ <;> assumption

theorem distinct_images {K : Type*} [Field K] (char : (24:K)≠0) {x : K} (reg : mask x≠0) :
    Function.Injective (fun i : Fin 12 => imageNum x i / imageDen x i) := by
  intro i j eq
  by_contra bad
  have z := (div_eq_div_iff (denominator_ne reg i) (denominator_ne reg j)).mp eq
  have diff := sub_eq_zero.mpr z
  rw [cross] at diff
  have scalar := (mul_eq_zero.mp diff).resolve_right (basic_ne reg _)
  obtain ⟨v,hv⟩ := coeffs i j bad
  have out := congrArg (Int.cast : ℤ → K) hv
  push_cast at out
  exact char (by simpa [scalar] using out)

/-- The twelve bilinear comparisons can be charged as a single equality
of rational values after the two values have been computed. -/
theorem product_identity {K : Type*} [Field K] (x y : K) :
    num x*den y-num y*den x =
      -108 * ∏ i : Fin 12, (imageDen x i*y-imageNum x i) := by
  rw [difference]
  simp [Fin.prod_univ_succ,imageDen,imageNum,a,b,c,d,pair]
  ring

theorem equality_iff {K : Type*} [Field K] (char : (108:K)≠0) {x : K} (reg : mask x≠0) (y : K) :
    num x*den y=num y*den x ↔ ∃ i : Fin 12, y=imageNum x i/imageDen x i := by
  rw [←sub_eq_zero,product_identity,mul_eq_zero]
  simp only [neg_eq_zero,char,false_or,Finset.prod_eq_zero_iff,mem_univ,true_and]
  apply exists_congr
  intro i
  rw [sub_eq_zero,eq_div_iff (denominator_ne reg i),mul_comm y]

/-- On a regular residue the fiber over a prime field has exactly twelve elements. -/
theorem fiber_card {p : ℕ} [Fact p.Prime] (large : 108<p) {x : ZMod p} (reg : mask x≠0) :
    (univ.filter (fun y => num x*den y=num y*den x)).card=12 := by
  have char (n : ℕ) (hn : 0<n) (small : n≤108) : (n:ZMod p)≠0 := by
    rw [Ne, ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact Nat.not_dvd_of_pos_of_lt hn (small.trans_lt large)
  have equal : univ.filter (fun y => num x*den y=num y*den x) =
      univ.image (fun i : Fin 12 => imageNum x i/imageDen x i) := by
    ext y
    simp only [mem_filter,mem_univ,true_and,mem_image]
    rw [equality_iff (by exact_mod_cast char 108 (by decide) (by decide)) reg]
    exact exists_congr (fun i => eq_comm)
  rw [equal,card_image_of_injective _ (distinct_images (by exact_mod_cast char 24 (by decide) (by decide)) reg)]
  simp

/-- At most thirteen residues need to be excluded for regularity. -/
theorem exceptions {p : ℕ} [Fact p.Prime] :
    (univ.filter fun x : ZMod p => mask x=0).card≤13 := by
  let P : (ZMod p)[X] := mask X
  have mon : P.Monic := by unfold P mask; monicity!
  have deg : P.natDegree≤13 := by unfold P mask; compute_degree
  by_contra! more
  apply mon.ne_zero
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P _ _ (deg.trans_lt more)
  intro i hi
  simpa [P,mask] using (mem_filter.mp hi).2

private theorem sextic_factors {K : Type*} [Field K] (x : K) :
    sextic x=(x^2-3)*(x^2+6*x-3)*(x^2-6*x-3) := by unfold sextic; ring

private theorem boundary {K : Type*} [Field K] (x : K) :
    den x-num x=108*(x*(x+1)*(x-1)*(x+3)*(x-3))^2 := by unfold den num sextic; ring

theorem regular_iff {K : Type*} [Field K] (char : (108:K)≠0) (x : K) :
    mask x≠0 ↔ den x≠0 ∧ num x≠0 ∧ den x≠num x := by
  rw [←sub_ne_zero (a:=den x) (b:=num x),boundary]
  simp only [mask,den,num,sextic_factors,mul_ne_zero_iff,ne_eq,OfNat.ofNat_ne_zero,
    not_false_eq_true,pow_ne_zero_iff,char,true_and]
  tauto

private theorem no_common_zero {K : Type*} [Field K] (char : (864:K)≠0) {y : K}
    (z : den y=0) : num y≠0 := by
  have yz : y^2+3=0 := by simpa [den] using z
  have repr : sextic y=(y^2+3)*(y^4-48*y^2+279)-864 := by unfold sextic; ring
  simp [num,repr,yz,char]

theorem regular_partner {K : Type*} [Field K] (c108 : (108:K)≠0) (c864 : (864:K)≠0)
    {x y : K} (rx : mask x≠0) (eq : num x*den y=num y*den x) : mask y≠0 := by
  obtain ⟨dx,nx,distinct⟩ := (regular_iff c108 x).mp rx
  have dy : den y≠0 := by
    intro z
    rw [z,mul_zero] at eq
    exact no_common_zero c864 z ((mul_eq_zero.mp eq.symm).resolve_right dx)
  apply (regular_iff c108 y).mpr
  refine ⟨dy,?_,?_⟩
  · intro z
    rw [z,zero_mul] at eq
    exact mul_ne_zero nx dy eq
  · intro same
    rw [←same,mul_comm (den y)] at eq
    exact distinct ((mul_right_cancel₀ dy eq).symm)

noncomputable def regulars (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  univ.filter fun x => mask x≠0

theorem regular_count (p : ℕ) [Fact p.Prime] : p≤(regulars p).card+13 := by
  have all := filter_card_add_filter_neg_card_eq_card (s:=univ) (fun x : ZMod p => mask x=0)
  simp only [card_univ,ZMod.card] at all
  have exc := exceptions (p:=p)
  change (univ.filter fun x : ZMod p => mask x=0).card + (regulars p).card = p at all
  omega

theorem regular_fiber {p : ℕ} [Fact p.Prime] (big : 864<p) {x : ZMod p} (rx : x∈regulars p) :
    ((regulars p).filter (fun y => num x*den y=num y*den x)).card=12 := by
  have ch (n : ℕ) (hn : 0<n) (small : n≤864) : (n:ZMod p)≠0 := by
    rw [Ne,ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact Nat.not_dvd_of_pos_of_lt hn (small.trans_lt big)
  have gx := (mem_filter.mp rx).2
  have eq : (regulars p).filter (fun y => num x*den y=num y*den x) =
      univ.filter (fun y => num x*den y=num y*den x) := by
    ext y
    simp only [regulars,mem_filter,mem_univ,true_and,and_iff_right_iff_imp]
    exact regular_partner (by exact_mod_cast ch 108 (by decide) (by decide))
      (by exact_mod_cast ch 864 (by decide) (by decide)) gx
  rw [eq]
  exact fiber_card (by omega) gx

end PrimeFactors.TwelveResidueCollision
