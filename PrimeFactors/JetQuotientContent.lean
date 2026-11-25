import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

namespace PrimeFactors.JetQuotientContent

open Polynomial

noncomputable def jetIdeal (n : ℤ) (H : ℤ[X]) : Ideal ℤ[X] :=
  Ideal.span {C (n^2),C n * X,H,X^2}

/-- The four rows (N²,0), (0,N), (H₀,H₁), and (0,H₀). -/
def pairRel (n a b x y : ℤ) : Prop :=
  ∃ A B E F : ℤ, x=n^2*A+a*E ∧ y=n*B+b*E+a*F

private theorem generators {n : ℤ} {H P : ℤ[X]} :
    P∈jetIdeal n H ↔ ∃ A B E F : ℤ[X], P=A*C (n^2)+B*(C n*X)+E*H+F*X^2 := by
  unfold jetIdeal
  constructor
  · intro h
    obtain ⟨A,R,hR,hP⟩ := Ideal.mem_span_insert.mp h
    obtain ⟨B,S,hS,hR'⟩ := Ideal.mem_span_insert.mp hR
    obtain ⟨E,F,hS'⟩ := Ideal.mem_span_pair.mp hS
    exact ⟨A,B,E,F,by rw [hP,hR',←hS']; ring⟩
  · rintro ⟨A,B,E,F,rfl⟩
    exact Ideal.mem_span_insert.mpr ⟨A,_,Ideal.mem_span_insert.mpr
      ⟨B,_,Ideal.mem_span_pair.mpr ⟨E,F,rfl⟩,rfl⟩,by ring⟩

/-- Higher coefficients of either polynomial give no additional relations. -/
theorem mem_iff {n : ℤ} {H P : ℤ[X]} :
    P∈jetIdeal n H ↔ pairRel n (H.coeff 0) (H.coeff 1) (P.coeff 0) (P.coeff 1) := by
  have z1 (z : ℤ) : (z:ℤ[X]).coeff 1=0 := by
    rw [←C_eq_intCast (R:=ℤ)]; simp only [coeff_C,one_ne_zero,if_false]
  have n0 : ((n:ℤ[X])^2).coeff 0 = n^2 := by
    rw [←Int.cast_pow,Polynomial.intCast_coeff_zero,Int.cast_id]
  have n1 : ((n:ℤ[X])^2).coeff 1 = 0 := by rw [←Int.cast_pow,z1]
  rw [generators]
  constructor
  · rintro ⟨A,B,E,F,rfl⟩
    refine ⟨A.coeff 0,n*A.coeff 1+B.coeff 0,E.coeff 0,E.coeff 1,?_,?_⟩ <;>
      simp [-map_pow,mul_coeff_one,coeff_C,coeff_X_pow,n0,n1,z1] <;> ring
  · rintro ⟨a,b,e,f,hx,hy⟩
    let Z := C a*C (n^2)+C b*(C n*X)+(C e+C f*X)*H
    have z0 : Z.coeff 0=P.coeff 0 := by dsimp [Z]; simp [-map_pow,coeff_C,hx,n0,n1,z1]; ring
    have z1 : Z.coeff 1=P.coeff 1 := by dsimp [Z]; simp [-map_pow,coeff_C,hy,mul_coeff_one,n0,n1,z1]; ring
    have div : X^2 ∣ P-Z := X_pow_dvd_iff.mpr (by
      intro i hi
      interval_cases i <;> simp [z0,z1])
    obtain ⟨F,hF⟩ := div
    refine ⟨C a,C b,C e+C f*X,F,?_⟩
    change P=Z+F*X^2
    linear_combination hF

/-- A lower triangular presentation obtained from the two horizontal rows. -/
private theorem triangular {n a b g m p s t x y : ℤ}
    (ng : n^2=g*m) (ag : a=g*p) (bez : m*s+p*t=1) :
    pairRel n a b x y ↔
      ∃ k A B D : ℤ, x=g*k ∧ y=b*t*k+n*A+a*B+(m*b)*D := by
  constructor
  · rintro ⟨A,B,E,F,hx,hy⟩
    refine ⟨m*A+p*E,B,F,s*E-t*A,by rw [hx,ng,ag]; ring,?_⟩
    linear_combination hy - b*E*bez
  · rintro ⟨k,A,B,D,hx,hy⟩
    refine ⟨s*k-p*D,A,t*k+m*D,B,?_,?_⟩
    · rw [hx,ng,ag]; linear_combination -g*k*bez
    · rw [hy]; ring

private theorem three_gcd (n a m y : ℤ) :
    (∃ A B D : ℤ, y=n*A+a*B+m*D) ↔ (Int.gcd (Int.gcd n a) m:ℤ)∣y := by
  let l := (Int.gcd n a:ℤ)
  let h := (Int.gcd l m:ℤ)
  have ll : l∣n := Int.gcd_dvd_left
  have lr : l∣a := Int.gcd_dvd_right
  have hl : h∣l := Int.gcd_dvd_left
  have hr : h∣m := Int.gcd_dvd_right
  constructor
  · rintro ⟨A,B,D,rfl⟩
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left (hl.trans ll) _) (dvd_mul_of_dvd_left (hl.trans lr) _))
      (dvd_mul_of_dvd_left hr _)
  · rintro ⟨j,hj⟩
    refine ⟨Int.gcdA n a*Int.gcdA l m*j,Int.gcdB n a*Int.gcdA l m*j,Int.gcdB l m*j,?_⟩
    change y=h*j at hj
    have h1 : h=l*Int.gcdA l m+m*Int.gcdB l m := Int.gcd_eq_gcd_ab l m
    have h2 : l=n*Int.gcdA n a+a*Int.gcdB n a := Int.gcd_eq_gcd_ab n a
    rw [hj,h1]; linear_combination (Int.gcdA l m*j)*h2

def horizontal (n a : ℤ) := Int.gcd (n^2) a
def vertical (n a b : ℤ) := Int.gcd (Int.gcd n a) ((n^2/(horizontal n a:ℤ))*b)
def shear (n a b : ℤ) := b*Int.gcdB (n^2) a

/-- Membership in the pair lattice as two exact integer divisibilities. -/
theorem pair_iff {n a b x y : ℤ} (nonzero : n≠0) :
    pairRel n a b x y ↔ ∃ k : ℤ, x=(horizontal n a:ℤ)*k ∧
      (vertical n a b:ℤ) ∣ y-shear n a b*k := by
  let g := (horizontal n a:ℤ)
  have gp : g≠0 := by
    dsimp [g,horizontal]
    exact_mod_cast (Int.gcd_pos_of_ne_zero_left a (pow_ne_zero 2 nonzero)).ne'
  let m := n^2/g
  let p := a/g
  let s := Int.gcdA (n^2) a
  let t := Int.gcdB (n^2) a
  have ng : n^2=g*m := (Int.mul_ediv_cancel' (show g∣n^2 from Int.gcd_dvd_left)).symm
  have ag : a=g*p := (Int.mul_ediv_cancel' (show g∣a from Int.gcd_dvd_right)).symm
  have raw : g=n^2*s+a*t := Int.gcd_eq_gcd_ab _ _
  have bz : m*s+p*t=1 := by
    apply mul_left_cancel₀ gp
    calc
      g*(m*s+p*t) = n^2*s+a*t := by rw [ng,ag]; ring
      _ = g*1 := by linarith only [raw]
  rw [triangular ng ag bz]
  constructor
  · rintro ⟨k,A,B,D,hx,hy⟩
    refine ⟨k,hx,(three_gcd _ _ _ _).mp ⟨A,B,D,?_⟩⟩
    change y-b*t*k=n*A+a*B+(m*b)*D
    linarith only [hy]
  · rintro ⟨k,hx,hy⟩
    obtain ⟨A,B,D,hD⟩ := (three_gcd n a (m*b) _).mpr hy
    exact ⟨k,A,B,D,hx,by change y-b*t*k=_ at hD; linarith only [hD]⟩

def minorGcd (n a b : ℤ) : ℕ :=
  Int.gcd (Int.gcd (Int.gcd (n^3) (n^2*b)) (n*a)) (a^2)

private theorem gcdCriterion (d x y : ℤ) : d∣(Int.gcd x y:ℤ) ↔ d∣x ∧ d∣y :=
  ⟨fun h => ⟨h.trans Int.gcd_dvd_left,h.trans Int.gcd_dvd_right⟩,
   fun h => Int.dvd_coe_gcd h.1 h.2⟩

/-- The index of the triangular pair presentation equals the gcd of the
nonredundant two-column minors. -/
theorem steps_product (n a b : ℤ) :
    horizontal n a * vertical n a b = minorGcd n a b := by
  let g := (horizontal n a:ℤ)
  let m := n^2/g
  let h := (vertical n a b:ℤ)
  have gn : g∣n^2 := Int.gcd_dvd_left
  have ga : g∣a := Int.gcd_dvd_right
  have ng : g*m=n^2 := Int.mul_ediv_cancel' gn
  have crit (d : ℤ) : d∣(minorGcd n a b:ℤ) ↔ ((d∣n^3 ∧ d∣n^2*b) ∧ d∣n*a) ∧ d∣a^2 := by
    simp only [minorGcd,gcdCriterion]
  have x1 : h∣n := (show h∣(Int.gcd n a:ℤ) from Int.gcd_dvd_left).trans Int.gcd_dvd_left
  have x2 : h∣a := (show h∣(Int.gcd n a:ℤ) from Int.gcd_dvd_left).trans Int.gcd_dvd_right
  have x3 : h∣m*b := Int.gcd_dvd_right
  have forwards : g*h∣(minorGcd n a b:ℤ) := by
    apply (crit _).mpr
    refine ⟨⟨⟨by simpa only [show n^3=n^2*n by ring] using mul_dvd_mul gn x1,?_⟩,
      by simpa only [mul_comm a] using mul_dvd_mul ga x1⟩,
      by simpa only [pow_two] using mul_dvd_mul ga x2⟩
    rw [←ng,mul_assoc]
    exact mul_dvd_mul (dvd_refl _) x3
  let d := (minorGcd n a b:ℤ)
  have ex := (crit d).mp (dvd_refl d)
  obtain ⟨A,B,D,comb⟩ := (three_gcd n a (m*b) h).mpr (dvd_refl _)
  let s := Int.gcdA (n^2) a
  let t := Int.gcdB (n^2) a
  have gz : g=n^2*s+a*t := Int.gcd_eq_gcd_ab _ _
  have dn : d∣g*n := by
    rw [gz,show (n^2*s+a*t)*n=n^3*s+(n*a)*t by ring]
    exact dvd_add (dvd_mul_of_dvd_left ex.1.1.1 _) (dvd_mul_of_dvd_left ex.1.2 _)
  have da : d∣g*a := by
    rw [gz,show (n^2*s+a*t)*a=(n*a)*(n*s)+a^2*t by ring]
    exact dvd_add (dvd_mul_of_dvd_left ex.1.2 _) (dvd_mul_of_dvd_left ex.2 _)
  have backwards : d∣g*h := by
    rw [comb,show g*(n*A+a*B+(m*b)*D)=(g*n)*A+(g*a)*B+(g*m*b)*D by ring,ng]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left dn _) (dvd_mul_of_dvd_left da _))
      (dvd_mul_of_dvd_left ex.1.1.2 _)
  dsimp only [d,g,h] at forwards backwards
  exact Nat.dvd_antisymm (by exact_mod_cast forwards : horizontal n a*vertical n a b ∣ minorGcd n a b)
    (by exact_mod_cast backwards : minorGcd n a b ∣ horizontal n a*vertical n a b)

private noncomputable def linear (x y : ℤ) : ℤ[X] := C x + C y*X

private theorem coeffs (x y : ℤ) : (linear x y).coeff 0=x ∧ (linear x y).coeff 1=y := by
  simp only [linear,coeff_add,mul_coeff_zero,coeff_C_zero,coeff_X_zero,mul_zero,add_zero,
    coeff_mul_X,coeff_C,one_ne_zero,if_false,if_true,zero_add,true_and]

private theorem quotient_eq {n : ℤ} {H P Q : ℤ[X]} (nonzero : n≠0) :
    Ideal.Quotient.mk (jetIdeal n H) P = Ideal.Quotient.mk (jetIdeal n H) Q ↔
      ∃ k : ℤ, P.coeff 0-Q.coeff 0=(horizontal n (H.coeff 0):ℤ)*k ∧
        (vertical n (H.coeff 0) (H.coeff 1):ℤ)∣P.coeff 1-Q.coeff 1-shear n (H.coeff 0) (H.coeff 1)*k := by
  rw [Ideal.Quotient.eq,mem_iff,pair_iff nonzero,coeff_sub,coeff_sub]

private theorem bounded_eq {g x y:ℤ} (xl : 0≤x) (xu : x<g) (yl : 0≤y) (yu : y<g)
    (div : g∣x-y) : x=y := by
  have eq := (Int.modEq_iff_dvd.mpr div).symm
  change x%g=y%g at eq
  simpa only [Int.emod_eq_of_lt xl xu,Int.emod_eq_of_lt yl yu] using eq

/-- Every quotient class has a unique degree-one representative in a finite
rectangle. The number of classes is computed using gcd and integer arithmetic. -/
theorem quotient_card (n : ℤ) (nonzero : n≠0) (H : ℤ[X]) :
    Nat.card (ℤ[X] ⧸ jetIdeal n H) = minorGcd n (H.coeff 0) (H.coeff 1) := by
  let a := H.coeff 0
  let b := H.coeff 1
  let g := horizontal n a
  let h := vertical n a b
  let s := shear n a b
  have gp : 0<g := Int.gcd_pos_of_ne_zero_left _ (pow_ne_zero 2 nonzero)
  have lp : 0<Int.gcd n a := Int.gcd_pos_of_ne_zero_left _ nonzero
  have hp : 0<h := Int.gcd_pos_of_ne_zero_left _ (by exact_mod_cast lp.ne')
  let f (r : Fin g × Fin h) := Ideal.Quotient.mk (jetIdeal n H) (linear r.1.val r.2.val)
  have inj : Function.Injective f := by
    rintro ⟨x,y⟩ ⟨p,q⟩ same
    obtain ⟨k,hx,hy⟩ := (quotient_eq nonzero).mp same
    simp only [(coeffs ..).1,(coeffs ..).2] at hx hy
    change (x.val:ℤ)-p.val=g*k at hx
    change (h:ℤ)∣(y.val:ℤ)-q.val-s*k at hy
    have first : (x.val:ℤ)=p.val := bounded_eq (by positivity) (by exact_mod_cast x.isLt)
      (by positivity) (by exact_mod_cast p.isLt) ⟨k,hx⟩
    have zero : k=0 := by
      rw [first,sub_self] at hx
      exact (mul_eq_zero.mp hx.symm).resolve_left (by exact_mod_cast gp.ne')
    rw [zero,mul_zero,sub_zero] at hy
    have second : (y.val:ℤ)=q.val := bounded_eq (by positivity) (by exact_mod_cast y.isLt)
      (by positivity) (by exact_mod_cast q.isLt) hy
    exact Prod.ext (Fin.ext (by exact_mod_cast first)) (Fin.ext (by exact_mod_cast second))
  have onto : Function.Surjective f := by
    intro z
    obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective z
    let x := P.coeff 0
    let y := P.coeff 1
    let k := x/(g:ℤ)
    let m := y-s*k
    have gz : 0<(g:ℤ) := by exact_mod_cast gp
    have hz : 0<(h:ℤ) := by exact_mod_cast hp
    let r : Fin g := ⟨(x%(g:ℤ)).toNat,by
      have := Int.emod_lt_of_pos x gz; have := Int.emod_nonneg x gz.ne'; omega⟩
    let t : Fin h := ⟨(m%(h:ℤ)).toNat,by
      have := Int.emod_lt_of_pos m hz; have := Int.emod_nonneg m hz.ne'; omega⟩
    refine ⟨(r,t),Eq.symm ((quotient_eq nonzero).mpr ⟨k,?_,?_⟩)⟩
    · change x-(linear r.val t.val).coeff 0=g*k
      rw [(coeffs ..).1,show (r.val:ℤ)=x%g from Int.toNat_of_nonneg (Int.emod_nonneg _ gz.ne')]
      have := Int.emod_add_ediv x (g:ℤ)
      dsimp [k]; omega
    · change (h:ℤ)∣y-(linear r.val t.val).coeff 1-s*k
      rw [(coeffs ..).2,show (t.val:ℤ)=m%h from Int.toNat_of_nonneg (Int.emod_nonneg _ hz.ne')]
      refine ⟨m/h,?_⟩
      have := Int.emod_add_ediv m (h:ℤ)
      dsimp only [m] at this ⊢
      omega
  have card := Nat.card_congr (Equiv.ofBijective f ⟨inj,onto⟩)
  rw [←steps_product]
  simpa only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fin] using card.symm

end PrimeFactors.JetQuotientContent
