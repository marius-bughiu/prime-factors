import PrimeFactors.GeometricDoubleMatch
import Mathlib.Tactic.ReduceModChar

/-! Replaying the three readings directly from the product and the public base. -/
namespace PrimeFactors.GeometricReadoutExamples
open Finset Polynomial GeometricDoubleMatch

set_option maxRecDepth 8192

structure Jet (R : Type*) where
  value : R
  slope : R
  curvature : R
  deriving DecidableEq

def step {R : Type*} [CommRing R] (u v : Jet R) : Jet R :=
  ⟨u.value*v.value, u.slope*v.value+u.value*v.slope,
    u.curvature*v.value+u.slope*v.slope+u.value*v.curvature⟩

def jet {R : Type*} [CommRing R] (y g z : R) : ℕ → Jet R
  | 0 => ⟨1,0,0⟩
  | i+1 => step (jet y g z i)
      ⟨y-g^i, z*y-i*g^i, -(i.choose 2 : R)*g^i⟩

private noncomputable def takeJet {R : Type*} [CommRing R] (f : R[X]) : Jet R :=
  ⟨f.coeff 0, f.coeff 1, f.coeff 2⟩

private theorem take_mul {R : Type*} [CommRing R] (f h : R[X]) :
    takeJet (f*h) = step (takeJet f) (takeJet h) := by
  have one : Finset.antidiagonal 1 = {(0,1),(1,0)} := by decide
  have two : Finset.antidiagonal 2 = {(0,2),(1,1),(2,0)} := by decide
  dsimp only [takeJet,step]
  have different : (1 : ℕ×ℕ) ≠ (2,0) := by decide
  congr 1 <;> rw [coeff_mul] <;> simp [one,two,different,add_comm,add_left_comm,add_assoc]

theorem coefficients {R : Type*} [CommRing R] (y g z : R) (n : ℕ) :
    takeJet (∏ i ∈ range n, factor y g z i) = jet y g z n := by
  induction n with
  | zero => simp [takeJet,jet,Polynomial.coeff_one]
  | succ n ih =>
    rw [prod_range_succ,take_mul,ih]
    congr 1
    dsimp only [takeJet, GeometricDoubleMatch.factor]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_X_mul_zero,
      Polynomial.coeff_C,ite_true,ite_false,OfNat.ofNat_ne_zero,add_zero,zero_add]
    simp

theorem curvature_eq {R : Type*} [CommRing R] (y g z : R) (n : ℕ) :
    reading (range n) y g z = (jet y g z n).curvature :=
  congrArg Jet.curvature (coefficients y g z n)

private abbrev N := 34393
private abbrev R := ZMod N

/-- The global simple-root derivative vanishes in both directions. Three second
coefficients nevertheless split the public synthetic product. -/
theorem double_split :
    (23:R)^(N+1-371)=12167 ∧
    jet (12167:R) 23 0 23 = ⟨0,0,11234⟩ ∧
    jet (12167:R) 23 1 23 = ⟨0,0,21456⟩ ∧
    jet (12167:R) 23 (-1) 23 = ⟨0,0,9974⟩ ∧
    (let c := reading (range 23) (12167:R) 23
     leading c=8962 ∧ linear c=22911 ∧ discriminant c=24758 ∧
       Nat.gcd N ((9:R)^2*discriminant c - (leading c)^2).val = 163) ∧
    Nat.Prime 163 ∧ Nat.Prime 211 ∧ 163*211=N := by
  refine ⟨by unfold N R; reduce_mod_char, by decide +kernel, by decide +kernel, by decide +kernel, ?_, by norm_num1, by norm_num1, rfl⟩
  simp only [leading,linear,discriminant,curvature_eq]
  decide +kernel

/-- Equal local order cofactors yield the full modulus in the test. The negative
sign then recovers the genuine index 17 on this selected example. -/
theorem equal_cofactors :
    let n := 30353
    let y := (22 : ZMod 30353)^(n+1-349)
    let c := reading (range 21) y 22
    let A := leading c
    let B := linear c
    let D := discriminant c
    A=21802 ∧ B=5681 ∧ D=24774 ∧ 14^2*D-A^2=0 ∧
      2*14*A*16687=1 ∧ ((14*B-A)*16687).val=17 ∧ 349+17=127+239 ∧
      Nat.Prime 127 ∧ Nat.Prime 239 ∧ 127*239=n := by
  dsimp only
  have base : (22:ZMod 30353)^(30353+1-349)=5259 := by reduce_mod_char
  rw [base]
  simp only [leading,linear,discriminant,curvature_eq]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide, by norm_num1, by norm_num1, by decide⟩

end PrimeFactors.GeometricReadoutExamples
