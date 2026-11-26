import PrimeFactors.CubicTraceSquare
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! Two rational and norm squares forced at a public base, followed by an
exact test of the remaining square condition in the cubic field. -/
namespace PrimeFactors.CubicForcedUnits
open Polynomial

/-- All coefficients and the base zero are determined by the odd input. -/
def sign (n : ℤ) : ℤ := if n%4=3 then 1 else -1
def parameter (n : ℤ) : ℤ := (n+sign n)/4

theorem parameters {n : ℤ} (odd : n%2=1) :
    (sign n=1 ∨ sign n= -1) ∧ 4*parameter n-sign n=n := by
  unfold parameter sign
  split <;> omega

noncomputable def poly {R : Type*} [CommRing R] (w H : R) : R[X] :=
  (X+1)*(X+4)*(X+C w)-C H

private theorem monic {R : Type*} [CommRing R] [Nontrivial R] (w H : R) : (poly w H).Monic := by
  unfold poly
  monicity!

private theorem degree (w H : ℚ) : (poly w H).natDegree=3 := by
  unfold poly
  compute_degree!

theorem represented {n : ℤ} (odd : n%2=1) : (poly (parameter n) (sign n)).eval 0=n := by
  simpa [poly] using (parameters odd).2

private theorem no_integer_root {w H : ℤ} (unit : H=1 ∨ H= -1) (z : ℤ) :
    (z+1)*(z+4)*(z+w) ≠ H := by
  intro eq
  have d1 : z+1 ∣ H := ⟨(z+4)*(z+w),by rw [← eq]; ring⟩
  have d4 : z+4 ∣ H := ⟨(z+1)*(z+w),by rw [← eq]; ring⟩
  have hn : H≠0 := by omega
  have h1 := Int.natAbs_le_of_dvd_ne_zero d1 hn
  have h4 := Int.natAbs_le_of_dvd_ne_zero d4 hn
  rcases unit with rfl|rfl <;> omega

/-- This cubic is irreducible for every integer parameter, including negative
and repeated shifts. A rational root would be integral, forcing two integers
whose difference is three to divide a unit. -/
theorem irreducible (w : ℤ) {H : ℤ} (unit : H=1 ∨ H= -1) :
    Irreducible (poly (w:ℚ) (H:ℚ)) := by
  apply irreducible_of_degree_le_three_of_not_isRoot (by rw [degree]; decide)
  intro q root
  have eq : (q+1)*(q+4)*(q+w)=H := by simpa [IsRoot,poly,sub_eq_zero] using root
  have ann : aeval q (poly w H)=0 := by
    simp only [poly,map_sub,map_add,map_mul,map_one,map_ofNat,aeval_X,aeval_C,sub_eq_zero]
    exact eq
  obtain ⟨z,hz,_⟩ := exists_integer_of_is_root_of_monic (monic w H) ann
  change q=(z:ℚ) at hz
  rw [hz] at eq
  apply no_integer_root unit z
  exact_mod_cast eq

abbrev K (w H : ℚ) := AdjoinRoot (poly w H)
noncomputable abbrev root (w H : ℚ) : K w H := AdjoinRoot.root (poly w H)
private noncomputable abbrev scalar (w H : ℚ) := algebraMap ℚ (K w H)
noncomputable def beta (w H : ℚ) : K w H := (root w H+1)*(root w H+4)
noncomputable def eta (w H : ℚ) : K w H := scalar w H H*(root w H+scalar w H w)

theorem defining (w H : ℚ) :
    (root w H+1)*(root w H+4)*(root w H+scalar w H w)=scalar w H H := by
  have eq : aeval (root w H) (poly w H)=0 := by rw [AdjoinRoot.aeval_eq,AdjoinRoot.mk_self]
  unfold poly at eq
  simpa only [map_sub,map_add,map_mul,map_one,map_ofNat,aeval_X,aeval_C,sub_eq_zero] using eq

theorem inverse_units {w H : ℚ} (unit : H=1 ∨ H= -1) : beta w H*eta w H=1 := by
  unfold beta eta
  calc
    _ = scalar w H H*((root w H+1)*(root w H+4)*(root w H+scalar w H w)) := by ring
    _ = 1 := by rw [defining,←map_mul]; rcases unit with rfl|rfl <;> simp

private theorem inverse_squares {R : Type*} [CommRing R] {a b : R} (inv : a*b=1) :
    IsSquare a → IsSquare b := by
  rintro ⟨s,hs⟩
  refine ⟨b*s,?_⟩
  calc
    b = b*(a*b) := by rw [inv,mul_one]
    _ = _ := by rw [hs]; ring

theorem beta_square_iff_eta {w H : ℚ} (unit : H=1 ∨ H= -1) :
    IsSquare (beta w H) ↔ IsSquare (eta w H) :=
  ⟨inverse_squares (inverse_units unit),inverse_squares ((mul_comm ..).trans (inverse_units unit))⟩

private noncomputable def basis (w H : ℚ) : Basis (Fin 3) ℚ (K w H) :=
  (AdjoinRoot.powerBasis' (monic w H)).basis.reindex (finCongr (degree w H))

private theorem basis_apply (w H : ℚ) (i : Fin 3) : basis w H i=root w H^i.val := by
  rw [basis,Basis.reindex_apply,PowerBasis.basis_eq_pow]
  rfl

private noncomputable def elem (w H a b c : ℚ) : K w H :=
  scalar w H a + scalar w H b*root w H + scalar w H c*root w H^2

private theorem coord (w H a b c : ℚ) (i : Fin 3) :
    (basis w H).repr (elem w H a b c) i = ![a,b,c] i := by
  have coords : (basis w H).equivFun.symm ![a,b,c] = elem w H a b c := by
    rw [Basis.equivFun_symm_apply]
    simp [elem,basis_apply,Fin.sum_univ_succ,Algebra.smul_def,add_assoc,scalar]
  change (basis w H).equivFun (elem w H a b c) i=_
  rw [←coords,LinearEquiv.apply_symm_apply]

private def matrix (w H t : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![t,0,H-4*w; 1,t,-(5*w+4); 0,1,t-w-5]

private theorem shifted_matrix (w H t : ℚ) :
    Algebra.leftMulMatrix (basis w H) (root w H+scalar w H t)=matrix w H t := by
  have first : root w H+scalar w H t=elem w H t 1 0 := by simp [elem,add_comm]
  have second : (root w H+scalar w H t)*root w H=elem w H 0 t 1 := by simp [elem]; ring
  have third : (root w H+scalar w H t)*root w H^2=elem w H (H-4*w) (-(5*w+4)) (t-w-5) := by
    simp only [elem,map_add,map_sub,map_neg,map_mul,map_ofNat]
    linear_combination defining w H
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul,basis_apply]
  fin_cases j
  · change (basis w H).repr ((root w H+scalar w H t)*root w H^0) i=_
    rw [pow_zero,mul_one,first,coord]
    fin_cases i <;> rfl
  · change (basis w H).repr ((root w H+scalar w H t)*root w H^1) i=_
    rw [pow_one,second,coord]
    fin_cases i <;> rfl
  · change (basis w H).repr ((root w H+scalar w H t)*root w H^2) i=_
    rw [third,coord]
    fin_cases i <;> rfl

/-- The two individual *field* norms are the same prescribed sign.
Their images at zero are 1 and 4. -/
theorem norms (w H : ℚ) :
    Algebra.norm ℚ (root w H+1)=H ∧ Algebra.norm ℚ (root w H+4)=H := by
  have cal (t : ℚ) : Algebra.norm ℚ (root w H+scalar w H t)=(t-1)*(t-4)*(t-w)+H := by
    rw [Algebra.norm_eq_matrix_det (basis w H),shifted_matrix,matrix,Matrix.det_fin_three]
    simp
    ring
  constructor
  · simpa using cal 1
  · simpa using cal 4


private def tr3 (M : Matrix (Fin 3) (Fin 3) ℚ) := M 0 0+M 1 1+M 2 2

private def second3 (M : Matrix (Fin 3) (Fin 3) ℚ) :=
  M 0 0*M 1 1-M 0 1*M 1 0 + (M 0 0*M 2 2-M 0 2*M 2 0) + (M 1 1*M 2 2-M 1 2*M 2 1)

/-- The trace of a three-dimensional matrix and its determinant satisfy the
square-root quartic for its square. No diagonalization is assumed. -/
private theorem trace_identity (M : Matrix (Fin 3) (Fin 3) ℚ) :
    ((tr3 M)^2 - tr3 (M*M))^2 - 8*M.det*tr3 M - 4*second3 (M*M)=0 := by
  simp [tr3,second3,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.det_fin_three]
  ring

/-- Every genuine root of the unit in the cubic field produces a rational
root of the sparse quartic. The sign picks determinant +1. -/
theorem rational_trace {w H : ℚ} (unit : H=1 ∨ H= -1) (sq : IsSquare (eta w H)) :
    ∃ u : ℚ, u^4-2*(H*(2*w-5))*u^2-8*u+9=0 := by
  obtain ⟨δ,hh⟩ := sq
  let M := Algebra.leftMulMatrix (basis w H) δ
  let T := H • matrix w H w
  have square : M*M=T := by
    change Algebra.leftMulMatrix (basis w H) δ * Algebra.leftMulMatrix (basis w H) δ = _
    rw [←map_mul,←hh,eta,←Algebra.smul_def H, map_smul, shifted_matrix]
  have values : tr3 T=H*(2*w-5) ∧ second3 T=(w-1)*(w-4) ∧ T.det=1 := by
    rcases unit with rfl|rfl <;> dsimp [T] <;> refine ⟨?_,?_,?_⟩ <;>
      simp [tr3,second3,matrix,Matrix.det_fin_three,Matrix.smul_apply] <;> ring
  have char := trace_identity M
  rw [square,values.1,values.2.1] at char
  have d : M.det^2=1 := by rw [pow_two,←Matrix.det_mul,square,values.2.2]
  have choices := sq_eq_sq_iff_eq_or_eq_neg.mp (show M.det^2=(1:ℚ)^2 by simpa using d)
  have diff : (H*(2*w-5))^2-4*((w-1)*(w-4))=9 := by rcases unit with rfl|rfl <;> ring
  rcases choices with pos|neg
  · refine ⟨tr3 M,?_⟩
    rw [pos] at char
    linear_combination char-diff
  · refine ⟨-tr3 M,?_⟩
    rw [neg] at char
    linear_combination char-diff

/-- The integer trace divides nine. Exactly three integer first coefficients
admit a rational root. In particular the trace -9 must be retained. -/
theorem trace_cases {A : ℤ} {q : ℚ} (rootQ : q^4-2*(A:ℚ)*q^2-8*q+9=0) :
    A=1 ∨ A=9 ∨ A=41 := by
  let Q : ℤ[X] := X^4-C (2*A)*X^2-8*X+9
  have mon : Q.Monic := by dsimp [Q]; monicity!
  have ann : aeval q Q=0 := by
    simp only [Q,map_add,map_sub,map_mul,map_pow,aeval_X,aeval_C,map_ofNat,Int.cast_mul,Int.cast_ofNat]
    exact rootQ
  obtain ⟨u,hu,_⟩ := exists_integer_of_is_root_of_monic mon ann
  change q=(u:ℚ) at hu
  rw [hu] at rootQ
  have integer : u^4-2*A*u^2-8*u+9=0 := by exact_mod_cast rootQ
  have dvd : u∣9 := ⟨8+2*A*u-u^3,by linear_combination integer⟩
  have bound := Int.natAbs_le_of_dvd_ne_zero dvd (by decide)
  have low : -9≤u := by omega
  have high : u≤9 := by omega
  interval_cases u <;> norm_num at integer <;> omega

private theorem equation {w H : ℚ} (unit : H=1 ∨ H= -1) :
    (eta w H)^3 - scalar w H (H*(2*w-5))*(eta w H)^2 +
      scalar w H ((w-1)*(w-4))*eta w H - 1 = 0 := by
  have rel := defining w H
  rcases unit with rfl|rfl <;>
    simp only [eta,map_add,map_sub,map_neg,map_mul,map_one,map_ofNat] at rel ⊢
  · linear_combination rel
  · linear_combination -rel

private theorem square_of_coeff {F : Type*} [Field F] [CharZero F] {x B : F}
    {A : F} (ann : x^3-A*x^2+B*x-1=0) (diff : A^2-4*B=9)
    (good : A=1 ∨ A=9 ∨ A=41) : IsSquare x := by
  apply (isSquare_iff_exists_sq _).mpr
  rcases good with rfl|rfl|rfl
  · have eq : B= -2 := by linear_combination -diff/4
    rw [eq] at ann
    exact ⟨x^2-x-1,by linear_combination -(x-1)*ann⟩
  · have eq : B=18 := by linear_combination -diff/4
    rw [eq] at ann
    refine ⟨(-x^2+5*x-1)/3,?_⟩
    field_simp
    linear_combination -(x-1)*ann
  · have eq : B=418 := by linear_combination -diff/4
    rw [eq] at ann
    refine ⟨(x^2-61*x+9)/181,?_⟩
    field_simp
    linear_combination -(x-81)*ann

/-- Exact square criterion in the full rational cubic field, permitting
arbitrary denominators in a proposed square root. -/
theorem square_iff (w H : ℤ) (unit : H=1 ∨ H= -1) :
    IsSquare (beta (w:ℚ) (H:ℚ)) ↔ H*(2*w-5)=1 ∨ H*(2*w-5)=9 ∨ H*(2*w-5)=41 := by
  have signQ : (H:ℚ)=1 ∨ (H:ℚ)= -1 := by exact_mod_cast unit
  letI : Fact (Irreducible (poly (w:ℚ) (H:ℚ))) := ⟨irreducible w unit⟩
  rw [beta_square_iff_eta signQ]
  constructor
  · intro sq
    obtain ⟨q,hq⟩ := rational_trace signQ sq
    exact trace_cases (A:=H*(2*w-5)) (by push_cast; exact hq)
  · intro good
    apply square_of_coeff (equation (w:=(w:ℚ)) signQ)
    · have eq : ((H:ℚ)*(2*w-5))^2-4*((w-1:ℚ)*(w-4))=9 := by
        rcases signQ with h|h <;> rw [h] <;> ring
      simpa only [map_pow,map_mul,map_sub,map_ofNat] using congrArg (scalar (w:ℚ) (H:ℚ)) eq
    · have mapped {k : ℤ} (eq : H*(2*w-5)=k) :
          scalar (w:ℚ) (H:ℚ) ((H:ℚ)*(2*w-5)) = (k:K (w:ℚ) (H:ℚ)) := by
        have eqQ : (H:ℚ)*(2*w-5)=(k:ℚ) := by exact_mod_cast eq
        rw [eqQ,map_intCast]
      rcases good with h|h|h
      · left; simpa using mapped h
      · right; left; simpa using mapped h
      · right; right; simpa using mapped h

/-- The sole positive product of distinct odd primes on this list is 91. -/
theorem positive_inputs {n : ℤ} (pos : 0<n) (odd : n%2=1) :
    IsSquare (beta (parameter n:ℚ) (sign n:ℚ)) ↔ n=9 ∨ n=11 ∨ n=27 ∨ n=91 := by
  obtain ⟨hs,rep⟩ := parameters odd
  rw [square_iff _ _ hs]
  rcases hs with s|s <;> rw [s] at rep ⊢ <;> simp only [one_mul,neg_one_mul] at * <;> omega

/-- Beyond the exceptional inputs the two rows always pass both numerical
square tests, and their cubic-field product is always a nonsquare. -/
theorem large_inputs {n : ℤ} (large : 91<n) (odd : n%2=1) :
    let w : ℚ := parameter n
    let H : ℚ := sign n
    (1:ℚ)*4=2^2 ∧ Algebra.norm ℚ (root w H+1)*Algebra.norm ℚ (root w H+4)=1 ∧
      ¬IsSquare (beta w H) := by
  dsimp only
  have normsQ := norms (parameter n:ℚ) (sign n:ℚ)
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [normsQ.1,normsQ.2]
    rcases (parameters odd).1 with h|h <;> rw [h] <;> norm_num
  · rw [positive_inputs (by omega) odd]
    omega

/-- The exceptional semiprime has a genuine field square. Its power-basis
numerator and denominator at base zero specialize to the same sign at 7 and 13. -/
theorem example_91 :
    let x := root 23 1
    (181:K 23 1)^2*beta 23 1=(9*x^2+46*x-2)^2 ∧
    ((-2:ℤ)-2*181).natAbs.gcd 91=91 ∧ ((-2:ℤ)+2*181).natAbs.gcd 91=1 ∧
    Nat.Prime 7 ∧ Nat.Prime 13 ∧ 7*13=91 := by
  refine ⟨?_,by decide,by decide,by decide,by decide,by decide⟩
  have eq := defining 23 1
  norm_num only [map_ofNat,map_one] at eq
  unfold beta
  linear_combination -(81*root 23 1-1440)*eq

end PrimeFactors.CubicForcedUnits
