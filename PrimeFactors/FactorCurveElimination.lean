import PrimeFactors.HigherDivisorWindow
import Mathlib.Algebra.Polynomial.FieldDivision

namespace PrimeFactors.FactorCurveElimination

open Finset Polynomial

/-- The x^B multiple of a mixed monomial x^i y^j on xy=N, with j≤B. -/
noncomputable def mixed (N : ℤ) (B i j : ℕ) : ℤ[X] := monomial (B+i-j) (N^j)
noncomputable def pure (N : ℤ) (B u : ℕ) : ℤ[X] := monomial u (N^(B-u))

theorem mixed_eval (N x y : ℤ) (B i j : ℕ) (jb : j≤B) (pair : x*y=N) :
    (mixed N B i j).eval x=x^B*(x^i*y^j) := by
  rw [mixed,eval_monomial,← pair,mul_pow]
  have h : j+(B+i-j)=B+i := by omega
  calc
    _ = x^(j+(B+i-j))*y^j := by rw [pow_add]; ring
    _ = _ := by rw [h,pow_add]; ring

/-- The entire rectangular footprint reduces to the canonical single-variable jet lattice.
This is an equality over the integers, including the coefficient divisibilities. -/
theorem rectangle_span (N : ℤ) (A B : ℕ) :
    Submodule.span ℤ {F | ∃ i≤A, ∃ j≤B, F=mixed N B i j} =
    Submodule.span ℤ {F | ∃ u≤A+B, F=pure N B u} := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨i,hi,j,hj,rfl⟩
    have e : min i j+(B-(B+i-j))=j := by omega
    have collapse : mixed N B i j=(N^(min i j)) • pure N B (B+i-j) := by
      rw [mixed,pure,smul_monomial,smul_eq_mul,← pow_add,e]
    rw [collapse]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨B+i-j,by omega,rfl⟩)
  · rintro _ ⟨u,hu,rfl⟩
    apply Submodule.subset_span
    by_cases h : B≤u
    · refine ⟨u-B,by omega,0,by omega,?_⟩
      simp [pure,mixed,Nat.sub_eq_zero_of_le h,Nat.add_sub_of_le h]
    · refine ⟨0,by omega,B-u,by omega,?_⟩
      simp [pure,mixed,Nat.sub_sub_self (by omega : u≤B)]

/-- Collect the coefficients on each diagonal of the rectangle. The result
vanishes identically exactly when every weighted diagonal sum is zero. -/
theorem rectangle_zero_iff (N : ℤ) (A B : ℕ) (w : Fin (A+1) → Fin (B+1) → ℤ) :
    (∑ i, ∑ j, w i j • mixed N B i.val j.val)=0 ↔
      ∀ u≤A+B, ∑ i, ∑ j, (if B+i.val-j.val=u then w i j*N^j.val else 0)=0 := by
  have diag (u : ℕ) :
      (∑ i, ∑ j, w i j • mixed N B i.val j.val).coeff u =
      ∑ i, ∑ j, (if B+i.val-j.val=u then w i j*N^j.val else 0) := by
    simp only [finset_sum_coeff,coeff_smul,mixed,coeff_monomial,smul_eq_mul]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    split_ifs <;> simp_all
  constructor
  · intro eq u _
    rw [← diag,eq,coeff_zero]
  · intro eq
    ext u
    rw [diag,coeff_zero]
    by_cases bound : u≤A+B
    · exact eq _ bound
    · apply sum_eq_zero
      intro i _
      apply sum_eq_zero
      intro j _
      exact if_neg (by omega)

/-- The existing ascending-coefficient relation interpreted in a centered variable. -/
noncomputable def hom {R : Type*} [CommRing R] (k : ℕ) (v : Fin (k+1) → R) (a b : R) : R :=
  ∑ i, v i*a^i.val*b^(k-i.val)

theorem hom_scale {R : Type*} [CommRing R] (k : ℕ) (v : Fin (k+1) → R) (a b s : R) :
    hom k v (s*a) (s*b) = s^k * hom k v a b := by
  unfold hom
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  have e : i.val+(k-i.val)=k := by omega
  have ps : s^i.val*s^(k-i.val)=s^k := by rw [← pow_add,e]
  rw [mul_pow,mul_pow,← ps]
  ring

theorem hom_one (k : ℕ) (v : Fin (k+1) → ℤ) (x : ℤ) :
    hom k v x 1=(ofFn (k+1) v).eval x := by simp [hom,HigherDivisorWindow.eval_coeff]

/-- The second equation expressed in the index of the first window, by clearing
the denominator in y=(N−e(c+sx))/(t(c+sx)). Both strides and centers are independent. -/
noncomputable def pullback (k : ℕ) (v : Fin (k+1) → ℤ) (N c s e t x : ℤ) : ℤ :=
  hom k v (N-e*(c+s*x)) (t*(c+s*x))

theorem pullback_pair (k : ℕ) (v : Fin (k+1) → ℤ) (N c s e t x y : ℤ)
    (pair : (c+s*x)*(e+t*y)=N) :
    pullback k v N c s e t x=(t*(c+s*x))^k*(ofFn (k+1) v).eval y := by
  rw [pullback,← hom_one,← hom_scale]
  rw [← pair]
  congr 1 <;> ring

theorem pullback_zero_iff (k : ℕ) (v : Fin (k+1) → ℤ) (N c s e t x y : ℤ)
    (pair : (c+s*x)*(e+t*y)=N) (den : t*(c+s*x)≠0) :
    pullback k v N c s e t x=0 ↔ (ofFn (k+1) v).eval y=0 := by
  rw [pullback_pair k v N c s e t x y pair,mul_eq_zero]
  simp [pow_ne_zero _ den]

/-- Homogeneous evaluation with the public N-powers of the depth-m jet basis. -/
noncomputable def canonical {R : Type*} [CommRing R] (k m : ℕ) (N : R)
    (a : Fin (k+1) → R) (z v : R) : R :=
  hom k (fun i => a i*N^(m-i.val)) z v

/-- Integral, normalized cofactor transform in the centered odd index. Here N=2h+1
and the factor is N+2z. It uses only additions and products. -/
noncomputable def oddPull {R : Type*} [CommRing R] (k m : ℕ) (N h : R)
    (a : Fin (k+1) → R) (z v : R) : R :=
  ∑ i, a i*N^(i.val-m)*(-(z+h*v))^i.val*(N*v+2*z)^(k-i.val)

theorem odd_pull_identity {R : Type*} [CommRing R] (k m : ℕ) (N h : R)
    (a : Fin (k+1) → R) (z v : R) :
    canonical k m N a (N*(-(z+h*v))) (N*v+2*z) = N^m*oddPull k m N h a z v := by
  unfold canonical hom oddPull
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  have eq : N^(m-i.val)*N^i.val = N^m*N^(i.val-m) := by
    rw [← pow_add,← pow_add]
    congr 1
    omega
  rw [mul_pow]
  linear_combination a i*(-(z+h*v))^i.val*(N*v+2*z)^(k-i.val)*eq

/-- Pulling back twice recovers the source form after the complementary N-powers cancel. -/
theorem odd_pull_back {R : Type*} [CommRing R] [IsDomain R] (k m : ℕ) (mk : m≤k)
    (N h : R) (odd : N=2*h+1) (nz : N≠0) (a : Fin (k+1) → R) (z v : R) :
    oddPull k m N h a (N*(-(z+h*v))) (N*v+2*z)=N^(k-m)*canonical k m N a z v := by
  have first : N*(-(N*(-(z+h*v))+h*(N*v+2*z)))=N*z := by rw [odd]; ring
  have second : N*(N*v+2*z)+2*(N*(-(z+h*v)))=N*v := by rw [odd]; ring
  have eq := odd_pull_identity k m N h a (N*(-(z+h*v))) (N*v+2*z)
  rw [first,second] at eq
  apply mul_left_cancel₀ (pow_ne_zero m nz)
  rw [← eq,canonical,hom_scale,← mul_assoc,← pow_add,Nat.add_sub_of_le mk]
  rfl

/-- An actual pair in odd anchored coordinates. Neither x nor y is used to construct a row. -/
theorem odd_pair (k m : ℕ) (N h : ℤ) (odd : N=2*h+1) (a : Fin (k+1) → ℤ)
    (z u : ℤ) (pair : (N+2*z)*(N+2*u)=N) :
    N^m*oddPull k m N h a z 1=(N+2*z)^k*canonical k m N a u 1 := by
  have index : N*(-(z+h))=(N+2*z)*u := by rw [odd] at pair ⊢; nlinarith only [pair]
  rw [← odd_pull_identity]
  simp only [mul_one,index]
  simpa only [mul_one,canonical] using hom_scale k (fun i => a i*N^(m-i.val)) u 1 (N+2*z)

private def IntegralJet (N : ℤ) (m : ℕ) (F : ℤ[X]) : Prop :=
  ∀ j, N^(m-j) ∣ F.coeff j

private theorem jet_zero (N : ℤ) (F : ℤ[X]) : IntegralJet N 0 F := by
  intro j
  simp

private theorem jet_mul {N : ℤ} {m r : ℕ} {P Q : ℤ[X]} (p : IntegralJet N m P)
    (q : IntegralJet N r Q) : IntegralJet N (m+r) (P*Q) := by
  intro j
  rw [coeff_mul]
  apply dvd_sum
  intro ij h
  have idx := Finset.HasAntidiagonal.mem_antidiagonal.mp h
  apply (pow_dvd_pow N (show m+r-j≤(m-ij.1)+(r-ij.2) by omega)).trans
  rw [pow_add]
  exact mul_dvd_mul (p _) (q _)

private theorem jet_pow {N : ℤ} {m : ℕ} {P : ℤ[X]} (p : IntegralJet N m P) (k : ℕ) :
    IntegralJet N (m*k) (P^k) := by
  induction k with
  | zero => simpa using jet_zero N (1:ℤ[X])
  | succ k ih => simpa only [Nat.mul_succ,pow_succ] using jet_mul ih p

private theorem jet_const (N : ℤ) (m : ℕ) : IntegralJet N m (C (N^m)) := by
  intro j
  cases j with
  | zero => rw [coeff_C_zero,Nat.sub_zero]
  | succ j => rw [coeff_C_succ]; exact dvd_zero _

private theorem jet_linear (N : ℤ) : IntegralJet N 1 (C N+2*X) := by
  intro j
  cases j with
  | zero => simp
  | succ j => simp

/-- The normalized transport is an integer polynomial with the complementary
Taylor divisibilities. Thus an exact second equation need not reflect a distinct
underlying lattice. Its coefficient height is a separate condition. -/
theorem complementary_jets (k m n : ℕ) (h : ℤ) (a : Fin (k+1) → ℤ) :
    HigherDivisorWindow.Jets (k-m) n 0
      (oddPull k m (C (n:ℤ)) (C h) (fun i => C (a i)) X 1) := by
  intro j
  rw [taylor_zero,oddPull,finset_sum_coeff]
  apply dvd_sum
  intro i _
  have c := jet_mul (jet_zero (n:ℤ) (C (a i))) (jet_const (n:ℤ) (i.val-m))
  have l := jet_zero (n:ℤ) ((-(X+C h))^i.val)
  have d := jet_pow (jet_linear (n:ℤ)) (k-i.val)
  have combined := jet_mul (jet_mul c l) d j.val
  have exp : (k-m)-j.val≤((0+(i.val-m)+0)+1*(k-i.val))-j.val := by
    simp only [zero_add,add_zero,one_mul]
    omega
  apply (pow_dvd_pow (n:ℤ) exp).trans
  simpa only [mul_one,← C_pow] using combined

/-- The transform fits inside the complementary basis in the same degree.
The witness consists of integral coefficients; heights at a prescribed window
can change and must be checked there. -/
theorem complementary_basis (k m n : ℕ) (h : ℤ) (a : Fin (k+1) → ℤ) :
    ∃ b : Fin (k+1) → ℤ, oddPull k m (C (n:ℤ)) (C h) (fun i => C (a i)) X 1 =
      ofFn (k+1) (fun i => b i*(n:ℤ)^((k-m)-i.val)) := by
  let P := oddPull k m (C (n:ℤ)) (C h) (fun i => C (a i)) X 1
  have d : P.natDegree≤k := by
    dsimp only [P,oddPull]
    apply natDegree_sum_le_of_forall_le
    intro i _
    simp only [mul_one,← C_pow,← C_mul]
    have li : (-(X+C h)).natDegree≤1 := by
      rw [natDegree_neg]
      exact natDegree_add_le_of_degree_le (by simp) (by simp)
    have lj : (C (n:ℤ)+2*X).natDegree≤1 :=
      natDegree_add_le_of_degree_le (by simp) (by simp)
    have lp : ((-(X+C h))^i.val).natDegree ≤ (i : ℕ) :=
      natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left i.val li)
    have lq : ((C (n:ℤ)+2*X)^(k-i.val)).natDegree≤k-i.val :=
      natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (k-i.val) lj)
    apply natDegree_mul_le.trans
    have lc := natDegree_mul_le (p:=C (a i*(n:ℤ)^(i.val-m))) (q:=(-(X+C h))^i.val)
    rw [natDegree_C,zero_add] at lc
    omega
  have row (i : Fin (k+1)) : (n:ℤ)^((k-m)-i.val) ∣ P.coeff i.val := by
    by_cases hi : i.val<k-m
    · simpa only [taylor_zero] using complementary_jets k m n h a ⟨i.val, hi⟩
    · rw [Nat.sub_eq_zero_of_le (by omega : k-m ≤ (i : ℕ)),pow_zero]; exact one_dvd _
  choose b eq using row
  refine ⟨b,?_⟩
  change P=_
  ext j
  by_cases hsmall : j<k+1
  · rw [ofFn_coeff_eq_val_of_lt _ hsmall]
    simpa only [mul_comm] using eq ⟨j,hsmall⟩
  · rw [ofFn_coeff_eq_zero_of_ge _ (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- Euclid's polynomial gcd describes the common roots exactly over the rationals.
A rational root still needs the integer divisor and window checks. -/
theorem common_iff_gcd (P Q : ℚ[X]) (x : ℚ) :
    (EuclideanDomain.gcd P Q).IsRoot x ↔ P.IsRoot x ∧ Q.IsRoot x := by
  simp only [← dvd_iff_isRoot]
  exact ⟨fun h => ⟨h.trans (EuclideanDomain.gcd_dvd_left _ _),h.trans (EuclideanDomain.gcd_dvd_right _ _)⟩,
    fun ⟨u,v⟩ => EuclideanDomain.dvd_gcd u v⟩

/-- The surviving rational candidates, counted with their common multiplicity. -/
theorem common_count {P Q : ℚ[X]} (p : P≠0) (q : Q≠0) :
    (EuclideanDomain.gcd P Q).roots.card≤min P.natDegree Q.natDegree := by
  apply (card_roots' _).trans
  exact le_min (natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left _ _) p)
    (natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right _ _) q)

/-- Agreement off two adjacent coefficient positions gives a directly testable
linear factor after subtraction and removal of the known power of X. -/
theorem adjacent (P Q : ℤ[X]) (l : ℕ) (s t a b x : ℤ) (nonzero : x≠0)
    (cancel : C s*P-C t*Q = X^l*(C a+C b*X)) (p : P.IsRoot x) (q : Q.IsRoot x) :
    b*x = -a := by
  have h := congrArg (Polynomial.eval x) cancel
  rw [IsRoot] at p q
  have eq : x^l*(a+b*x)=0 := by simpa [p,q] using h.symm
  have hz := (mul_eq_zero.mp eq).resolve_left (pow_ne_zero _ nonzero)
  linarith

private theorem hom4 (a b c d e x y : ℤ) :
    hom 4 ![a,b,c,d,e] x y=a*y^4+b*x*y^3+c*x^2*y^2+d*x^3*y+e*x^4 := by
  rw [hom,Fin.sum_univ_five]
  change a*x^0*y^4+b*x^1*y^3+c*x^2*y^2+d*x^3*y^1+e*x^4*y^0=_
  ring

/-- On this product the transported second row repeats the first one exactly, up to scale. -/
theorem control_2501 (x : ℤ) :
    pullback 4 ![7,32,-23,-17,1] 2501 43 2 59 2 x =
      100080016*(-5-32*x-5*x^2+25*x^3+3*x^4) := by rw [pullback,hom4]; ring

/-- On this product the second row has two different rational roots in the first index. -/
theorem control_6901 (x : ℤ) :
    pullback 4 ![1,6,1,-24,16] 6901 69 2 101 2 x =
      761980816*((x+1)*(6*x+1))^2 := by rw [pullback,hom4]; ring

/-- In the first index the common rational root is exactly -1, giving (67,103). -/
theorem control_6901_common (x : ℚ) :
    (-46-33*x-13*x^2+23*x^3+49*x^4=0 ∧ ((x+1)*(6*x+1))^2=0) ↔ x= -1 := by
  constructor
  · rintro ⟨p,q⟩
    have z : (x+1)*(6*x+1)=0 := by exact pow_eq_zero q
    rcases mul_eq_zero.mp z with u|v
    · linarith
    · have : x= -1/6 := by linarith
      subst x
      norm_num at p
  · rintro rfl
    norm_num

theorem control_6901_pair :
    (67:ℕ).Prime ∧ (103:ℕ).Prime ∧ 67*103=6901 ∧ (69+2*(-1):ℤ)=67 := by decide +kernel

end PrimeFactors.FactorCurveElimination
