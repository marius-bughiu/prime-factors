import PrimeFactors.GeometricBlockReading
import Mathlib.Tactic

/-! Finite checks for the small-root step after geometric interpolation.
The lattice search proposes integer polynomials. Shortness and ideal
membership are the properties that make an auxiliary polynomial valid. -/

namespace PrimeFactors.GeometricSmallRoot
open Finset Polynomial

/-- The whole balanced interval is inside the degree-r small-root scale
for modulus n^k when its squared width is below n and r ≤ 2k. -/
theorem root_scale {W n r k : ℕ} (width : W^2<n) (positive : 0<r) (precision : r≤2*k) :
    W^r<n^k := by
  have one : 1≤n := by omega
  have strict := Nat.pow_lt_pow_left width positive.ne'
  have upper := Nat.pow_le_pow_right one precision
  have square : (W^r)^2 < (n^k)^2 := by
    calc
      (W^r)^2 = (W^2)^r := by rw [←pow_mul, ←pow_mul, Nat.mul_comm r 2]
      _ < n^(2*k) := strict.trans_le upper
      _ = (n^k)^2 := by rw [←pow_mul, Nat.mul_comm k 2]
  exact lt_of_not_ge (fun h => (not_lt_of_ge (Nat.pow_le_pow_left h 2)) square)

/-- The elementary balanced-interval endpoints imply the required square bound. -/
theorem width_sq {n L U : ℕ} (pos : 0<n) (lo : 4*n≤L^2) (hi : 2*U^2≤9*n) :
    (U-L)^2<n := by
  by_cases h : U≤L
  · simpa [Nat.sub_eq_zero_of_le h] using pos
  have grow : (2*U)^2 < (3*L)^2 := by nlinarith
  have twice : 2*U<3*L := by
    by_contra! contra
    exact (not_lt_of_ge (Nat.pow_le_pow_left contra 2)) grow
  have add : U-L+L=U := Nat.sub_add_cancel (by omega)
  have hpos : 0<L := by nlinarith
  have h1 : 3*(U-L)<U := by omega
  have h2 : (3*(U-L))^2 < U^2 := Nat.pow_lt_pow_left h1 (by decide)
  nlinarith

/-- Integer lattice rows x^j M^(m-l) f(x)^l share modulus M^m
at every integral root of f modulo M. -/
theorem row_divides {M x : ℤ} (f : ℤ[X]) (root : M∣f.eval x)
    {l m : ℕ} (level : l≤m) (j : ℕ) :
    M^m ∣ x^j*M^(m-l)*(f.eval x)^l := by
  obtain ⟨c, hc⟩ := root
  refine ⟨x^j*c^l, ?_⟩
  rw [hc, mul_pow, ←Nat.sub_add_cancel level, pow_add]
  simp only [Nat.add_sub_cancel]
  ring

/-- A row combination that is shorter than its common divisor vanishes exactly. -/
theorem integer_zero {ι : Type*} (s : Finset ι) (weights values : ι → ℤ)
    {M : ℤ} (rows : ∀ i∈s, M∣values i)
    (short : |∑ i∈s, weights i*values i| < M) :
    ∑ i∈s, weights i*values i = 0 := by
  have div : M∣∑ i∈s, weights i*values i :=
    Finset.dvd_sum (fun i hi => dvd_mul_of_dvd_right (rows i hi) _)
  exact Int.eq_zero_of_abs_lt_dvd div short

/-- The checked norm is a bound on the entire interval, including its endpoints. -/
theorem eval_bound (f : ℤ[X]) {x B : ℤ} (inside : |x|≤B) :
    |f.eval x| ≤ ∑ j∈range (f.natDegree+1), |f.coeff j| * B^j := by
  rw [eval_eq_sum_range]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro j _
  rw [abs_mul,abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) inside j) (abs_nonneg _)

/-- The four-row witness for the actual cubic reading at N=30607.
Its integer factorization and a seven-residue check isolate the small root. -/
theorem unique_30607 {z : ℤ} (lo : 0≤z) (hi : z≤21)
    (root : (936788449:ℤ) ∣ z^3+214435022*z^2+45419578*z+901416760) :
    z=18 := by
  let x := z-10
  let F := z^3+214435022*z^2+45419578*z+901416760
  let H := 929296+485766*x-58081*x^2-2145*x^3
  have row : H = (-2145)*F+936788449*(52204+9924*x+491*x^2) := by
    dsimp [H,F,x]; ring
  have dv : (936788449:ℤ) ∣ H := by
    rw [row]; exact dvd_add (dvd_mul_of_dvd_right root _) (dvd_mul_right ..)
  have xlo : -11≤x := by dsimp [x]; omega
  have xhi : x≤11 := by dsimp [x]; omega
  have absx : |x|≤11 := abs_le.mpr ⟨xlo,xhi⟩
  have hpoly : H = (C 929296+C 485766*X-C 58081*X^2-C 2145*X^3 : ℤ[X]).eval x := by
    simp [H]
  have hnorm : |H|≤16155518 := by
    rw [hpoly]
    simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X]
    calc
      _ ≤ |929296+485766*x-58081*x^2| + |2145*x^3| := abs_sub ..
      _ ≤ (|929296+485766*x| + |58081*x^2|) + |2145*x^3| :=
        add_le_add_right (abs_sub ..) _
      _ ≤ (|929296| + |485766*x| + |58081*x^2|) + |2145*x^3| := by
        gcongr; exact abs_add_le ..
      _ ≤ 16155518 := by
        simp only [abs_mul,abs_pow]
        norm_num
        have sq : x^2≤121 := by nlinarith [mul_nonneg (show 0≤x+11 by omega) (show 0≤11-x by omega)]
        have cube := pow_le_pow_left₀ (abs_nonneg x) absx 3
        linarith
  have zero := Int.eq_zero_of_abs_lt_dvd dv (lt_of_le_of_lt hnorm (by decide))
  have fac : H=(x-8)*(-(2145*x^2+75241*x+116162)) := by dsimp [H]; ring
  rw [fac,mul_eq_zero] at zero
  rcases zero with eq | eq
  · dsimp [x] at eq; omega
  · have bad : (2145:ZMod 7)*(x:ZMod 7)^2+75241*(x:ZMod 7)+116162=0 := by
      have cast := congrArg (fun v : ℤ => (v : ZMod 7)) (neg_eq_zero.mp eq)
      push_cast at cast
      exact cast
    have excluded : ∀ a : ZMod 7, (2145:ZMod 7)*a^2+75241*a+116162≠0 := by decide
    exact (excluded _ bad).elim

end PrimeFactors.GeometricSmallRoot
