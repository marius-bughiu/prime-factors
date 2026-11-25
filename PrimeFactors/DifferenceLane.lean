import PrimeFactors.PowerFactorScale
import PrimeFactors.PowerFactorLanes
import Mathlib.RingTheory.Binomial
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Fintype.Card

namespace PrimeFactors.DifferenceLane

open Finset Polynomial

/-- Value at x of the monic Newton polynomial with nodes u,u+R,... . -/
noncomputable def basisValue (u R x : ℤ) (j : ℕ) : ℤ := ∏ i ∈ range j, (x - (u + R*i))

theorem basis_on_lane (u R k : ℤ) (j : ℕ) :
    basisValue u R (u+R*k) j = R^j * j.factorial * Ring.choose k j := by
  have base : basisValue u R (u+R*k) j = R^j * (descPochhammer ℤ j).eval k := by
    induction j with
    | zero => simp [basisValue]
    | succ j ih =>
      rw [basisValue, prod_range_succ, ← basisValue, ih, descPochhammer_succ_right,
        eval_mul, eval_sub, eval_X, eval_natCast, pow_succ]
      ring
  rw [base, eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul,
    mul_assoc]

/-- The unit triangular Pascal matrix makes the first d+1 values enough to recover
the divisibility of every binomial-basis coefficient, over the integers. -/
theorem binomial_lane_iff (d : ℕ) (M : ℤ) (a : ℕ → ℤ) :
    (∀ k : ℤ, M ∣ ∑ j ∈ range (d+1), a j * Ring.choose k j) ↔
      ∀ j ≤ d, M ∣ a j := by
  constructor
  · intro hall j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      have eq : (∑ i ∈ range (j+1), a i * Ring.choose (j : ℤ) i) =
          ∑ i ∈ range (d+1), a i * Ring.choose (j : ℤ) i := by
        apply sum_subset (range_mono (by omega))
        intro i _ h
        have hi : j < i := by simpa using h
        rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hi]
        simp
      have all := hall (j : ℤ)
      rw [← eq, sum_range_succ, Ring.choose_natCast, Nat.choose_self, Nat.cast_one,
        mul_one] at all
      have prev : M ∣ ∑ i ∈ range j, a i * Ring.choose (j : ℤ) i :=
        dvd_sum fun i hi => dvd_mul_of_dvd_left (ih i (mem_range.mp hi) (by
          have := mem_range.mp hi
          omega)) _
      exact (dvd_add_right prev).mp all
  · intro ha k
    exact dvd_sum fun j hj => dvd_mul_of_dvd_left (ha j (by
      have := mem_range.mp hj
      omega)) _

/-- The surviving precision after the dyadic stride and the factorial content. -/
def precision (L e j : ℕ) : ℕ := L - (e*j + padicValNat 2 j.factorial)

theorem dyadic_diagonal (L e j : ℕ) (b : ℤ) :
    (2:ℤ)^L ∣ b * ((2:ℤ)^e)^j * j.factorial ↔ (2:ℤ)^(precision L e j) ∣ b := by
  by_cases hb : b=0
  · simp [hb]
  have hp : (2:ℤ)^(e*j) ≠ 0 := by positivity
  have hf : (j.factorial:ℤ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hv : padicValInt 2 ((2:ℤ)^(e*j)) = e*j := by
    change padicValInt 2 (((2:ℕ):ℤ)^(e*j)) = _
    rw [← Nat.cast_pow, padicValInt.of_nat, padicValNat.prime_pow]
  rw [← pow_mul]
  change ((2:ℕ):ℤ)^L ∣ _ ↔ ((2:ℕ):ℤ)^(precision L e j) ∣ b
  rw [padicValInt_dvd_iff, padicValInt_dvd_iff,
    padicValInt.mul (mul_ne_zero hb hp) hf, padicValInt.mul hb hp, hv, padicValInt.of_nat]
  simp only [mul_ne_zero hb hp, mul_ne_zero (mul_ne_zero hb hp) hf, hb, false_or]
  unfold precision
  omega

/-- A congruence on the whole integer lane is exactly one independent congruence
per Newton coefficient, including the coordinates whose precision drops to zero. -/
theorem lane_iff (u : ℤ) (L e d : ℕ) (b : ℕ → ℤ) :
    (∀ k : ℤ, (2:ℤ)^L ∣ ∑ j ∈ range (d+1), b j * basisValue u (2^e) (u+2^e*k) j) ↔
      ∀ j ≤ d, (2:ℤ)^(precision L e j) ∣ b j := by
  simp_rw [basis_on_lane, ← mul_assoc]
  rw [binomial_lane_iff]
  exact forall_congr' fun j => forall_congr' fun _ => dyadic_diagonal L e j (b j)

/-- The independent coefficient residues index the cosets in Newton coordinates. -/
theorem residue_count (L e d : ℕ) :
    Fintype.card ((j : Fin (d+1)) → Fin (2^precision L e j)) =
      2^(∑ j ∈ range (d+1), precision L e j) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range]

/-- For each coordinate the margin L minus the required precision is min(L,α).
It is largest once L reaches α. -/
theorem margin (L e j : ℕ) : L - precision L e j = min L (e*j + padicValNat 2 j.factorial) := by
  unfold precision
  omega

theorem factorial_bits (j : ℕ) : padicValNat 2 j.factorial = j-(Nat.digits 2 j).sum := by
  simpa using (sub_one_mul_padicValNat_factorial (p:=2) j)

theorem saved_bits_lt {t : ℕ} (ht : 0<t) :
    (∑ j ∈ range (2*t+1), padicValNat 2 j.factorial) < t*(2*t+1) := by
  rw [← (PowerFactorScale.determinant_exponents t).1]
  apply sum_lt_sum
  · intro j _
    rw [factorial_bits]
    omega
  · refine ⟨1, mem_range.mpr (by omega), ?_⟩
    simp

/-- Each Newton diagonal is an exact divisor of the full common modulus. -/
def quotient (R d j : ℕ) : ℕ := R^(d-j) * (d.factorial / j.factorial)

theorem quotient_identity (R d j : ℕ) (hj : j ≤ d) :
    quotient R d j * (R^j * j.factorial) = R^d * d.factorial := by
  unfold quotient
  rw [mul_mul_mul_comm, ← pow_add, Nat.sub_add_cancel hj,
    Nat.div_mul_cancel (Nat.factorial_dvd_factorial hj)]

theorem full_lane_iff (u : ℤ) (R d : ℕ) (hR : 0 < R) (b : ℕ → ℤ) :
    (∀ k : ℤ, ((R^d * d.factorial : ℕ):ℤ) ∣
      ∑ j ∈ range (d+1), b j * basisValue u R (u+R*k) j) ↔
      ∀ j ≤ d, (quotient R d j : ℤ) ∣ b j := by
  simp_rw [basis_on_lane, ← mul_assoc]
  rw [binomial_lane_iff]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  rw [← quotient_identity R d j hj]
  simp only [Nat.cast_mul, Nat.cast_pow, mul_assoc]
  apply mul_dvd_mul_iff_right
  positivity

/-- The cardinality of the independent residues times the determinant margin
equals M^(d+1). No assumption that the factorials are units is used. -/
theorem full_index_identity (R d : ℕ) :
    Fintype.card ((j : Fin (d+1)) → Fin (quotient R d j)) *
      (R^(∑ j ∈ range (d+1), j) * ∏ j ∈ range (d+1), j.factorial) =
      (R^d * d.factorial)^(d+1) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [Fin.prod_univ_eq_prod_range, ← Finset.prod_pow_eq_pow_sum, ← prod_mul_distrib,
    ← prod_mul_distrib]
  calc _ = ∏ _j ∈ range (d+1), R^d * d.factorial := by
             apply prod_congr rfl
             intro j hj
             exact quotient_identity R d j (by have := mem_range.mp hj; omega)
       _ = _ := by simp

/-- Translation preserves the leading coefficient, so a forward difference of a
polynomial of degree at most d+1 has degree at most d. -/
private theorem difference_degree {P : ℤ[X]} {d : ℕ} (R : ℤ) (bound : P.natDegree ≤ d+1) :
    (taylor R P - P).natDegree ≤ d := by
  by_cases hzero : P = 0
  · simp [hzero]
  by_cases hdif : taylor R P - P = 0
  · simp [hdif]
  have same : (taylor R P).leadingCoeff = P.leadingCoeff := by
    rw [taylor_apply, leadingCoeff_comp (by rw [natDegree_X_add_C]; decide),
      leadingCoeff_X_add_C, one_pow, mul_one]
  have htr : taylor R P ≠ 0 := leadingCoeff_ne_zero.mp (same ▸ leadingCoeff_ne_zero.mpr hzero)
  have hd : (taylor R P).degree = P.degree := by
    rw [degree_eq_natDegree htr, degree_eq_natDegree hzero, natDegree_taylor]
  have hlt := Polynomial.degree_sub_lt hd htr same
  rw [degree_eq_natDegree hdif, degree_eq_natDegree htr, natDegree_taylor] at hlt
  have hlt' : (taylor R P - P).natDegree < P.natDegree := by exact_mod_cast hlt
  omega

/-- Any modulus, any stride, and both signs of k. The consecutive checks at
k=0,...,d certify every integer value on the lane of a degree-at-most-d polynomial. -/
theorem finite_grid_dvd {d : ℕ} (M u R : ℤ) (P : ℤ[X]) (bound : P.natDegree ≤ d)
    (grid : ∀ j : ℕ, j ≤ d → M ∣ P.eval (u+R*j)) :
    ∀ k : ℤ, M ∣ P.eval (u+R*k) := by
  induction d generalizing P with
  | zero =>
    have init := grid 0 le_rfl
    rw [eq_C_of_natDegree_le_zero bound, eval_C] at init
    intro k
    rwa [eq_C_of_natDegree_le_zero bound, eval_C]
  | succ d ih =>
    let Q := taylor R P - P
    have difference (k : ℤ) :
        Q.eval (u+R*k) = P.eval (u+R*(k+1)) - P.eval (u+R*k) := by
      simp [Q, taylor_eval, mul_add, add_assoc]
    have qgrid (j : ℕ) (hj : j ≤ d) : M ∣ Q.eval (u+R*j) := by
      rw [difference, ← Nat.cast_succ]
      exact dvd_sub (grid (j+1) (by omega)) (grid j (by omega))
    have steps := ih Q (difference_degree R bound) qgrid
    intro k
    induction k using Int.inductionOn' (b := 0) with
    | H0 => simpa using grid 0 (by omega)
    | Hs k _ hk =>
      have step := steps k
      rw [difference] at step
      simpa using dvd_add step hk
    | Hp k _ hk =>
      have step := steps (k-1)
      rw [difference, sub_add_cancel] at step
      simpa using dvd_sub hk step

/-- The factor-membership theorem for the solver's d+1-point verification, using
its actual modulus. In particular, M may omit prime factors of the full factorial. -/
theorem grid_mem_candidates {t : ℕ} {M R u N x y : ℤ} {c : ℕ → ℤ}
    (hN : N ≠ 0) (nz : ∃ j ≤ 2*t, c j ≠ 0) (cop : IsCoprime M N)
    (grid : ∀ j : ℕ, j ≤ 2*t → M ∣ (PowerFactorLanes.polynomial t c N).eval (u+R*j))
    (lane : ∃ k : ℤ, x = u+R*k) (pair : x*y=N)
    (short : |PowerFactorLanes.trace t c x y| < M) :
    x ∈ PowerFactorLanes.candidates t c N := by
  obtain ⟨k, hk⟩ := lane
  have hval : M ∣ (PowerFactorLanes.polynomial t c N).eval x := by
    rw [hk]
    exact finite_grid_dvd M u R _ (PowerFactorLanes.degree_bound t c N) grid k
  rw [PowerFactorLanes.pair_identity t c pair] at hval
  have copx : IsCoprime M x := (show IsCoprime M (x*y) from pair.symm ▸ cop).of_mul_right_left
  have zero := Int.eq_zero_of_abs_lt_dvd (copx.pow_right.dvd_of_dvd_mul_left hval) short
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots (PowerFactorLanes.polynomial_nonzero hN nz)).mpr
  rw [Polynomial.IsRoot, PowerFactorLanes.pair_identity t c pair, zero, mul_zero]

/-- A short trace satisfying the full-factorial congruences includes the true
factor in the existing set of at most 2t roots. The expansion hypothesis relates
the supplied Newton and monomial coordinates as integer polynomial functions. -/
theorem full_mem_candidates {t R : ℕ} {u N x y : ℤ} {b c : ℕ → ℤ}
    (hR : 0 < R) (hN : N ≠ 0) (nz : ∃ j ≤ 2*t, c j ≠ 0)
    (cop : IsCoprime ((R^(2*t) * (2*t).factorial : ℕ):ℤ) N)
    (expansion : ∀ z, (PowerFactorLanes.polynomial t c N).eval z =
      ∑ j ∈ range (2*t+1), b j * basisValue u R z j)
    (hc : ∀ j ≤ 2*t, (quotient R (2*t) j : ℤ) ∣ b j)
    (lane : ∃ k : ℤ, x = u+R*k) (pair : x*y=N)
    (short : |PowerFactorLanes.trace t c x y| < ((R^(2*t)*(2*t).factorial : ℕ):ℤ)) :
    x ∈ PowerFactorLanes.candidates t c N := by
  apply grid_mem_candidates hN nz cop _ lane pair short
  intro j _
  rw [expansion]
  exact (full_lane_iff u R (2*t) hR b).mpr hc j

/-- The cleared LLL inequality after substituting the uniform 2048-bit coordinate
bound. Small entries can be checked directly with exact integer operations. -/
def factorialScale (t e : ℕ) : Prop :=
  let m := 2*t+1
  m^m * 2^(t*m + 2049*t*(t+1)) <
    2^(2*e*t*m) * (∏ j ∈ range m, j.factorial)^2

noncomputable instance (t e : ℕ) : Decidable (factorialScale t e) := by
  unfold factorialScale
  infer_instance

theorem small_full_scales : ∀ entry ∈ ([(1,684), (2,615), (3,586), (4,569),
    (8,541)] : List (ℕ × ℕ)),
    factorialScale entry.1 entry.2 ∧ ¬factorialScale entry.1 (entry.2-1) := by
  decide +kernel

end PrimeFactors.DifferenceLane
