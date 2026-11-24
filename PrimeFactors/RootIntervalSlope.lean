import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- A bounded multiplier brings the doubled interval center near a multiple
of the modulus, with an integral signed remainder. -/
theorem rootIntervalSlope_exists (N B : ℕ) (c : ℤ) (n : 0 < N) (bound : 0 < B) :
    ∃ b : ℕ, 1 ≤ b ∧ b ≤ B ∧
      ∃ j : ℤ, |2*(b:ℤ)*c-(N:ℤ)*j| *((B:ℤ)+1) ≤ (N:ℤ) := by
  have nR : (0:ℝ) < N := by exact_mod_cast n
  let α : ℝ := 2*(c:ℝ)/N
  obtain ⟨b,hb,bb,approx⟩ := Real.exists_nat_abs_mul_sub_round_le α bound
  let j : ℤ := round ((b:ℝ)*α)
  refine ⟨b,hb,bb,j,?_⟩
  change |(b:ℝ)*α-(j:ℝ)| ≤ 1/((B:ℝ)+1) at approx
  have scaled := (le_div_iff₀ (by positivity : (0:ℝ)<(B:ℝ)+1)).mp approx
  have eqn : 2*(b:ℝ)*c-(N:ℝ)*j=((b:ℝ)*α-j)*N := by
    dsimp [α]
    field_simp
    ring
  have goal : |2*(b:ℝ)*c-(N:ℝ)*j| *((B:ℝ)+1) ≤ N := by
    rw [eqn,abs_mul,abs_of_pos nR,mul_right_comm]
    simpa using mul_le_mul_of_nonneg_right scaled nR.le
  exact_mod_cast goal

/-- The Euclidean remainder step preserves the cross sum of the remainders
and the convergent denominators, even at the final zero remainder. -/
theorem rootIntervalSlope_euclidean_step (U V a b : ℕ) :
    (a+U/V*b)*V+b*(U%V)=a*V+b*U := by
  have eqn := Nat.mod_add_div U V
  calc
    _ = a*V+b*(U%V+V*(U/V)) := by ring
    _ = _ := by rw [eqn]


/-- Consecutive convergents have opposite remainder signs. The Euclidean
update propagates the signed congruence along with the denominator. -/
theorem rootIntervalSlope_signed_step {x N a b U V s j k : ℤ}
    (first : x*a = s*U+N*j) (second : x*b = -s*V+N*k) (q : ℤ) :
    x*(a+q*b)=s*(U-q*V)+N*(j+q*k) := by
  calc
    _ = x*a+q*(x*b) := by ring
    _ = _ := by rw [first, second]; ring

/-- At a denominator-budget stop the retained remainder meets Dirichlet's
bound by the same cross sum used in the Euclidean loop. -/
theorem rootIntervalSlope_euclidean_stop {N B U V a b : ℕ}
    (inv : a*V+b*U=N) (stop : B < a+U/V*b) : V*(B+1) ≤ N := by
  rw [←inv,←rootIntervalSlope_euclidean_step U V a b]
  exact (show V*(B+1) ≤ (a+U/V*b)*V by
    rw [Nat.mul_comm V]
    exact Nat.mul_le_mul_right _ stop).trans (Nat.le_add_right _ _)

/-- Taking the integer square root of the integral quotient brackets N/M
without relying on floating point. -/
theorem rootIntervalSlope_width {N M : ℕ} (hm : 0 < M) :
    (N/M).sqrt^2*M ≤ N ∧ N < ((N/M).sqrt+1)^2*M := by
  constructor
  · exact (Nat.le_div_iff_mul_le hm).mp (Nat.sqrt_le' _)
  · exact (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_succ_sqrt' _)

/-- The chosen denominator cap simultaneously controls the quadratic and
linear interval coefficients. -/
theorem rootIntervalSlope_coefficients {N M : ℕ} (c : ℤ) (pos : 0 < M) (width : M ≤ N) :
    ∃ (b : ℕ) (j : ℤ), 1 ≤ b ∧ b ≤ (N/M).sqrt ∧ b^2*M ≤ N ∧
      (2*(b:ℤ)*c-(N:ℤ)*j)^2 ≤ (N:ℤ)*M := by
  let B := (N/M).sqrt
  have n : 0 < N := pos.trans_le width
  have bpos : 0 < B := by
    apply Nat.pos_of_ne_zero
    intro z
    have hi := (rootIntervalSlope_width (N:=N) pos).2
    change N < (B+1)^2*M at hi
    simp [z] at hi
    omega
  obtain ⟨b,hb,bb,j,err⟩ := rootIntervalSlope_exists N B c n bpos
  have bounds := rootIntervalSlope_width (N:=N) pos
  refine ⟨b,j,hb,bb,(Nat.mul_le_mul_right M (Nat.pow_le_pow_left bb 2)).trans bounds.1,?_⟩
  let r : ℤ := 2*(b:ℤ)*c-(N:ℤ)*j
  have size : |r| *((B:ℤ)+1) ≤ (N:ℤ) := err
  have square : (|r| *((B:ℤ)+1))^2 ≤ (N:ℤ)^2 :=
    sq_le_sq' (le_trans (by omega : -(N:ℤ) ≤ 0) (by positivity)) size
  have upper : (N:ℤ) < ((B:ℤ)+1)^2*(M:ℤ) := by exact_mod_cast bounds.2
  have strict := mul_lt_mul_of_pos_left upper (by exact_mod_cast n : 0 < (N:ℤ))
  have coeff : 0 < ((B:ℤ)+1)^2 := by positivity
  rw [mul_pow,sq_abs] at square
  apply le_of_lt
  change r^2 < (N:ℤ)*M
  apply (lt_of_mul_lt_mul_left _ coeff.le)
  nlinarith only [square,strict]

end PrimeFactors
