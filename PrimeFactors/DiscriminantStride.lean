import PrimeFactors.GapStride
import PrimeFactors.DivisorSum
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.LinearCombination

namespace PrimeFactors

/-- Every common stride of a probe discriminant and the actual half-gap supplies a
fixed difference of squares, even when the stride is composite. -/
theorem discriminant_stride_factorization {N H s m c e : ℤ}
    (gap : H^2 = N+(m*c)^2) (probe : s^2-N = m*e) :
    (H-s)*(H+s) = m*(m*c^2-e) := by linear_combination gap - probe

/-- A nonzero difference of squares has at most one representation per positive divisor
chosen as the sum. The finite bound applies to signed probe errors. -/
theorem discriminant_stride_representation_count {K : ℤ} (hk : K ≠ 0) (T : Finset (ℤ × ℤ))
    (repr : ∀ x ∈ T, 0 < x.1+x.2 ∧ (x.1-x.2)*(x.1+x.2) = K) :
    T.card ≤ K.natAbs.divisors.card := by
  apply Finset.card_le_card_of_injOn (fun x : ℤ × ℤ => (x.1+x.2).natAbs)
  · intro x hx
    apply Nat.mem_divisors.mpr
    refine ⟨Int.natAbs_dvd_natAbs.mpr ?_, by simpa using hk⟩
    rw [← (repr x hx).2]
    exact dvd_mul_left ..
  · rintro ⟨a,b⟩ hx ⟨c,d⟩ hy h
    obtain ⟨px, ex⟩ := repr (a,b) hx
    obtain ⟨py, ey⟩ := repr (c,d) hy
    dsimp only at h px py ex ey
    have sum : a+b = c+d := by
      have := congrArg (fun n : ℕ => (n : ℤ)) h
      simpa only [Int.natCast_natAbs, abs_of_pos px, abs_of_pos py] using this
    rw [sum] at ex
    have diff := mul_right_cancel₀ py.ne' (ex.trans ey.symm)
    exact Prod.ext (by omega) (by omega)

/-- One modular inverse lifts the known root supplied by the probe. -/
theorem discriminant_probe_lift {s m n e t k : ℤ} (probe : n-s^2 = m*e)
    (digit : 2*s*t-e = m*k) : (s+m*t)^2 - n = m^2*(k+t^2) := by
  linear_combination m*digit - probe

/-- A prime stride dividing the probe discriminant and the true half-gap forces one
of two linear congruences. The residual signed index has an exact integral identity. -/
theorem discriminant_stride_orientation {m : ℕ} (hm : m.Prime) {N H D s c : ℤ}
    (gap : H^2 = N + D^2) (cofactor : D = m*c) (probe : (m : ℤ) ∣ s^2 - N) :
    ∃ h : ℤ, (H - s = m*h ∨ H + s = m*h) ∧
      s^2 - N = m * (m*(c^2+h^2) - 2*H*h) := by
  have both : (m : ℤ) ∣ (H+s)*(H-s) := by
    rw [← sq_sub_sq, show H^2 - s^2 = m*(m*c^2) - (s^2-N) by
      rw [gap, cofactor]; ring]
    exact dvd_sub (dvd_mul_right ..) probe
  rcases (Nat.prime_iff_prime_int.mp hm).dvd_mul.mp both with ⟨h, hh⟩ | ⟨h, hh⟩
  · refine ⟨h, Or.inr hh, ?_⟩
    rw [cofactor] at gap
    linear_combination (s-H+m*h)*hh + gap
  · refine ⟨h, Or.inl hh, ?_⟩
    rw [cofactor] at gap
    linear_combination (-s-H+m*h)*hh + gap

/-- Two midpoints counted for fixed modulus, gap cofactor and nonzero signed index
must be close whenever both probe discriminants are small. -/
theorem discriminant_stride_diameter {m c h H₁ H₂ e₁ e₂ L : ℤ}
    (first : e₁ = m*(m*(c^2+h^2)-2*H₁*h)) (second : e₂ = m*(m*(c^2+h^2)-2*H₂*h))
    (small₁ : |e₁| ≤ L) (small₂ : |e₂| ≤ L) : |m| * |h| * |H₁ - H₂| ≤ L := by
  have diff : 2*m*h*(H₁-H₂) = e₂ - e₁ := by rw [first, second]; ring
  have bound := (abs_sub e₂ e₁).trans (add_le_add small₂ small₁)
  rw [← diff, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by decide : (0:ℤ) ≤ 2)] at bound
  linarith only [bound]

/-- The near-square residual itself is prime here. Its two lifted root classes
produce the prime factors in two trials; the ordinary midpoint offset is 483. -/
theorem discriminant_stride_103469711 :
    Nat.sqrt 103469711 = 10172 ∧ 103469711 - 10172^2 = 127 ∧ Nat.Prime 127 ∧
    2*10172*90 % 127 = 1 ∧ (10172+127*90) % 127^2 = 5473 ∧
    21602 % 127^2 = 5473 ∧ 10656 = 127^2-5473 ∧
    10656^2 = 103469711+3175^2 ∧ 10656-10173 = 483 ∧
    7481*13831 = 103469711 ∧ Nat.Prime 7481 ∧ Nat.Prime 13831 := by
  norm_num

/-- If the squarefree part is at least two, the square part of `(p-1)(q-1)`
is directly readable at a single scaled square root of the public product. -/
theorem predecessor_square_part {a b d y : ℕ} (positive : 0 < a) (ordered : a ≤ b)
    (balance : b+1 ≤ 2*(a+1)) (scale : 2 ≤ d) (kernel : a*b = d*y^2) :
    Nat.sqrt (((a+1)*(b+1))/d) = y := by
  have dpos : 0 < d := by omega
  have ratio : b ≤ 3*a := by omega
  have h₁ := Nat.mul_le_mul_left a ordered
  have h₂ := Nat.mul_le_mul_left b ratio
  have tot : (a+b)^2 ≤ 6*(a*b) := by nlinarith only [h₁, h₂]
  have sq : (a+b)^2 ≤ (2*d*y)^2 := calc
    _ ≤ 6*(a*b) := tot
    _ = 6*(d*y^2) := by rw [kernel]
    _ ≤ (4*d)*(d*y^2) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring
  have ab : a+b ≤ 2*d*y := by simpa using (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp sq
  apply Nat.le_antisymm
  · apply Nat.le_of_lt_succ
    apply Nat.sqrt_lt'.mpr
    apply (Nat.div_lt_iff_lt_mul dpos).mpr
    nlinarith only [kernel, ab, scale]
  · apply Nat.le_sqrt'.mpr
    apply (Nat.le_div_iff_mul_le dpos).mpr
    nlinarith only [kernel]

/-- In the exceptional scale-one case the integer square root overshoots by exactly one. -/
theorem predecessor_square_root {a b y : ℕ} (ordered : a ≤ b)
    (balance : b+1 ≤ 2*(a+1)) (kernel : a*b = y^2) :
    Nat.sqrt ((a+1)*(b+1)) = y+1 := by
  have ay : a ≤ y := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    rw [← kernel, pow_two]
    exact Nat.mul_le_mul_left a ordered
  have lower : 2*y ≤ a+b := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ordered
    nlinarith only [kernel, Nat.zero_le (k^2)]
  apply Nat.le_antisymm
  · apply Nat.le_of_lt_succ
    apply Nat.sqrt_lt'.mpr
    nlinarith only [kernel, ay, balance]
  · apply Nat.le_sqrt'.mpr
    nlinarith only [kernel, lower]

/-- Product-only sum candidate at a given square-class multiplier. -/
def predecessorSquareSum (n d : ℕ) : ℕ :=
  let y := if d=1 then n.sqrt-1 else (n/d).sqrt
  n+1-d*y^2

theorem predecessorSquareSum_correct {a b d y : ℕ} (positive : 0 < a) (ordered : a ≤ b)
    (balance : b+1 ≤ 2*(a+1)) (scale : 0 < d) (kernel : a*b = d*y^2) :
    predecessorSquareSum ((a+1)*(b+1)) d = (a+1)+(b+1) := by
  unfold predecessorSquareSum
  have prod : (a+1)*(b+1)+1 = (a+1)+(b+1)+d*y^2 := by nlinarith only [kernel]
  by_cases h : d = 1
  · subst d
    simp only [↓reduceIte, one_mul] at kernel prod ⊢
    rw [predecessor_square_root ordered balance kernel, Nat.add_sub_cancel, prod, Nat.add_sub_cancel]
  · rw [if_neg h, predecessor_square_part positive ordered balance (by omega) kernel, prod,
      Nat.add_sub_cancel]

/-- A six-square predecessor product with small signed gcds, far past the first Fermat midpoint. -/
theorem predecessorSquareSum_1604108860967 :
    let N := 1604108860967
    let S := predecessorSquareSum N 6
    S = 2599368 ∧ recoverFromSigma N (N+S+1) = (1008017,1591351) ∧
      1008017*1591351 = N ∧ (1008017-1)*(1591351-1)=6*517060^2 ∧
      (1008017-1).gcd (1591351-1) = 2 ∧ (1008017-1).gcd (1591351+1) = 8 ∧
      (1008017+1).gcd (1591351-1) = 6 ∧ (1008017+1).gcd (1591351+1) = 2 ∧
      S/2-ceilSqrt N = 33149 := by
  dsimp only
  have hs : predecessorSquareSum 1604108860967 6 = 2599368 :=
    predecessorSquareSum_correct (a := 1008016) (b := 1591350) (y := 517060)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hr : ceilSqrt 1604108860967 = 1266535 := by
    apply Nat.le_antisymm (ceilSqrt_le_iff.mpr (by decide))
    have low : ¬ ceilSqrt 1604108860967 ≤ 1266534 := fun h => (by decide : ¬ 1604108860967 ≤ 1266534^2) (ceilSqrt_le_iff.mp h)
    omega
  rw [hs, hr]
  have pair : recoverFromSigma 1604108860967 (1604108860967+2599368+1) = (1008017, 1591351) := by
    unfold recoverFromSigma
    norm_num
  rw [pair]
  decide +kernel

theorem predecessorSquareSum_example_primes : Nat.Prime 1008017 ∧ Nat.Prime 1591351 := by
  constructor <;> norm_num

end PrimeFactors
