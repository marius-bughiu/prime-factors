import PrimeFactors.Fermat
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum.Prime

namespace PrimeFactors

/-- A square product of two positive-side Fermat discriminants determines
a factorization of the input times the squared distance between midpoints. -/
theorem midpoint_collision_identity {n a c r : ℕ} (start : n ≤ a ^ 2) (ordered : a < c)
    (square : (a ^ 2 - n) * (c ^ 2 - n) = r ^ 2) :
    (a * c - n) ^ 2 = r ^ 2 + n * (c - a) ^ 2 := by
  have ac := Nat.mul_le_mul_left a ordered.le
  have cc := Nat.pow_le_pow_left ordered.le 2
  have mid : n ≤ a*c := by nlinarith
  have last : n ≤ c^2 := start.trans cc
  zify [start, mid, last, ordered.le] at square ⊢
  nlinarith only [square]

/-- Both complementary factors of the scaled product lie strictly between zero
and the input. Hence the gcd returns a proper divisor for every square collision
in this interval; the argument does not require knowledge of any input factor. -/
theorem midpoint_collision_split {n a c r : ℕ} (positive : 0 < n) (start : n ≤ a ^ 2)
    (ordered : a < c) (upper : 2*c^2 ≤ 3*n)
    (square : (a ^ 2 - n) * (c ^ 2 - n) = r ^ 2) :
    let u := a*c - n - r
    1 < n.gcd u ∧ n.gcd u < n ∧ n.gcd u ∣ n := by
  let h := a*c-n
  have iden : h^2 = r^2 + n*(c-a)^2 := midpoint_collision_identity start ordered square
  have step : 0 < c-a := Nat.sub_pos_of_lt ordered
  have extra : 0 < n*(c-a)^2 := by positivity
  have rlt : r < h := by
    by_contra! he
    have monotone := Nat.pow_le_pow_left he 2
    omega
  have posC : 0 < c := by omega
  have ac_lt := Nat.mul_lt_mul_of_pos_right ordered posC
  have ac_ge : n ≤ a*c := start.trans (by simpa [pow_two] using Nat.mul_le_mul_left a ordered.le)
  have width : h + r < n := by
    dsimp [h] at rlt ⊢
    rw [pow_two] at upper
    omega
  let u := h-r
  have product : u*(h+r) = n*(c-a)^2 := by
    dsimp [u]
    zify [rlt.le] at iden ⊢
    nlinarith only [iden]
  change 1 < n.gcd u ∧ n.gcd u < n ∧ n.gcd u ∣ n
  have nonzero : 0 < u := Nat.sub_pos_of_lt rlt
  have small : u < n := by dsimp [u]; omega
  have divisor := Nat.gcd_dvd_right n u
  refine ⟨?_, (Nat.le_of_dvd nonzero divisor).trans_lt small, Nat.gcd_dvd_left n u⟩
  have gpos := Nat.gcd_pos_of_pos_left u positive
  by_contra! trivial
  have cop : n.Coprime u := show n.gcd u = 1 by omega
  have divides : n ∣ u*(h+r) := ⟨_, product⟩
  have dv := cop.dvd_of_dvd_mul_left divides
  have rhspos : 0 < h+r := by omega
  exact (Nat.not_dvd_of_pos_of_lt rhspos width) dv

/-- A collision at adjacent midpoints outputs two factors directly. -/
theorem adjacent_collision_product {n a r : ℕ} (start : n ≤ a ^ 2)
    (square : (a ^ 2 - n) * ((a+1) ^ 2 - n) = r ^ 2) :
    (a*(a+1)-n-r) * (a*(a+1)-n+r) = n := by
  have iden := midpoint_collision_identity start (Nat.lt_succ_self a) square
  change (a*(a+1)-n)^2 = r^2 + n*(a+1-a)^2 at iden
  rw [show a+1-a=1 by omega, one_pow, mul_one] at iden
  have le : r ≤ a*(a+1)-n := by
    by_contra! h
    have := Nat.pow_lt_pow_left h (show 2 ≠ 0 by decide)
    omega
  zify [le] at iden ⊢
  nlinarith only [iden]

/-- Just above the cutoff, arbitrarily large inputs admit adjacent collisions
with complementary factors 1 and n. The third identity measures the excess
over the cutoff exactly. -/
theorem midpoint_collision_cutoff_family (t : ℕ) :
    let n := 6*t^2 + 6*t + 1
    let a := 3*t + 1
    let c := 3*t + 2
    let r := 3*t*(t+1)
    (a^2-n)*(c^2-n) = r^2 ∧ a*c-n-r = 1 ∧
    2*c^2 = 3*n + 6*t + 5 := by
  dsimp only
  have da : (3*t+1)^2 = (6*t^2+6*t+1) + 3*t^2 := by ring
  have dc : (3*t+2)^2 = (6*t^2+6*t+1) + 3*(t+1)^2 := by ring
  have ac : (3*t+1)*(3*t+2) = (6*t^2+6*t+1) + (3*t*(t+1)+1) := by ring
  rw [da, dc, ac]
  simp only [Nat.add_sub_cancel_left]
  refine ⟨by ring, ?_, by ring⟩
  trivial

/-- Both false midpoints satisfy the parity restriction for the odd factors
of 9017. The gcd of the first component with the input yields 71. -/
theorem midpoint_collision_9017 :
    (95^2 - 9017) * (97^2 - 9017) = (56 : ℕ)^2 ∧
    Nat.gcd 9017 (95*97-9017-56) = 71 ∧ 9017 = 71*127 ∧
    Nat.Prime 71 ∧ Nat.Prime 127 := by
  refine ⟨by decide, by decide, by decide, by norm_num, by norm_num⟩

/-- For a balanced pair whose shifted factors have square product, one formula
at the ceiling square root gives the exact doubled factor sum. -/
theorem shifted_square_sum {p q : ℕ} (ordered : p ≤ q) (balance : q ≤ 2*p)
    (shifted : IsSquare ((2*p+1)*(2*q+1))) :
    let m := ceilSqrt (p*q)
    2*(m*(m+1)-p*q) = p+q := by
  obtain ⟨z, hz⟩ := shifted
  have oddProd : Odd ((2*p+1)*(2*q+1)) :=
    (odd_iff_exists_bit1.mpr ⟨p, rfl⟩).mul (odd_iff_exists_bit1.mpr ⟨q,rfl⟩)
  obtain ⟨a, ha⟩ := (Nat.odd_mul.mp (hz ▸ oddProd)).1.exists_bit1
  rw [ha] at hz
  have eqn : 2*(a*(a+1)) = 2*(p*q) + (p+q) := by nlinarith only [hz]
  let m := ceilSqrt (p*q)
  have bound : p*q ≤ m^2 := ceilSqrt_le_iff.mp le_rfl
  have ma : m ≤ a := by
    apply ceilSqrt_le_iff.mpr
    by_contra! small
    have s : p+q < 2*a := by nlinarith only [eqn, small]
    have ss := Nat.pow_lt_pow_left s (show 2 ≠ 0 by decide)
    have sq : 4*(p*q) ≤ (p+q)^2 := by
      zify
      nlinarith only [sq_nonneg ((p:ℤ)-q)]
    nlinarith only [small, ss, sq]
  have pm : p ≤ m := Nat.mul_self_le_mul_self_iff.mp <|
    (Nat.mul_le_mul_left p ordered).trans (by simpa [pow_two] using bound)
  have am : a ≤ m := by
    by_contra! bad
    have h := Nat.mul_le_mul (show m+1 ≤ a by omega) (show m+2 ≤ a+1 by omega)
    nlinarith only [h, eqn, bound, balance, pm]
  have same := le_antisymm ma am
  change 2*(m*(m+1)-p*q) = p+q
  rw [same]
  omega

/-- Product-only recovery for the shifted-square family. An application to an
unrestricted input can check that the returned pair multiplies back to it. -/
def adjacentShiftFactors (n : ℕ) : ℕ × ℕ :=
  let a := ceilSqrt n
  let h := a * (a + 1) - n
  let r := (h ^ 2 - n).sqrt
  (h - r, h + r)

theorem adjacentShiftFactors_correct {p q : ℕ} (ordered : p ≤ q) (balance : q ≤ 2*p)
    (shifted : IsSquare ((2*p+1)*(2*q+1))) :
    adjacentShiftFactors (p*q) = (p,q) := by
  let m := ceilSqrt (p*q)
  let h := m*(m+1)-p*q
  have sum : 2*h = p+q := shifted_square_sum ordered balance shifted
  have plo : p ≤ h := by omega
  have qeq : q = h+(h-p) := by omega
  have half : h^2 = p*q+(h-p)^2 := by
    zify [plo] at sum ⊢
    nlinarith only [congrArg (fun t : ℤ => (p:ℤ)*t) sum]
  change (h-(h^2-p*q).sqrt,h+(h^2-p*q).sqrt) = (p,q)
  rw [half, Nat.add_sub_cancel_left, Nat.sqrt_eq']
  congr 1 <;> omega

/-- The shifted-square family includes unequal, balanced primes even when
the initial Fermat midpoint itself has a nonsquare discriminant. -/
theorem adjacent_collision_2701 :
    ceilSqrt 2701 = 52 ∧ (52^2-2701)*((52+1)^2-2701) = (18:ℕ)^2 ∧
    52*53-2701-18 = (37:ℕ) ∧ 52*53-2701+18 = (73:ℕ) ∧
    Nat.Prime 37 ∧ Nat.Prime 73 := by
  refine ⟨?_, by decide, by decide, by decide, by norm_num, by norm_num⟩
  exact le_antisymm (ceilSqrt_le_iff.mpr (by decide)) (by
    by_contra! tooSmall
    exact (by decide : ¬ 2701 ≤ 51^2) (ceilSqrt_le_iff.mp (by omega)))

end PrimeFactors
