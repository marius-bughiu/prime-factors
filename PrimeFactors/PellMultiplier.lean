import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PrimeFactors

private theorem pellMultiplier_square_mod_four (x : ℕ) : x^2 % 4 = 0 ∨ x^2 % 4 = 1 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt x (by decide : 0 < 4)
  interval_cases x % 4 <;> decide

/-- A central denominator is odd for a radicand congruent to one modulo four.
The first identity comes from a complete quotient; the last is the signed
norm of the preceding convergent. -/
theorem pellMultiplier_center_odd {D P Q R c a b : ℕ} (rad : D % 4 = 1)
    (complete : D = P^2 + Q*R) (center : 2*P = c*Q)
    (norm : a^2 = D*b^2 + Q ∨ D*b^2 = a^2 + Q) : Q % 2 = 1 := by
  by_contra bad
  have casesQ : Q % 4 = 0 ∨ Q % 4 = 2 := by omega
  rcases casesQ with z | two
  · have eq := congrArg (· % 4) complete
    simp only [Nat.add_mod, Nat.mul_mod Q R, z, zero_mul, Nat.zero_mod, Nat.add_zero,
      Nat.mod_mod] at eq
    have sq : P^2 % 4 = 1 := by omega
    have evenP : P % 2 = 0 := by
      have cent := congrArg (· % 4) center
      simp only [Nat.mul_mod c Q, z, mul_zero, Nat.zero_mod] at cent
      omega
    obtain ⟨v,hv⟩ := Nat.dvd_of_mod_eq_zero evenP
    rw [hv, show (2*v)^2 = 4*v^2 by ring, Nat.mul_mod_right] at sq
    contradiction
  · have prod : D*b^2 % 4 = b^2 % 4 := by simp [Nat.mul_mod D, rad]
    rcases norm with h | h <;> have eq := congrArg (· % 4) h <;>
      simp only [Nat.add_mod (D*b^2) Q, Nat.add_mod (a^2) Q, two, prod] at eq <;>
      rcases pellMultiplier_square_mod_four a with ha | ha <;>
      rcases pellMultiplier_square_mod_four b with hb | hb <;> omega

/-- At a center the odd denominator divides the radicand. -/
theorem pellMultiplier_center_dvd {D P Q R c : ℕ} (odd : Q.Coprime 2)
    (complete : D = P^2 + Q*R) (center : 2*P = c*Q) : Q ∣ D := by
  have divides : Q ∣ 2*P := center ▸ dvd_mul_left Q c
  have hp := odd.dvd_of_dvd_mul_left divides
  rw [complete, sq]
  exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_right ..)

/-- Once the denominator is coprime to N and the single-prime cases have
been ruled out, the two prime multiplier is the only possible denominator. -/
theorem pellMultiplier_failed_pair {N Q r s : ℕ} (hr : r.Prime) (hs : s.Prime)
    (cop : Q.Coprime N) (divides : Q ∣ N*(r*s)) (size : 1 < Q)
    (nr : Q ≠ r) (ns : Q ≠ s) : Q = r*s := by
  have d := cop.dvd_of_dvd_mul_left divides
  by_cases h : r ∣ Q
  · obtain ⟨k,hk⟩ := h
    rw [hk] at d
    have dk : k ∣ s := (Nat.mul_dvd_mul_iff_left hr.pos).mp d
    rcases (Nat.dvd_prime hs).mp dk with one | all
    · simp [one] at hk
      exact (nr hk).elim
    · simp [hk, all]
  · have dc : Q.Coprime r := (hr.coprime_iff_not_dvd.mpr h).symm
    rcases (Nat.dvd_prime hs).mp (dc.dvd_of_dvd_mul_left d) with one | all <;> omega

/-- Opposite Legendre signs exclude both signed products when minus one is a
square at the selected prime. This is the obstruction on a successful edge. -/
theorem pellMultiplier_opposite {p : ℕ} [Fact p.Prime] {r s : ℤ}
    (minus : legendreSym p (-1) = 1) (opposite : legendreSym p r * legendreSym p s = -1) :
    ¬IsSquare ((r*s : ℤ) : ZMod p) ∧ ¬IsSquare ((-(r*s) : ℤ) : ZMod p) := by
  constructor <;> apply (legendreSym.eq_neg_one_iff p).mp
  · simpa only [legendreSym.mul] using opposite
  · rw [neg_eq_neg_one_mul, legendreSym.mul, minus, one_mul, legendreSym.mul, opposite]

/-- If the failed denominator is r*s, the negative sign would make N a
square modulo r. The Jacobi filter and reciprocity exclude this sign. -/
theorem pellMultiplier_no_negative_norm {r s N a b : ℕ} [Fact r.Prime]
    (hs : s.Prime) (cop : r.Coprime s) (nonresidue : ¬IsSquare (N : ZMod r)) :
    a^2 + r*s ≠ N*(r*s)*b^2 := by
  intro eq
  have hr := Fact.out (p := r.Prime)
  have dv : r*s ∣ a^2 := by
    have big : r*s ∣ N*(r*s)*b^2 := dvd_mul_of_dvd_left (dvd_mul_left ..) _
    rw [← eq] at big
    exact (Nat.dvd_add_iff_left (dvd_refl _)).mpr big
  have ra := hr.dvd_of_dvd_pow ((dvd_mul_right r s).trans dv)
  have sa := hs.dvd_of_dvd_pow ((dvd_mul_left s r).trans dv)
  obtain ⟨k, hk⟩ := cop.mul_dvd_of_dvd_of_dvd ra sa
  rw [hk] at eq
  have scaled : (r*s)*(r*s*k^2+1) = (r*s)*(N*b^2) := by linear_combination eq
  have small := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hr.pos hs.pos) scaled
  have modEq := congrArg (fun t : ℕ => (t : ZMod r)) small
  push_cast at modEq
  simp only [ZMod.natCast_self, zero_mul, zero_add] at modEq
  apply nonresidue
  refine ⟨(N : ZMod r)*b, ?_⟩
  calc
    (N : ZMod r) = N * ((N : ZMod r)*b^2) := by rw [← modEq, mul_one]
    _ = (N*b)*(N*b) := by ring

/-- Three individually uninformative signed roots on a triangle give a
square congruence. Multiplying by the three unit vertices clears division. -/
theorem pellMultiplier_triangle {A : Type*} [CommRing A] {r s t a b c e f g : A}
    (ab : a^2=e*r*s) (ac : b^2=f*r*t) (bc : c^2=g*s*t) :
    (a*b*c)^2=(e*f*g)*(r*s*t)^2 := by
  rw [mul_pow, mul_pow, ab, ac, bc]
  ring

/-- The three coprime center denominators from the full-cycle benchmark.
Clearing the unit denominator checks the assembled root directly. -/
theorem pellMultiplier_cycle_example :
    Nat.gcd 57 77837 = 1 ∧ Nat.gcd 69 77837 = 1 ∧ Nat.gcd 437 77837 = 1 ∧
    65162^2 % 77837 = 3*19 ∧ 28501^2 % 77837 = 3*23 ∧ 64425^2 % 77837 = 19*23 ∧
    (65162*28501*64425) % 77837 = (39058*3*19*23) % 77837 ∧
    Nat.gcd (39058-1) 77837 = 277 ∧ 277*281 = 77837 := by decide

end PrimeFactors
