import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- Both parts of the local key used to bucket signed norms are necessary:
the valuation parities and the Legendre signs after removing all powers of p.
In particular the test still works when just one norm is divisible by p. -/
theorem squareClassFilter_agrees {a b z p : ℕ} [Fact p.Prime]
    (ha : a ≠ 0) (hb : b ≠ 0) (square : a*b = z^2) :
    a.factorization p % 2 = b.factorization p % 2 ∧
    legendreSym p (ordCompl[p] a : ℕ) = legendreSym p (ordCompl[p] b : ℕ) := by
  have hz : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide), mul_eq_zero] at square
    exact square.elim ha hb
  constructor
  · have e := congrArg (fun n : ℕ => n.factorization p) square
    simp only [Nat.factorization_mul ha hb, Nat.factorization_pow, Finsupp.add_apply,
      Finsupp.smul_apply, nsmul_eq_mul] at e
    omega
  · have unit (n : ℕ) (hn : n ≠ 0) : (((ordCompl[p] n : ℕ) : ℤ) : ZMod p) ≠ 0 := by
      rw [Int.cast_natCast, ne_eq, ZMod.natCast_zmod_eq_zero_iff_dvd]
      exact Nat.not_dvd_ordCompl Fact.out hn
    have natParts : (ordCompl[p] a)*(ordCompl[p] b) = (ordCompl[p] z)^2 := by
      simpa only [pow_two, Nat.ordCompl_mul] using congrArg (fun n : ℕ => ordCompl[p] n) square
    have intParts : ((ordCompl[p] a : ℕ) : ℤ) * (ordCompl[p] b : ℕ) =
        ((ordCompl[p] z : ℕ) : ℤ)^2 := by exact_mod_cast natParts
    have product := congrArg (legendreSym p) intParts
    rw [legendreSym.mul, legendreSym.sq_one' p (unit z hz)] at product
    have sign := legendreSym.sq_one p (unit b hb)
    calc
      _ = legendreSym p (ordCompl[p] a : ℕ) * (legendreSym p (ordCompl[p] b : ℕ))^2 := by rw [sign, mul_one]
      _ = (legendreSym p (ordCompl[p] a : ℕ) * legendreSym p (ordCompl[p] b : ℕ)) *
            legendreSym p (ordCompl[p] b : ℕ) := by ring
      _ = _ := by rw [product, one_mul]

/-- For nonzero signed rows with square product, the sign bits agree and
the local keys computed on their magnitudes agree at every test prime. -/
theorem squareClassFilter_signed_agrees {a b z : ℤ} {p : ℕ} [Fact p.Prime]
    (ha : a ≠ 0) (hb : b ≠ 0) (square : a*b = z^2) :
    (a < 0 ↔ b < 0) ∧
    a.natAbs.factorization p % 2 = b.natAbs.factorization p % 2 ∧
    legendreSym p (ordCompl[p] a.natAbs : ℕ) = legendreSym p (ordCompl[p] b.natAbs : ℕ) := by
  have nonneg : 0 ≤ a*b := square ▸ sq_nonneg z
  have magnitude := congrArg Int.natAbs square
  simp only [Int.natAbs_mul, Int.natAbs_pow] at magnitude
  refine ⟨?_, squareClassFilter_agrees (Int.natAbs_ne_zero.mpr ha)
    (Int.natAbs_ne_zero.mpr hb) magnitude⟩
  rcases mul_nonneg_iff.mp nonneg with pos | neg <;> omega

end PrimeFactors
