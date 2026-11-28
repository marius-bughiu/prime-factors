import PrimeFactors.FactorClueSumPrecision
import PrimeFactors.WithinResidueSearchFloor

/-! A floor on the ordinary ascending search even when a genuine 160-bit
factor suffix and its sharpest single sum congruence are given for free. -/
namespace PrimeFactors.FactorClueSumPrefix

open Finset WithinResidueSearchFloor
open MixedPrefixSample (eligible)
open scoped Classical
set_option exponentiation.threshold 4096
attribute [local irreducible] eligible

/-- The true sum's modulus after the low bits of the smaller prime have been supplied. -/
def modulus (v : ℕ×ℕ) :=
  FactorClueSumPrecision.greatest (v.1*v.2) (v.1%2^160) (2^160)

private theorem modulus_bounds (v : ℕ×ℕ) : 0<modulus v ∧ modulus v≤2^321 := by
  have cap : FactorClueSumPrecision.cap (2^160)=2^321 := by decide +kernel
  have div : modulus v ∣ FactorClueSumPrecision.cap (2^160) :=
    Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right ..)
  rw [cap] at div
  exact ⟨Nat.pos_of_dvd_of_pos div (by positivity),Nat.le_of_dvd (by positivity) div⟩

/-- The scan visits only the correct sum class, in increasing order, from
the ceiling of twice the square root up to and including the true sum. -/
noncomputable def visits (v : ℕ×ℕ) :=
  (Icc (low v) (target v)).filter fun s => s%modulus v=target v%modulus v

/-- On all but fewer than one in 2^35 eligible inputs, at least 2^579 wrong
sums precede the successful endpoint in this particular scan. -/
theorem population :
    2^35*(eligible.filter (fun v => (visits v).card≤2^579)).card<eligible.card := by
  have sub : eligible.filter (fun v => (visits v).card≤2^579) ⊆ short := by
    intro v hv
    obtain ⟨member,small⟩ := mem_filter.mp hv
    apply mem_filter.mpr
    refine ⟨member,lt_of_not_ge ?_⟩
    intro wide
    obtain ⟨pos,cap⟩ := modulus_bounds v
    have cover : WithinResidueSearchFloor.Covers (visits v) (modulus v) (low v) (target v) :=
      fun _ h₁ h₂ eq => mem_filter.mpr ⟨mem_Icc.mpr ⟨h₁,h₂⟩,eq⟩
    have lower := prefix_floor pos (show low v≤target v by omega) cover
    have scale := (Nat.mul_le_mul_left (2^579) cap).trans_eq
      (by decide +kernel : (2:ℕ)^579*2^321=2^900)
    have enough : 2^579≤(target v-low v)/modulus v :=
      (Nat.le_div_iff_mul_le pos).mpr (scale.trans (by omega))
    omega
  exact (Nat.mul_le_mul_left _ (card_le_card sub)).trans_lt exceptional

end PrimeFactors.FactorClueSumPrefix
