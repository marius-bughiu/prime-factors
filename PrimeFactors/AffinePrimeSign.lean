import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

/-! The public numerator 1−4Nr has Legendre symbol +1 at every prime divisor
of N. For each fixed odd prime candidate ℓ not dividing N with ℓ²≤N, strictly
fewer than half the draws r=0,...,N−1 give +1. -/

namespace PrimeFactors.AffinePrimeSign

open Finset

/-- On a prime candidate the Jacobi expression is the Legendre symbol. Taking
the difference in ℤ admits the zero draw with numerator one. -/
def passes (N ℓ r : ℕ) : Prop := jacobiSym (1 - 4*(N : ℤ)*r) ℓ = 1

noncomputable def seeds (N ℓ : ℕ) : Finset ℕ := by
  classical
  exact (range N).filter (passes N ℓ)

theorem mem_seeds {N ℓ r : ℕ} : r ∈ seeds N ℓ ↔ r < N ∧ passes N ℓ r := by
  classical
  simp only [seeds, mem_filter, mem_range]

theorem passes_iff_legendre (N ℓ r : ℕ) [Fact ℓ.Prime] :
    passes N ℓ r ↔ legendreSym ℓ (1 - 4*(N : ℤ)*r) = 1 := by
  rw [passes, jacobiSym.legendreSym.to_jacobiSym]

private theorem passes_field (N ℓ r : ℕ) [Fact ℓ.Prime] :
    passes N ℓ r ↔ quadraticChar (ZMod ℓ) (1-4*(N : ZMod ℓ)*r) = 1 := by
  rw [passes_iff_legendre, legendreSym]
  push_cast
  rfl

/-- A genuine prime divisor survives every draw. -/
theorem true_pass {N ℓ : ℕ} (prime : ℓ.Prime) (dvd : ℓ ∣ N) (r : ℕ) : passes N ℓ r := by
  letI : Fact ℓ.Prime := ⟨prime⟩
  rw [passes_field, (ZMod.natCast_zmod_eq_zero_iff_dvd N ℓ).mpr dvd]
  simp

/-- Every affine image in the prime field has exactly one preimage. -/
theorem affine_bijective {N ℓ : ℕ} (prime : ℓ.Prime) (odd : ℓ ≠ 2) (miss : ¬ ℓ ∣ N) :
    Function.Bijective (fun x : ZMod ℓ => 1 - 4*(N : ZMod ℓ)*x) := by
  letI : Fact ℓ.Prime := ⟨prime⟩
  have two : (2 : ZMod ℓ) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have four : (4 : ZMod ℓ) ≠ 0 := by
    rw [show (4 : ZMod ℓ) = 2*2 by norm_num]
    exact mul_ne_zero two two
  have unit : (N : ZMod ℓ) ≠ 0 := fun eq => miss ((ZMod.natCast_zmod_eq_zero_iff_dvd N ℓ).mp eq)
  apply Finite.injective_iff_bijective.mp
  intro x y h
  exact mul_left_cancel₀ (mul_ne_zero four unit) (sub_right_injective h)

noncomputable def positive (ℓ : ℕ) [Fact ℓ.Prime] : Finset (ZMod ℓ) :=
  univ.filter fun x => quadraticChar (ZMod ℓ) x = 1

/-- Exactly (ℓ−1)/2 field values have positive sign; the zero value is excluded. -/
theorem positive_count (ℓ : ℕ) [Fact ℓ.Prime] (odd : ℓ ≠ 2) :
    2*(positive ℓ).card + 1 = ℓ := by
  classical
  have point (x : ZMod ℓ) :
      2 * (if quadraticChar (ZMod ℓ) x = 1 then (1 : ℤ) else 0) =
        (1 + quadraticChar (ZMod ℓ) x) - (if x = 0 then 1 else 0) := by
    by_cases hx : x = 0
    · simp [hx]
    · rcases quadraticChar_dichotomy hx with h | h <;> simp [hx, h]
  have total := congrArg (fun g : ZMod ℓ → ℤ => ∑ x, g x) (funext point)
  have cs := quadraticChar_sum_zero (F := ZMod ℓ) (by rwa [ZMod.ringChar_zmod_n])
  simp only [← mul_sum, sum_sub_distrib, sum_add_distrib, cs, add_zero,
    sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one] at total
  have hc : ((positive ℓ).card : ℤ) =
      ∑ x : ZMod ℓ, if quadraticChar (ZMod ℓ) x = 1 then (1 : ℤ) else 0 := by
    simp only [positive, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have zero : (∑ x : ZMod ℓ, if x = 0 then (1 : ℤ) else 0) = 1 := by simp
  rw [zero, ← hc] at total
  omega

/-- Sorting accepted draws by their quotient and affine value embeds them in
a rectangle. Its first side includes the final incomplete block. -/
theorem ceiling_bound {N ℓ : ℕ} (prime : ℓ.Prime) (odd : ℓ ≠ 2) (miss : ¬ ℓ ∣ N) :
    2*(seeds N ℓ).card ≤ ((N-1)/ℓ+1)*(ℓ-1) := by
  classical
  letI : Fact ℓ.Prime := ⟨prime⟩
  let code (r : ℕ) : ℕ × ZMod ℓ := (r/ℓ, 1 - 4*(N : ZMod ℓ)*r)
  have bound : (seeds N ℓ).card ≤ (range ((N-1)/ℓ+1) ×ˢ positive ℓ).card := by
    apply card_le_card_of_injOn code
    · intro r hr
      obtain ⟨inside,pass⟩ := mem_seeds.mp hr
      exact mem_product.mpr
        ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))),
         mem_filter.mpr ⟨mem_univ _,(passes_field ..).mp pass⟩⟩
    · intro r _ s _ eq
      have quot : r/ℓ = s/ℓ := congrArg Prod.fst eq
      have field := (affine_bijective prime odd miss).injective (congrArg Prod.snd eq)
      have rem := (ZMod.natCast_eq_natCast_iff' r s ℓ).mp field
      calc
        r = ℓ * (r/ℓ) + r%ℓ := (Nat.div_add_mod r ℓ).symm
        _ = s := by rw [quot,rem,Nat.div_add_mod]
  rw [card_product,card_range] at bound
  have count := positive_count ℓ odd
  calc
    _ ≤ 2 * (((N-1)/ℓ+1)*(positive ℓ).card) := Nat.mul_le_mul_left _ bound
    _ = ((N-1)/ℓ+1)*(2*(positive ℓ).card) := by ring
    _ = _ := by rw [show 2*(positive ℓ).card=ℓ-1 by omega]

/-- In the lower-factor range, strictly fewer than half the public draws pass
for each false odd prime. The assumption ℓ²≤N pays for the clipped last block. -/
theorem false_strict {N ℓ : ℕ} (prime : ℓ.Prime) (odd : ℓ ≠ 2) (miss : ¬ ℓ ∣ N)
    (fit : ℓ^2 ≤ N) : 2*(seeds N ℓ).card < N := by
  have q : ℓ ≤ N/ℓ := (Nat.le_div_iff_mul_le prime.pos).mpr (by simpa [pow_two] using fit)
  have round : (N-1)/ℓ + 1 ≤ N/ℓ + 1 := Nat.add_le_add_right (Nat.div_le_div_right (by omega)) 1
  have entry := (ceiling_bound prime odd miss).trans (Nat.mul_le_mul_right (ℓ-1) round)
  have full : (N/ℓ)*ℓ ≤ N := Nat.div_mul_le_self N ℓ
  have reconstruct : ℓ-1+1 = ℓ := by have := prime.pos; omega
  have scale : (N/ℓ)*(ℓ-1) + N/ℓ = (N/ℓ)*ℓ := by
    calc
      _ = (N/ℓ)*(ℓ-1+1) := by ring
      _ = _ := by rw [reconstruct]
  rw [Nat.add_mul, Nat.one_mul] at entry
  omega

theorem false_bound {N ℓ : ℕ} (prime : ℓ.Prime) (odd : ℓ ≠ 2) (miss : ¬ ℓ ∣ N)
    (fit : ℓ^2 ≤ N) : 2*(seeds N ℓ).card ≤ N := (false_strict prime odd miss fit).le

end PrimeFactors.AffinePrimeSign
