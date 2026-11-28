import PrimeFactors.FiniteThreeSquareTwists
import Mathlib.NumberTheory.SumTwoSquares

/-! Positivity of the base count for twists 2ℓ. The classical three-square
theorem enters as an explicit mathematical premise; individual represented
targets require only a witness. See N. C. Ankeny, "Sums of three squares",
Proceedings of the AMS 8 (1957), 316–319, Theorem 1. -/

namespace PrimeFactors.EvenPrimeThreeSquareBase

open Finset FiniteThreeSquareTwists
open private PrimeFactors.ThreeSquareRadiusCounts.signs from PrimeFactors.ThreeSquareRadiusCounts

def Represented (n : ℕ) : Prop := ∃ x y z : ℕ, x^2+y^2+z^2=n

/-- The sufficient direction of the classical Gauss–Legendre three-square
theorem. Integer coordinates may be replaced by their absolute values. -/
def ThreeSquares : Prop :=
  ∀ n : ℕ, 0<n → (∀ a b : ℕ, n≠4^a*(8*b+7)) → Represented n

private theorem sum_pos_iff {ι : Type*} (S : Finset ι) (f : ι → ℕ) :
    0<∑ i∈S, f i ↔ ∃ i∈S, 0<f i := by
  constructor
  · intro h
    by_contra! no
    have z : ∑ i∈S, f i=0 := sum_eq_zero (fun i hi => Nat.eq_zero_of_le_zero (no i hi))
    omega
  · rintro ⟨i,hi,pos⟩
    exact pos.trans_le (single_le_sum (fun i _ => Nat.zero_le (f i)) hi)

/-- Positivity of the project's signed and ordered count is equivalent to
the existence of a certificate with nonnegative integer coordinates. -/
theorem positive_iff (n : ℕ) : 0<r₃ n ↔ Represented n := by
  unfold r₃
  rw [sum_pos_iff]
  constructor
  · rintro ⟨x,_,row⟩
    obtain ⟨y,_,hy⟩ := (sum_pos_iff ..).mp row
    refine ⟨x,y,(n-x^2-y^2).sqrt,?_⟩
    by_contra miss
    simp [miss] at hy
  · rintro ⟨x,y,z,eq⟩
    have bound (k : ℕ) (hk : k^2≤n) : k∈range (n.sqrt+1) := by
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_sqrt'.mpr hk))
    refine ⟨x,bound x (by omega),(sum_pos_iff ..).mpr ⟨y,bound y (by omega),?_⟩⟩
    have root : (n-x^2-y^2).sqrt=z := by
      rw [show n-x^2-y^2=z^2 by omega,pow_two,Nat.sqrt_eq]
    simp only [root,eq,if_true]
    have weight (k : ℕ) : 0<PrimeFactors.ThreeSquareRadiusCounts.signs k := by
      unfold PrimeFactors.ThreeSquareRadiusCounts.signs
      split <;> decide
    exact Nat.mul_pos (Nat.mul_pos (weight x) (weight y)) (weight z)

/-- Twice an odd integer is 2 modulo 4, whereas an exceptional integer is
either odd or divisible by four. No primality or size bound is needed. -/
theorem even_base (h : ThreeSquares) {m : ℕ} (odd : Odd m) : 0<r₃ (2*m) := by
  apply (positive_iff _).mpr
  obtain ⟨j,hj⟩ := odd
  apply h _ (by omega)
  intro a b eq
  cases a with
  | zero => simp only [pow_zero,one_mul] at eq; omega
  | succ a =>
    rw [pow_succ,show 4^a*4*(8*b+7)=4*(4^a*(8*b+7)) by ring] at eq
    omega

/-- For primes other than 3 modulo 4, Fermat's two-square theorem already
gives the needed positive base count without a three-square premise. -/
theorem two_square_prime {p : ℕ} [Fact p.Prime] (good : p%4≠3) : 0<r₃ (2*p) := by
  obtain ⟨a,b,h⟩ := Nat.Prime.sq_add_sq good
  obtain ⟨x,y,eq⟩ := Nat.sq_add_sq_mul (show 2=1^2+1^2 by decide) h.symm
  exact (positive_iff _).mpr ⟨x,y,0,by simpa using eq.symm⟩

/-- Only the bounded odd-prime subcase is required when using the stated
least-prime cutoff. Concrete witnesses can discharge the same premise. -/
def BoundedBases (B : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → p≤B → 0<r₃ (2*p)

theorem bounded (h : ThreeSquares) (B : ℕ) : BoundedBases B :=
  fun _ _ odd _ => even_base h odd

/-- The counts at 2·3 and 2·7 are direct finite evaluations independent
of the general three-square theorem. -/
theorem controls : r₃ 6=24 ∧ r₃ 14=48 := by decide +kernel

end PrimeFactors.EvenPrimeThreeSquareBase
