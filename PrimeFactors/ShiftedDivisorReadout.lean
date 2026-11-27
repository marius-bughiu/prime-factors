import PrimeFactors.IntermediateShiftedExponent

/-! Recover a candidate prime sum from a partial factorization of N+k, and describe
the portion of a shifted divisor which must lie in the unfactored remainder. -/
namespace PrimeFactors.ShiftedDivisorReadout

/-- Treat the unresolved factor R as a single piece and enumerate all divisors
of the known component H, as well as R times those divisors. -/
def known (H R g : ℕ) : Prop := g ∣ H ∨ ∃ a, a ∣ H ∧ g=R*a

theorem sound {H R g : ℕ} (h : known H R g) : g ∣ H*R := by
  rcases h with small | ⟨a,ah,rfl⟩
  · exact small.trans (dvd_mul_right ..)
  · simpa [Nat.mul_comm R a] using Nat.mul_dvd_mul_right ah R

/-- If the remaining component is prime, every divisor of the neighbor is covered. -/
theorem complete {H R g : ℕ} (prime : R.Prime) (hit : g ∣ H*R) : known H R g := by
  obtain ⟨a,b,ah,br,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hit
  rcases (Nat.dvd_prime prime).mp br with small | large
  · exact Or.inl (by simpa [small] using ah)
  · exact Or.inr ⟨a,ah,by rw [large,Nat.mul_comm]⟩

/-- Skipping this range misses no divisor of the known form. -/
theorem skip {H R g L U : ℕ} (hp : 0<H) (gap : H<L) (beyond : U≤R)
    (bottom : L≤g) (top : g<U) : ¬known H R g := by
  rintro (div | ⟨a,_,eq⟩)
  · have := Nat.le_of_dvd hp div
    omega
  · have ap : 0<a := by by_contra! zero; simp [Nat.eq_zero_of_le_zero zero] at eq; omega
    have := Nat.le_mul_of_pos_right R ap
    omega

/-- A solution in a skipped interval requires a proper divisor of R. If the known
component is small, L≤H*b also forces this unresolved divisor to be large. -/
theorem residual {H R g L U : ℕ} (hp : 0<H) (gap : H<L) (beyond : U≤R)
    (bottom : L≤g) (top : g<U) (hit : g ∣ H*R) :
    ∃ b, b ∣ R ∧ 1<b ∧ b<R ∧ L≤H*b ∧ b<U := by
  obtain ⟨a,b,ah,br,eq⟩ := exists_dvd_and_dvd_of_dvd_mul hit
  have au := Nat.le_of_dvd hp ah
  have gp : 0<g := by omega
  rw [eq] at gp
  have ap := Nat.pos_of_mul_pos_right gp
  have bp := Nat.pos_of_mul_pos_left gp
  have bu : b≤g := eq ▸ Nat.le_mul_of_pos_left b ap
  have mass := bottom.trans (eq.le.trans (Nat.mul_le_mul_right b au))
  have big : 1<b := by
    by_contra! small
    have one : b=1 := by omega
    rw [one,Nat.mul_one] at mass
    omega
  exact ⟨b,br,big,by omega,mass,by omega⟩

open IntermediateTotientObstruction

/-- Two actual later hits in the public divisor search, including the earlier
neighboring-sum example evaluated at a new, explicitly selected exponent. -/
theorem examples :
    rowAt 3 22 15525 108671 ⟨0,1⟩ ⟨1,0⟩=some ⟨23,160⟩ ∧
    15525*160=23*((271-1)*(401-1)) ∧ ¬15525 ∣ (271-1)*(401-1) ∧
    rowAt 3 58030 334258560000 7687946879999 ⟨0,1⟩ ⟨1,0⟩=some ⟨58031,1334712⟩ ∧
    334258560000*1334712=58031*((2101249-1)*(3658751-1)) := by decide +kernel

end PrimeFactors.ShiftedDivisorReadout
