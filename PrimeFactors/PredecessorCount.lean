import PrimeFactors.DiscriminantStride
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace PrimeFactors

/-- A finite pool of candidate totients admits at most one predecessor pair
for each totient and first divisor. Both predecessors must be positive. -/
theorem predecessor_pairs_card {pairs : Finset (ℕ × ℕ)} {pool : Finset ℕ}
    (inside : ∀ x ∈ pairs, 0 < x.1 ∧ 0 < x.2 ∧ x.1*x.2 ∈ pool) :
    pairs.card ≤ ∑ n ∈ pool, n.divisors.card := by
  let key (x : ℕ × ℕ) : Σ _ : ℕ, ℕ := ⟨x.1*x.2,x.1⟩
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn key
  · intro x hx
    obtain ⟨h₁,h₂,mem⟩ := inside x hx
    exact Finset.mem_sigma.mpr ⟨mem,Nat.mem_divisors.mpr ⟨dvd_mul_right ..,
      (Nat.mul_pos h₁ h₂).ne'⟩⟩
  · intro x hx y _ eq
    have first : x.1=y.1 := congrArg (fun k : Σ _ : ℕ, ℕ => k.2) eq
    have prod : x.1*x.2=y.1*y.2 := congrArg Sigma.fst eq
    rw [← first] at prod
    exact Prod.ext first (Nat.eq_of_mul_eq_mul_left (inside x hx).1 prod)

/-- Two members of the linear family at indices i and i+k. -/
def nearSquareForm (i t : ℕ) : ℕ := i^2*t+2*i+1

def nearSquareCenter (i k t : ℕ) : ℕ := i*(i+k)*t+i+(i+k)

/-- All family pairs have totient exactly k² below a square, independently of t. -/
theorem nearSquare_predecessor (i k t : ℕ) :
    (nearSquareForm i t-1)*(nearSquareForm (i+k) t-1)+k^2=(nearSquareCenter i k t)^2 := by
  simp [nearSquareForm,nearSquareCenter]
  ring

/-- The square at the public root leaves a multiple of the squared index gap. -/
theorem nearSquare_residual (i k t : ℕ) :
    nearSquareForm i (t+1)*nearSquareForm (i+k) (t+1) =
      (nearSquareCenter i k (t+1)+1)^2+k^2*t := by
  unfold nearSquareForm nearSquareCenter
  ring

/-- For close enough indices the product identifies the center using one square root. -/
theorem nearSquare_floor (i k t : ℕ) (gap : k^2 ≤ 2*i*(i+k)) :
    (nearSquareForm i (t+1)*nearSquareForm (i+k) (t+1)).sqrt =
      nearSquareCenter i k (t+1)+1 := by
  rw [nearSquare_residual]
  apply Nat.le_antisymm
  · apply Nat.le_of_lt_succ
    apply Nat.sqrt_lt'.mpr
    have h := Nat.mul_le_mul_right t gap
    unfold nearSquareCenter
    nlinarith only [h, Nat.zero_le (i*(i+k)), Nat.zero_le i, Nat.zero_le k]
  · exact Nat.le_sqrt'.mpr (Nat.le_add_right _ _)

/-- A product-only sum at a proposed index gap, also usable outside the family. -/
def correctedPredecessorSum (N k : ℕ) := N+1+k^2-(N.sqrt-1)^2

theorem nearSquare_sum (i k t : ℕ) (gap : k^2 ≤ 2*i*(i+k)) :
    correctedPredecessorSum (nearSquareForm i (t+1)*nearSquareForm (i+k) (t+1)) k =
    nearSquareForm i (t+1)+nearSquareForm (i+k) (t+1) := by
  rw [correctedPredecessorSum, nearSquare_floor i k t gap, Nat.add_sub_cancel]
  apply Nat.sub_eq_of_eq_add
  unfold nearSquareForm nearSquareCenter
  ring


/-- A prime dividing a positive integer to exponent one must divide its
multiplier in every scaled-square representation. -/
theorem prime_dvd_square_multiplier {r v d y : ℕ} (hr : Nat.Prime r)
    (dvd₁ : r ∣ v) (dvd₂ : ¬r^2 ∣ v) (rep : v=d*y^2) : r ∣ d := by
  rw [rep] at dvd₁ dvd₂
  rcases hr.dvd_mul.mp dvd₁ with hd | hy
  · exact hd
  · exact (dvd₂ (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (hr.dvd_of_dvd_pow hy) 2) _)).elim

/-- The 92-bit example's large prime multiplier occurs only once in its
totient. The benchmark's Lucas certificate for q also establishes its
primality. -/
theorem nearSquare_large_multiplier_example :
    let p := 42949673760401
    let q := 63403382146843
    p = nearSquareForm 200 1073741844 ∧ q = nearSquareForm 243 1073741844 ∧
      p*q = 2723154578512940020180564043 ∧
      130459634047 ∣ (p-1)*(q-1) ∧ ¬130459634047^2 ∣ (p-1)*(q-1) := by
  decide +kernel


/-- Even when both indices and the shared parameter are free, positive
indices fitting below X occupy a square of side at most sqrt(X/t). -/
theorem nearSquare_index_pairs_card {s : Finset (ℕ × ℕ)} {X t : ℕ} (ht : 0 < t)
    (within : ∀ z ∈ s, 1 ≤ z.1 ∧ nearSquareForm z.1 t ≤ X ∧
      1 ≤ z.2 ∧ nearSquareForm z.2 t ≤ X) : s.card ≤ X/t := by
  let I := Finset.Icc 1 (X/t).sqrt
  have mem {i : ℕ} (pos : 1 ≤ i) (h : nearSquareForm i t ≤ X) : i ∈ I := by
    apply Finset.mem_Icc.mpr
    refine ⟨pos, Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le ht).mpr ?_)⟩
    dsimp [nearSquareForm] at h
    omega
  have subset : s ⊆ I ×ˢ I := by
    intro z hz
    obtain ⟨pi,hi,pj,hj⟩ := within z hz
    exact Finset.mem_product.mpr ⟨mem pi hi,mem pj hj⟩
  calc s.card ≤ (I ×ˢ I).card := Finset.card_le_card subset
    _ = (X/t).sqrt * (X/t).sqrt := by simp [I]
    _ ≤ X/t := Nat.sqrt_le _

end PrimeFactors
