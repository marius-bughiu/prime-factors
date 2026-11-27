import PrimeFactors.WeightedCrowdingEstimates
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! Many prime squares pass affine Jacobi tests when the candidate search
also admits composites. Only a large prime dividing a label can remove its square. -/

namespace PrimeFactors.SquarePrimeDecoys
open Finset Real
open WeightedCrowdingEstimates (Dusart count_eq)
set_option exponentiation.threshold 8192

private theorem endpoint {x : ℕ} (lo : 2^511 ≤ x) (hi : x ≤ 2^512) (du : Dusart) :
    353*x.primeCounting ≤ x ∧ x ≤ 355*x.primeCounting := by
  have a := log_le_log (show 0 < (2:ℝ)^511 by positivity) (show (2:ℝ)^511 ≤ x by exact_mod_cast lo)
  have b := log_le_log (show 0 < (x:ℝ) by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2^511) lo)
    (show (x:ℝ) ≤ 2^512 by exact_mod_cast hi)
  rw [log_pow] at a b
  norm_num1 at a b
  have low : (353:ℝ) ≤ log x-11/10 := by linarith only [a,log_two_gt_d9]
  have high : log (x:ℝ)-1 ≤ 355 := by linarith only [b,log_two_lt_d9]
  obtain ⟨l,u⟩ := du x (lt_of_lt_of_le (by decide +kernel : 60184 < 2^511) lo)
  have u' := (le_div_iff₀ (by linarith only [low] : 0 < log (x:ℝ)-11/10)).mp u
  have l' := (div_le_iff₀ (by linarith only [low] : 0 < log (x:ℝ)-1)).mp l
  constructor
  · have := (mul_le_mul_of_nonneg_left low (Nat.cast_nonneg x.primeCounting)).trans u'
    rw [mul_comm] at this
    exact_mod_cast this
  · have := l'.trans (mul_le_mul_of_nonneg_left high (Nat.cast_nonneg x.primeCounting))
    rw [mul_comm (x.primeCounting:ℝ) 355] at this
    exact_mod_cast this

/-- A simple rational comparison prices the number of prime bases in one
interval. The additive allowance is reserved for primes dividing the labels. -/
theorem base_count {a b : ℕ} (low : 2^511 ≤ a) (ab : a ≤ b) (high : b ≤ 2^512)
    (room : 355*a+355*353*(2^498+8800) < 353*b) (du : Dusart) :
    2^498+8800 < ((Ioc a b).filter Nat.Prime).card := by
  have l := (endpoint low (ab.trans high) du).1
  have u := (endpoint (low.trans ab) high du).2
  have diff := count_eq a b ab
  omega

private theorem exceptions (P : Finset ℕ) {z : ℤ} (nz : z ≠ 0) (size : z.natAbs < 2^4098)
    (valid : ∀ p ∈ P, p.Prime ∧ 2^511 ≤ p) :
    (P.filter (fun p => p ∣ z.natAbs)).card ≤ 8 := by
  let s := P.filter (fun p => p ∣ z.natAbs)
  have div : ∏ p ∈ s, p ∣ z.natAbs := prod_primes_dvd _
    (fun p hp => Nat.prime_iff.mp (valid p (mem_filter.mp hp).1).1)
    (fun _ hp => (mem_filter.mp hp).2)
  have product : (2^511)^s.card ≤ ∏ p ∈ s, p :=
    pow_card_le_prod _ _ _ fun p hp => (valid p (mem_filter.mp hp).1).2
  have h := product.trans_lt ((Nat.le_of_dvd (Int.natAbs_pos.mpr nz) div).trans_lt size)
  rw [← pow_mul] at h
  have bits := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp h
  change s.card ≤ 8
  omega

/-- The number of distinct prime squares satisfying all signs. This counts
the values themselves by injectivity of squaring on naturals. -/
theorem square_survivors {k : ℕ} (z : Fin k → ℤ) (P : Finset ℕ)
    (labels : ∀ i, z i ≠ 0 ∧ (z i).natAbs < 2^4098)
    (bases : ∀ p ∈ P, p.Prime ∧ 2^511 ≤ p) :
    P.card ≤ ((P.filter (fun p => ∀ i, jacobiSym (z i) (p^2) = 1)).image (fun p => p^2)).card + 8*k := by
  classical
  let bad (i : Fin k) := P.filter fun p => p ∣ (z i).natAbs
  let rejected := univ.biUnion bad
  have count : rejected.card ≤ 8*k := calc
    _ ≤ ∑ i, (bad i).card := card_biUnion_le
    _ ≤ ∑ _ : Fin k, 8 := sum_le_sum fun i _ => exceptions P (labels i).1 (labels i).2 bases
    _ = _ := by simp [Nat.mul_comm]
  let good := P.filter (fun p => ∀ i, jacobiSym (z i) (p^2) = 1)
  have cover : P ⊆ good ∪ rejected := by
    intro p hp
    by_cases h : p ∈ rejected
    · exact mem_union_right _ h
    apply mem_union_left _ (mem_filter.mpr ⟨hp,?_⟩)
    intro i
    have no : ¬p ∣ (z i).natAbs := fun d =>
      h (mem_biUnion.mpr ⟨i,mem_univ i,mem_filter.mpr ⟨hp,d⟩⟩)
    rw [jacobiSym.pow_right]
    exact jacobiSym.sq_one ((bases p hp).1.coprime_iff_not_dvd.mpr no).symm
  have im : (good.image (fun p => p^2)).card = good.card := by
    apply card_image_of_injOn
    intro x _ y _ h
    exact Nat.pow_left_injective (by decide : 2≠0) h
  change P.card ≤ (good.image (fun p => p^2)).card + 8*k
  rw [im]
  exact ((card_le_card cover).trans (card_union_le _ _)).trans (Nat.add_le_add_left count _)

theorem affine_size {N r : ℕ} (size : N < 2^2048) (draw : r < N) :
    (1-4*(N:ℤ)*r) ≠ 0 ∧ (1-4*(N:ℤ)*r).natAbs < 2^4098 := by
  have prod := Nat.mul_lt_mul_of_lt_of_le size (show r ≤ 2^2048 from (draw.trans size).le)
    (by decide : 0 < 2^2048)
  have cap : 4*(N*r) < 2^4098 := (Nat.mul_lt_mul_left (by decide : 0<4)).mpr prod
  have zi : 4*((N:ℤ)*r) < (2:ℤ)^4098 := by exact_mod_cast cap
  constructor
  · rw [mul_assoc]
    omega
  · have nonneg : 0 ≤ (N:ℤ)*r := mul_nonneg (Int.natCast_nonneg N) (Int.natCast_nonneg r)
    have room : (1:ℤ) < 2^4098 := by decide +kernel
    have a : |1-4*(N:ℤ)*r| < (2:ℤ)^4098 := by
      rw [abs_lt, mul_assoc]
      constructor <;> omega
    rw [Int.abs_eq_natAbs] at a
    exact_mod_cast a

end PrimeFactors.SquarePrimeDecoys
