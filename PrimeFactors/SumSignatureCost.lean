import PrimeFactors.OffsetAdaptiveFloor
import PrimeFactors.ResidueCount

namespace PrimeFactors.SumSignatureCost

open Finset

set_option exponentiation.threshold 2048

/-- The standard public balanced interval contains this whole subinterval at 2048 bits. -/
theorem interval_span {n : ℕ} (bits : 2^2047 ≤ n) :
    let t := (4*n).sqrt
    ∀ s ∈ Icc (t+1) (t+1+2^1020), 4*n ≤ s^2 ∧ 2*s^2 ≤ 9*n := by
  let t := (4*n).sqrt
  have lower : 20*(2^1020+1) ≤ t := Nat.le_sqrt'.mpr
    ((by decide +kernel : (20*((2:ℕ)^1020+1))^2 ≤ 4*2^2047).trans (Nat.mul_le_mul_left 4 bits))
  have square : t^2 ≤ 4*n := Nat.sqrt_le' _
  change ∀ s ∈ Icc (t+1) (t+1+2^1020), _
  intro s hs
  obtain ⟨lo, hi⟩ := mem_Icc.mp hs
  change t+1 ≤ s at lo
  change s ≤ t+1+2^1020 at hi
  have endpoint : 20*s ≤ 21*t := by omega
  have squares := Nat.pow_le_pow_left endpoint 2
  exact ⟨(Nat.lt_succ_sqrt' (4*n)).le.trans (Nat.pow_le_pow_left lo 2),
    by nlinarith only [squares, square]⟩

/-- Number of locally admissible sums at an odd prime, including repeated roots. -/
noncomputable def localCount (n p : ℕ) := Nat.card {s : ZMod p // AdmissibleSum (n : ZMod p) s}

theorem regular_le_count {n p : ℕ} (hp : p.Prime) (coprime : (n : ZMod p) ≠ 0) :
    OffsetAdaptiveFloor.regular p ≤ localCount n p := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [localCount, card_admissibleSum_eq p _ coprime]
  have size := two_mul_card_factorSumResidues p _ coprime
  unfold OffsetAdaptiveFloor.regular
  omega

/-- A full half-list contains every tuple on its side. Clipping the sums after
building the lists cannot save their initial construction cost. The fixed stride may
supply a factor of four of the period at zero cost. -/
theorem larger_list {n stride a b : ℕ} (S : Finset ℕ)
    (ok : ∀ p ∈ S, p.Prime ∧ p ≠ 2 ∧ (n : ZMod p) ≠ 0)
    (strideCap : stride ≤ 4) (covers : 2^1020 < stride * ∏ p ∈ S, p)
    (tables : (∏ p ∈ S, localCount n p) ≤ a*b) :
    2^442 < max a b := by
  have modulus := covers.trans_le (Nat.mul_le_mul_right _ strideCap)
  have threshold : 2^1023 < 2*16*(∏ p ∈ S, p) := by
    have scale := Nat.mul_lt_mul_of_pos_left modulus (by decide : 0<8)
    have shift : (8:ℕ)*2^1020 = 2^1023 := by decide +kernel
    omega
  have floor := OffsetAdaptiveFloor.scaled_floor S (m := 16) (by decide)
    (fun p h => ⟨(ok p h).1, (ok p h).2.1⟩) threshold
  have counts : (∏ p ∈ S, OffsetAdaptiveFloor.regular p) ≤ a*b :=
    (Finset.prod_le_prod' (fun p h => regular_le_count (ok p h).1 (ok p h).2.2)).trans tables
  by_contra! small
  have product := Nat.mul_le_mul ((le_max_left a b).trans small) ((le_max_right a b).trans small)
  have cap : (16:ℕ)*(2^442*2^442) ≤ 2^889 := by decide +kernel
  exact (not_le_of_gt floor) ((Nat.mul_le_mul_left 16 (counts.trans product)).trans cap)

end PrimeFactors.SumSignatureCost
