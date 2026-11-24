import PrimeFactors.CountingReadout
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PrimeFactors

/-- Accept a multiplication assignment only when its first input is nontrivial
and no larger than its second input. The input box may include the trivial factors. -/
noncomputable def orderedNontrivialBox (n B : ℕ) : Finset (ℕ × ℕ) :=
  (acceptedBox n B).filter (fun xy => 1 < xy.1 ∧ xy.1 ≤ xy.2)

theorem orderedNontrivialBox_semiprime {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p ≤ q) (inside : q < B) :
    orderedNontrivialBox (p * q) B = {(p, q)} := by
  ext ⟨x, y⟩
  simp only [orderedNontrivialBox, acceptedBox, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨_, hm⟩, hx, hxy⟩
    exact ordered_semiprime_pair_unique hp hq ordered hxy hx hm
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨⟨ordered.trans_lt inside, inside⟩, rfl⟩, hp.one_lt, ordered⟩

/-- Add an unrestricted `k`-bit input and compare it with the low `k` bits
of the larger factor. Every accepting triple has unit weight. -/
noncomputable def lowFactorTriples (n B k : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (orderedNontrivialBox n B ×ˢ Finset.range (2 ^ k)).filter
    (fun xyt => xyt.2 < xyt.1.2 % 2 ^ k)

/-- For a semiprime, the auxiliary input ranges over precisely the residues strictly
below the low word of the larger factor. This also holds for an empty range. -/
theorem lowFactorTriples_semiprime {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p ≤ q) (inside : q < B) (k : ℕ) :
    lowFactorTriples (p * q) B k = {(p, q)} ×ˢ Finset.range (q % 2 ^ k) := by
  ext ⟨xy, t⟩
  simp only [lowFactorTriples, orderedNontrivialBox_semiprime hp hq ordered inside,
    Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_range]
  constructor
  · rintro ⟨⟨rfl, _⟩, h⟩
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨⟨rfl, h.trans (Nat.mod_lt _ (by positivity))⟩, h⟩

theorem card_lowFactorTriples {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p ≤ q) (inside : q < B) (k : ℕ) :
    (lowFactorTriples (p * q) B k).card = q % 2 ^ k := by
  simp [lowFactorTriples_semiprime hp hq ordered inside]

/-- A single unweighted count modulo a power of two, with its canonical residue as output. -/
noncomputable def lowFactorReadout (n B k : ℕ) : ℕ :=
  ((lowFactorTriples n B k).card : ZMod (2 ^ k)).val

theorem lowFactorReadout_semiprime {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p ≤ q) (inside : q < B) (k : ℕ) :
    lowFactorReadout (p * q) B k = q % 2 ^ k := by
  rw [lowFactorReadout, card_lowFactorTriples hp hq ordered inside, ZMod.val_natCast,
    Nat.mod_mod]

/-- Least integer number of bits whose quadruple covers the product word. -/
def quarterWord (b : ℕ) : ℕ := (b + 3) / 4

theorem quarterWord_le_iff (b k : ℕ) : quarterWord b ≤ k ↔ b ≤ 4 * k := by
  unfold quarterWord
  omega

/-- Taking the ceiling of one quarter of the product width meets the exact
fourth-root threshold used by the small-root theorem. -/
theorem quarterWord_fourth_power {n b : ℕ} (fits : n < 2 ^ b) :
    n < (2 ^ quarterWord b) ^ 4 := by
  rw [← pow_mul]
  exact fits.trans_le (Nat.pow_le_pow_right (by decide)
    (by simpa [Nat.mul_comm] using (quarterWord_le_iff b (quarterWord b)).mp le_rfl))

/-- Full product-width inputs and a quarter-width counter suffice, regardless of the prime gap. -/
theorem quarterWordReadout {p q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p ≤ q) (fits : p * q < 2 ^ b) :
    lowFactorReadout (p * q) (2 ^ b) (quarterWord b) = q % 2 ^ quarterWord b ∧
      p * q < (2 ^ quarterWord b) ^ 4 := by
  have qle : q ≤ p * q := by simpa using Nat.mul_le_mul_right q hp.one_le
  exact ⟨lowFactorReadout_semiprime hp hq ordered (qle.trans_lt fits) _, quarterWord_fourth_power fits⟩

/-- A constant-factor size guess for the divisor bounds the unknown quotient in the linear
small-root theorem. The fourth-root precision works uniformly in the size exponent. -/
theorem quotient_le_smallRoot_bound {N M q C β x : ℝ} (hN : 1 ≤ N) (hC : 0 ≤ C)
    (precision : N ^ (1 / 4 : ℝ) ≤ M) (guess : q ≤ C * N ^ β) (quotient : x * M ≤ q) :
    x ≤ C * N ^ (β ^ 2) := by
  have positive : 0 < N ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  refine (le_div_iff₀ (positive.trans_le precision)).mpr quotient |>.trans ?_
  calc
    q / M ≤ (C * N ^ β) / M := div_le_div_of_nonneg_right guess (positive.trans_le precision).le
    _ ≤ (C * N ^ β) / N ^ (1 / 4 : ℝ) :=
      div_le_div_of_nonneg_left (mul_nonneg hC (Real.rpow_nonneg (by linarith) _)) positive precision
    _ = C * N ^ (β - 1 / 4) := by rw [Real.rpow_sub (by linarith : 0 < N)]; ring
    _ ≤ C * N ^ (β ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.rpow_le_rpow_of_exponent_le hN (by nlinarith only [sq_nonneg (β - 1 / 2)])

/-- Directly enumerate the assignments for 77, including the zero-bit empty range. -/
theorem lowFactorReadout_77 :
    (lowFactorTriples 77 16 3).card = 3 ∧ lowFactorReadout 77 16 3 = 3 ∧
    (lowFactorTriples 77 16 0).card = 0 ∧ lowFactorReadout 77 16 0 = 0 := by decide +kernel

end PrimeFactors
