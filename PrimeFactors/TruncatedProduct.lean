import PrimeFactors.LowFactorBits
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace PrimeFactors

/-- Truncated product witnesses indexed by the larger input, the smaller input, and the
auxiliary counter. The interval for the counter includes exactly the words below the low bits. -/
noncomputable def truncatedProductTriples (n B M k : ℕ) : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
  (Finset.range B).sigma fun y => (Finset.range (y + 1)).sigma fun x =>
    if 1 < x ∧ x * y % M = n % M then Finset.range (y % 2 ^ k) else ∅

/-- An exact row-sum identity for arbitrary box size, modulus and counter width. -/
theorem card_truncatedProductTriples (n B M k : ℕ) :
    (truncatedProductTriples n B M k).card =
      ∑ y ∈ Finset.range B, ∑ x ∈ Finset.range (y + 1),
        if 1 < x ∧ x * y % M = n % M then y % 2 ^ k else 0 := by
  simp only [truncatedProductTriples, Finset.card_sigma]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

private def triangle (f : ℕ → ℕ → ZMod 2) (B : ℕ) : ZMod 2 :=
  ∑ y ∈ Finset.range B, ∑ x ∈ Finset.range (y + 1), f x y

private theorem double_zero (z : ZMod 2) : z + z = 0 := by
  rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

/-- In characteristic two the sum of a symmetric square array equals its diagonal sum. -/
theorem symmetric_square_sum_mod_two (f : ℕ → ℕ → ZMod 2)
    (symm : ∀ x y, f x y = f y x) (B : ℕ) :
    ∑ y ∈ Finset.range B, ∑ x ∈ Finset.range B, f x y =
      ∑ x ∈ Finset.range B, f x x := by
  induction B with
  | zero => simp
  | succ B ih =>
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib, ih]
    simp_rw [symm B]
    linear_combination double_zero (∑ x ∈ Finset.range B, f x B)

/-- Two identical diagonal blocks of a periodic triangle cancel in characteristic two.
The rectangular off-diagonal block remains. -/
private theorem triangle_double (f : ℕ → ℕ → ZMod 2) (L : ℕ)
    (leftPeriod : ∀ x y, f (L + x) y = f x y) (rightPeriod : ∀ x y, f x (L + y) = f x y) :
    triangle f (L + L) = ∑ y ∈ Finset.range L, ∑ x ∈ Finset.range L, f x y := by
  unfold triangle
  rw [Finset.sum_range_add]
  have row (y : ℕ) : ∑ x ∈ Finset.range (L + y + 1), f x (L + y) =
      (∑ x ∈ Finset.range L, f x y) + ∑ x ∈ Finset.range (y + 1), f x y := by
    rw [Nat.add_assoc, Finset.sum_range_add]
    simp only [rightPeriod, leftPeriod]
  simp_rw [row]
  rw [Finset.sum_add_distrib]
  linear_combination double_zero (∑ y ∈ Finset.range L, ∑ x ∈ Finset.range (y + 1), f x y)

private theorem remove_trivial_row (f : ℕ → ℕ → ZMod 2)
    (zeroLeft : ∀ y, f 0 y = 0) (atZero : f 1 0 = 0) (B : ℕ) :
    triangle (fun x y => if 1 < x then f x y else 0) B +
      (∑ y ∈ Finset.range B, f 1 y) = triangle f B := by
  unfold triangle
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  cases y with
  | zero => simp [zeroLeft, atZero]
  | succ y => simp [Finset.sum_range_succ', zeroLeft]

private def productFlag (n M x y : ℕ) : ZMod 2 := if x * y % M = n % M then 1 else 0

private theorem solution_odd {n M x y : ℕ} (odd : Odd n) (evenMod : 2 ∣ M)
    (sol : x * y % M = n % M) : Odd x ∧ Odd y := by
  have modTwo : x * y ≡ n [MOD 2] := Nat.ModEq.of_dvd evenMod sol
  exact Nat.odd_mul.mp (Nat.odd_iff.mpr (Eq.trans modTwo (Nat.odd_iff.mp odd)))

private theorem card_parity_triangle {n M k : ℕ} (odd : Odd n) (evenMod : 2 ∣ M)
    (counter : 1 ≤ k) (B : ℕ) :
    ((truncatedProductTriples n B M k).card : ZMod 2) =
      triangle (fun x y => if 1 < x then productFlag n M x y else 0) B := by
  rw [card_truncatedProductTriples, triangle]
  simp only [Nat.cast_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : 1 < x
  · by_cases sol : x * y % M = n % M
    · simp only [hx, sol, and_self, ↓reduceIte, productFlag]
      have dk : 2 ∣ 2 ^ k := by simpa using Nat.pow_dvd_pow 2 counter
      apply (ZMod.natCast_eq_natCast_iff (y % 2 ^ k) 1 2).mpr
      exact (Nat.mod_mod_of_dvd y dk).trans (Nat.odd_iff.mp (solution_odd odd evenMod sol).2)
    · simp [hx, sol, productFlag]
  · simp [hx]

/-- A reusable block criterion. The box has side `4H`. Period `2H` cancels the two
triangles and the excluded row. The shifted diagonal is periodic with period `H`
because the modulus divides both `2H` and `H²`. -/
theorem truncatedProduct_even_of_blocks {n M H k : ℕ} (odd : Odd n) (evenMod : 2 ∣ M)
    (half : M ∣ H + H) (square : M ∣ H * H) (counter : 1 ≤ k) :
    Even (truncatedProductTriples n ((H + H) + (H + H)) M k).card := by
  let f := productFlag n M
  let L := H + H
  have symm (x y : ℕ) : f x y = f y x := by simp [f, productFlag, Nat.mul_comm]
  have leftPeriod (x y : ℕ) : f (L + x) y = f x y := by
    have mulDvd : M ∣ L * y := dvd_mul_of_dvd_left half y
    simp only [f, productFlag, Nat.add_mul, Nat.add_mod (L * y), Nat.mod_eq_zero_of_dvd mulDvd,
      Nat.zero_add, Nat.mod_mod]
  have rightPeriod (x y : ℕ) : f x (L + y) = f x y :=
    (symm _ _).trans ((leftPeriod y x).trans (symm _ _))
  have diag (x : ℕ) : f (H + x) (H + x) = f x x := by
    have eq : (H + x) * (H + x) = (H * H + (H + H) * x) + x * x := by ring
    have dv : M ∣ H * H + (H + H) * x := dvd_add square (dvd_mul_of_dvd_left half x)
    simp only [f, productFlag, eq, Nat.add_mod (H * H + (H + H) * x),
      Nat.mod_eq_zero_of_dvd dv, Nat.zero_add, Nat.mod_mod]
  have z : triangle f (L + L) = 0 := by
    rw [triangle_double f L leftPeriod rightPeriod, symmetric_square_sum_mod_two f symm]
    dsimp only [L]
    rw [Finset.sum_range_add]
    simp only [diag, double_zero]
  have row : ∑ y ∈ Finset.range (L + L), f 1 y = 0 := by
    rw [Finset.sum_range_add]
    simp only [rightPeriod, double_zero]
  have zeroLeft (y : ℕ) : f 0 y = 0 := by
    have impossible (sol : 0 * y % M = n % M) := (solution_odd odd evenMod sol).1
    exact if_neg (fun h => Nat.not_odd_zero (impossible h))
  have zeroAt : f 1 0 = 0 := (symm 1 0).trans (zeroLeft 1)
  have whole := remove_trivial_row f zeroLeft zeroAt (L + L)
  rw [row, add_zero, z] at whole
  apply even_iff_two_dvd.mpr
  apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ 2).mp
  exact (card_parity_triangle odd evenMod counter (L + L)).trans whole

/-- Dropping at least one product bit below the input width forces an even triple count
for every odd target, once at least two product bits and one counter bit are retained. -/
theorem truncatedProduct_even {n b m k : ℕ} (odd : Odd n)
    (two : 2 ≤ m) (drop : m < b) (counter : 1 ≤ k) :
    Even (truncatedProductTriples n (2 ^ b) (2 ^ m) k).card := by
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le two
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le (show m + 1 ≤ b from drop)
  subst m b
  let H := 2 * 2 ^ s * 2 ^ a
  have modulus : 2 ^ (2 + s) = 4 * 2 ^ s := by rw [pow_add]; norm_num
  have width : 2 ^ (2 + s + 1 + a) = (H + H) + (H + H) := by
    simp only [pow_add, H]; ring
  rw [width, modulus]
  apply truncatedProduct_even_of_blocks odd _ _ _ counter
  · exact ⟨2 * 2 ^ s, by ring⟩
  · exact ⟨2 ^ a, by dsimp [H]; ring⟩
  · exact ⟨2 ^ s * (2 ^ a) ^ 2, by dsimp [H]; ring⟩

/-- For an odd semiprime covered by the box, the wrapped truncated and exact counts
disagree even in their least significant bit. -/
theorem truncatedProduct_readout_ne {p q b m k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p ≤ q) (inside : q < 2 ^ b) (odd : Odd (p * q))
    (two : 2 ≤ m) (drop : m < b) (counter : 1 ≤ k) :
    (truncatedProductTriples (p * q) (2 ^ b) (2 ^ m) k).card % 2 ^ k ≠
      lowFactorReadout (p * q) (2 ^ b) k := by
  rw [lowFactorReadout_semiprime hp hq ordered inside]
  have dk : 2 ∣ 2 ^ k := by simpa using Nat.pow_dvd_pow 2 counter
  have even := Nat.even_iff.mp (truncatedProduct_even odd two drop counter)
  have qOdd := Nat.odd_iff.mp (Nat.odd_mul.mp odd).2
  intro equal
  have h := congrArg (fun t : ℕ => t % 2) equal
  dsimp only at h
  rw [Nat.mod_mod_of_dvd _ dk, Nat.mod_mod_of_dvd _ dk, even, qOdd] at h
  contradiction

/-- Keeping the lowest three product bits of 77 gives 30 witnesses, while exact
multiplication gives three. Their three-bit outputs are 6 and 3. -/
theorem truncatedProduct_77 :
    (truncatedProductTriples 77 16 8 3).card = 30 ∧
    (truncatedProductTriples 77 16 8 3).card % 8 = 6 ∧ lowFactorReadout 77 16 3 = 3 := by
  decide +kernel

end PrimeFactors
