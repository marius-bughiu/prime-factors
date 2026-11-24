import PrimeFactors.CountingReadout
import PrimeFactors.DivisorSum

namespace PrimeFactors

/-- With both input words wide enough, the multiplication witnesses are precisely
the positive divisor pairs of the target, including the trivial orientations. -/
theorem acceptedBox_eq_divisorsAntidiagonal {n B : ℕ} (positive : 0 < n) (fits : n < B) :
    acceptedBox n B = n.divisorsAntidiagonal := by
  ext ⟨x, y⟩
  simp only [acceptedBox, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Nat.mem_divisorsAntidiagonal]
  constructor
  · exact fun h => ⟨h.2, positive.ne'⟩
  · rintro ⟨h, _⟩
    have xd : x ∣ n := h ▸ dvd_mul_right x y
    have yd : y ∣ n := h ▸ dvd_mul_left y x
    exact ⟨⟨(Nat.le_of_dvd positive xd).trans_lt fits,
      (Nat.le_of_dvd positive yd).trans_lt fits⟩, h⟩

/-- An arbitrary weight on the first input occurs once for every positive divisor. -/
theorem sum_fullBox_first {R : Type*} [AddCommMonoid R] {n B : ℕ}
    (positive : 0 < n) (fits : n < B) (weight : ℕ → R) :
    ∑ xy ∈ acceptedBox n B, weight xy.1 = ∑ d ∈ n.divisors, weight d := by
  rw [acceptedBox_eq_divisorsAntidiagonal positive fits]
  exact Nat.sum_divisorsAntidiagonal (fun d _ => weight d)

/-- The linear digit weights add the cardinality and the first moment of any finite set. -/
theorem sum_inputDigitWeight_mod (radix T : ℕ) (ds : Finset ℕ) :
    Nat.ModEq (T ^ 2) (∑ d ∈ ds, inputDigitWeight radix T d) (ds.card + T * ∑ d ∈ ds, d) := by
  induction ds using Finset.induction_on with
  | empty => simp [Nat.ModEq]
  | @insert d ds hd ih =>
    rw [Finset.sum_insert hd, Finset.sum_insert hd, Finset.card_insert_of_not_mem hd]
    convert (inputDigitWeight_mod radix T d).add ih using 1
    ring

/-- The scalar uses a single binary residue of width `4*b`. -/
theorem divisorTensor_modulus (b : ℕ) : (2 ^ (2 * b) : ℕ) ^ 2 = 2 ^ (4 * b) := by
  rw [← pow_mul]
  congr 1
  ring

/-- Canonical representative of the scalar obtained by weighting the first input's set bits. -/
noncomputable def divisorTensorScalar (b n : ℕ) : ℕ :=
  (∑ xy ∈ acceptedBox n (2 ^ b), inputDigitWeight 2 (2 ^ (2 * b)) xy.1) % 2 ^ (4 * b)

/-- The same contraction performed directly in the scalar ring. -/
noncomputable def divisorTensorResidue (b n : ℕ) : ZMod (2 ^ (4 * b)) :=
  ∑ xy ∈ acceptedBox n (2 ^ b), (inputDigitWeight 2 (2 ^ (2 * b)) xy.1 : ZMod (2 ^ (4 * b)))

theorem divisorTensorResidue_val (b n : ℕ) : (divisorTensorResidue b n).val = divisorTensorScalar b n := by
  unfold divisorTensorResidue divisorTensorScalar
  rw [← Nat.cast_sum, ZMod.val_natCast]

/-- The residue of a first-input weight is an ordinary product of exactly `b` unary
bit weights in the scalar ring, including the neutral weights on leading zero bits. -/
theorem inputDigitWeight_eq_wireProduct {x b : ℕ} (fits : x < 2 ^ b) :
    (inputDigitWeight 2 (2 ^ (2 * b)) x : ZMod (2 ^ (4 * b))) =
      ((List.range b).map fun i =>
        1 + (2 : ZMod (2 ^ (4 * b))) ^ (2 * b) * (2 ^ i * (x.testBit i).toNat)).prod := by
  let digit (i : ℕ) := 2 ^ i * (x.testBit i).toNat
  have bits (j : ℕ) : ((List.range j).map digit).sum = x % 2 ^ j := by
    induction j with
    | zero => simp [Nat.mod_one]
    | succ j ih =>
      rw [List.sum_range_succ, ih, Nat.mod_pow_succ]
      simp only [digit, Nat.toNat_testBit]
  let T := 2 ^ (2 * b)
  let tags := ((List.range b).map digit).map (fun c => 1 + T * c)
  have h := digit_weight_product_mod T ((List.range b).map digit)
  rw [bits, Nat.mod_eq_of_lt fits] at h
  calc
    _ = (tags.prod : ZMod (2 ^ (4 * b))) := by
      apply (ZMod.natCast_eq_natCast_iff ..).mpr
      rw [← divisorTensor_modulus]
      exact (inputDigitWeight_mod 2 T x).trans h.symm
    _ = _ := by simp [tags, T, digit, List.map_map, Function.comp_def]

/-- This fixed-width product of per-bit scalars can be attached directly at the input wires. -/
theorem divisorTensorResidue_eq_wireSum (b n : ℕ) :
    divisorTensorResidue b n = ∑ xy ∈ acceptedBox n (2 ^ b),
      ((List.range b).map fun i =>
        1 + (2 : ZMod (2 ^ (4 * b))) ^ (2 * b) * (2 ^ i * (xy.1.testBit i).toNat)).prod := by
  unfold divisorTensorResidue
  refine Finset.sum_congr rfl fun xy hxy => inputDigitWeight_eq_wireProduct ?_
  exact Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp hxy).1).1

private theorem divisorTensor_word_bounds {b n : ℕ} (positive : 0 < n) (fits : n < 2 ^ b) :
    n.divisors.card < 2 ^ (2 * b) ∧ ArithmeticFunction.sigma 1 n < 2 ^ (2 * b) := by
  have sumBound : ∑ d ∈ n.divisors, d ≤ n.divisors.card * n := by
    simpa using n.divisors.sum_le_card_nsmul id n
      (fun d hd => Nat.le_of_dvd positive (Nat.dvd_of_mem_divisors hd))
  have cardBound := Nat.card_divisors_le_self n
  have sqBound : n * n < 2 ^ b * 2 ^ b := Nat.mul_lt_mul_of_lt_of_lt fits fits
  rw [two_mul, pow_add, ArithmeticFunction.sigma_one_apply]
  constructor
  · exact (cardBound.trans (Nat.le_mul_of_pos_right n positive)).trans_lt sqBound
  · exact (sumBound.trans (Nat.mul_le_mul_right n cardBound)).trans_lt sqBound

/-- The residue has two exact base-`2^(2*b)` digits, the divisor count and divisor sum. -/
theorem divisorTensorScalar_eq {b n : ℕ} (positive : 0 < n) (fits : n < 2 ^ b) :
    divisorTensorScalar b n = n.divisors.card + 2 ^ (2 * b) * ArithmeticFunction.sigma 1 n := by
  let T := 2 ^ (2 * b)
  obtain ⟨countFit, sumFit⟩ := divisorTensor_word_bounds positive fits
  have upper : n.divisors.card + T * ArithmeticFunction.sigma 1 n < T ^ 2 := by
    have step := Nat.mul_le_mul_left T (show ArithmeticFunction.sigma 1 n + 1 ≤ T from sumFit)
    change n.divisors.card < T at countFit
    nlinarith only [step, countFit]
  unfold divisorTensorScalar
  rw [← divisorTensor_modulus b, sum_fullBox_first positive fits]
  have h := sum_inputDigitWeight_mod 2 T n.divisors
  rw [← ArithmeticFunction.sigma_one_apply] at h
  exact Eq.trans h (Nat.mod_eq_of_lt upper)

theorem divisorTensorScalar_mod {b n : ℕ} (positive : 0 < n) (fits : n < 2 ^ b) :
    divisorTensorScalar b n % 2 ^ (2 * b) = n.divisors.card := by
  rw [divisorTensorScalar_eq positive fits, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt
    (divisorTensor_word_bounds positive fits).1]

theorem divisorTensorScalar_div {b n : ℕ} (positive : 0 < n) (fits : n < 2 ^ b) :
    divisorTensorScalar b n / 2 ^ (2 * b) = ArithmeticFunction.sigma 1 n := by
  rw [divisorTensorScalar_eq positive fits, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (divisorTensor_word_bounds positive fits).1, Nat.zero_add]

/-- For a product of two distinct primes the high digit gives both factors by integer square root. -/
theorem recoverFromDivisorTensor {b p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p < q) (fits : p * q < 2 ^ b) :
    recoverFromSigma (p * q) (divisorTensorScalar b (p * q) / 2 ^ (2 * b)) = (p, q) := by
  rw [divisorTensorScalar_div (Nat.mul_pos hp.pos hq.pos) fits]
  exact recoverFromSigma_correct hp hq ordered

/-- Twelve has six divisors with sum 28, giving 7174 in the four-bit-input contraction. -/
theorem divisorTensorScalar_12 : divisorTensorScalar 4 12 = 7174 := by
  rw [divisorTensorScalar_eq (by decide) (by decide), ArithmeticFunction.sigma_one_apply]
  decide +kernel

/-- Independently evaluate all 256 multiplication assignments and their local ring weights. -/
theorem divisorTensorResidue_12_direct : (divisorTensorResidue 4 12).val = 7174 := by
  rw [divisorTensorResidue_eq_wireSum]
  decide +kernel

end PrimeFactors
