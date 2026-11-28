import PrimeFactors.AllOddGuessFloor
import PrimeFactors.TwoPowerGuessShare

/-! A mean guess-rank floor for a fixed unit product at any positive modulus
under the stated size budget, including arbitrary powers of two. -/
namespace PrimeFactors.AnyModulusGuessFloor

open Finset PrimeSquareSumWeights CoprimeGuessTables GuessTableOverlap GuessModulusBudget
open scoped Classical
open private PrimeFactors.JointSumGuessFloor.sum_labels from PrimeFactors.JointSumGuessFloor

private theorem dyadic_share (k n : ℕ) (odd : Odd n) :
    Share (fun s : Labels (2^k) n => weight n s.val) ((1:ℝ)/16) := by
  apply from_uniform
  intro s
  unfold tableMass
  rw [←Nat.cast_sum,PrimeFactors.JointSumGuessFloor.sum_labels,
    total ((ZMod.isUnit_iff_coprime ..).mpr (odd.coprime_two_right.pow_right k))]
  have bound : (((2^k).totient:ℕ):ℝ)≤16*(Fintype.card (Labels (2^k) n):ℝ)*weight n s.val := by
    exact_mod_cast TwoPowerGuessShare.uniform_bound odd s
  linarith only [bound]

private theorem cap {α : Type*} [Fintype α] (w : α→ℕ) {c : ℝ} (h : Share w c) :
    Share w (min c 1) := by
  have pos : 0≤tableMass w := by unfold tableMass; positivity
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left c 1)
    (Nat.cast_nonneg (Fintype.card α))) pos).trans h

/-- At every positive modulus up to 2^2048, every ordering of the
attained sum labels has mean inclusive rank strictly above 1/1024 of a
uniformly shuffled order. The sampling distribution is uniform on ordered
residue pairs with prescribed unit product. -/
theorem rank (m n : ℕ) [NeZero m] (unit : n.Coprime m) (limit : m≤2^2048)
    (e : Fin (Fintype.card (Labels m n)) ≃ Labels m n) :
    (1:ℝ)/1024*((Fintype.card (Labels m n):ℝ)+1)/2 <
      IndependentGuessRanks.meanRank (fun s : Labels m n => (weight n s.val:ℝ)) e := by
  by_cases oddM : Odd m
  · apply lt_trans _ (AllOddGuessFloor.rank m n oddM unit limit e)
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (by norm_num : (1:ℝ)/1024<1/64)
      (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one)) (by norm_num)
  have nOdd := Nat.coprime_two_right.mp (unit.of_dvd_right (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp oddM)))
  obtain ⟨k,d,odd,rfl⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne m)
  haveI : NeZero d := ⟨odd.pos.ne'⟩
  have oddUnit := unit.of_dvd_right (dvd_mul_left d (2^k))
  have cop := odd.coprime_two_left.pow_left k
  have prodNon : 0≤∏p∈d.primeFactors,ratio p := prod_nonneg fun p _ =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have combined := crt cop n (by norm_num : (0:ℝ)≤1/16) (div_nonneg prodNon (by norm_num))
    (dyadic_share k n nOdd) (AllOddGuessFloor.share d n odd oddUnit)
  have budget : GuessRadicalBudget.radical d.primeFactors≤2^2048 :=
    ((Nat.le_of_dvd odd.pos (Nat.prod_primeFactors_dvd d)).trans
      (Nat.le_of_dvd (Nat.mul_pos (pow_pos (by decide : 0<2) k) odd.pos) (dvd_mul_left d (2^k)))).trans limit
  have lower := GuessRadicalBudget.sixteenth d.primeFactors (fun p h =>
    ⟨Nat.prime_of_mem_primeFactors h,fun eq => odd.not_two_dvd_nat (eq ▸ Nat.dvd_of_mem_primeFactors h)⟩) budget
  have pos : 0<tableMass (fun s : Labels (2^k*d) n => weight n s.val) := by
    unfold tableMass
    rw [←Nat.cast_sum,PrimeFactors.JointSumGuessFloor.sum_labels]
    haveI : Nonempty (Pairs n (2^k*d)) := ⟨⟨(1,n),one_mul _⟩⟩
    exact Nat.cast_pos.mpr Nat.card_pos
  apply lt_of_lt_of_le _ (rank_floor _ (min_le_right _ _) (cap _ combined) pos e)
  apply div_lt_div_of_pos_right _ (by norm_num)
  exact mul_lt_mul_of_pos_right (lt_min (by linarith only [lower]) (by norm_num))
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one)

end PrimeFactors.AnyModulusGuessFloor
