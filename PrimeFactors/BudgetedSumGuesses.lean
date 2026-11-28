import PrimeFactors.GuessModulusBudget

/-! Consequences of bounding the combined prime-square modulus. The rank
and coverage costs refer to a uniformly drawn ordered pair of remainders. -/
namespace PrimeFactors.BudgetedSumGuesses

open Finset CoprimeGuessTables PrimeSquareSumWeights PrimeSquareExpectedRank
open PrimeSquareUniformFloor GuessModulusBudget
open scoped Classical

variable {ι : Type*} [Fintype ι] (p : ι→ℕ) [∀ i,Fact (p i).Prime]

private theorem coeff (distinct : Function.Injective p) (odd : ∀ i,p i≠2) (limit : modulus p≤2^2048) :
    (7581413:ℝ)/100000000<∏ i, (numerator (p i):ℝ)/pairs (p i) := by
  let S := univ.image p
  have cert := GuessModulusBudget.minimum S (by
    intro q h
    obtain ⟨i,_,rfl⟩ := mem_image.mp h
    exact ⟨Fact.out,odd i⟩) (by
      unfold GuessModulusBudget.budget S
      rwa [prod_image (fun i _ j _ eq => distinct eq)])
  have step := GuessModulusBudget.minimum_value.1.trans_le cert
  simpa only [S,prod_image (fun i _ j _ eq => distinct eq),ratio] using step

/-- With combined modulus at most 2^2048, no ordering can reduce the
inclusive mean below 7.581413% of the uniform-random-order mean. -/
theorem rank (distinct : Function.Injective p) (n : ℕ) (odd : ∀ i,p i≠2)
    (unit : ∀ i,¬p i∣n) (limit : modulus p≤2^2048)
    (e : Fin (Fintype.card (Labels (modulus p) n)) ≃ Labels (modulus p) n) :
    (7581413:ℝ)/100000000*((Fintype.card (Labels (modulus p) n):ℝ)+1)/2 <
      IndependentGuessRanks.meanRank (fun s : Labels (modulus p) n => (weight n s.val:ℝ)) e := by
  exact (div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (coeff p distinct odd limit) (by positivity))
    (by norm_num : (0:ℝ)<2)).trans_le (rank_floor p distinct n odd unit e)

/-- A set of omitted labels retains a fixed share of its uniform mass.
This covers an arbitrary list, including lists chosen using the fixed
product and modulus. -/
theorem omitted (distinct : Function.Injective p) (n : ℕ) (odd : ∀ i,p i≠2)
    (unit : ∀ i,¬p i∣n) (limit : modulus p≤2^2048) (D : Finset (Labels (modulus p) n)) :
    ((7581413:ℝ)/100000000)*D.card*Nat.card (Pairs n (modulus p)) ≤
      (Fintype.card (Labels (modulus p) n):ℝ)*∑ s∈D,(weight n s.val:ℝ) := by
  let U := ∏ i,numerator (p i)
  let T := Nat.card (Pairs n (modulus p))
  have total : T=∏ i,pairs (p i) := by
    unfold T
    rw [JointSumGuessFloor.total_pairs p distinct n unit]
    simp only [JointSumGuessFloor.cap,JointSumGuessFloor.spread,pairs,prod_mul_distrib]
  have pos : 0<(T:ℝ) := by
    rw [total]
    exact_mod_cast (prod_pos (fun i _ => Nat.mul_pos (Fact.out : (p i).Prime).pos
      (Nat.sub_pos_of_lt (Fact.out : (p i).Prime).one_lt)) : 0<∏ i,pairs (p i))
  have lo := coeff p distinct odd limit
  rw [prod_div_distrib,←Nat.cast_prod,←Nat.cast_prod,←total] at lo
  have low : (7581413:ℝ)/100000000*T < U := (lt_div_iff₀ pos).mp lo
  have cap := sum_le_sum (s:=D) (fun s _ => label_bound p distinct n odd unit s)
  simp only [sum_const,nsmul_eq_mul,←mul_sum] at cap
  have realCap : (D.card:ℝ)*U ≤ (Fintype.card (Labels (modulus p) n):ℝ)*∑ s∈D,(weight n s.val:ℝ) := by
    exact_mod_cast cap
  change (7581413:ℝ)/100000000*D.card*T ≤ _
  calc
    _ = (D.card:ℝ)*((7581413:ℝ)/100000000*T) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left low.le (Nat.cast_nonneg _)).trans realCap

/-- A list covering at least 99.9% of all modular factor pairs must
contain more than 98.68% of the attained sum labels. -/
theorem near_complete (distinct : Function.Injective p) (n : ℕ) (odd : ∀ i,p i≠2)
    (unit : ∀ i,¬p i∣n) (limit : modulus p≤2^2048) (L : Finset (Labels (modulus p) n))
    (miss : 1000*(∑ s∈Lᶜ,weight n s.val) ≤ Nat.card (Pairs n (modulus p))) :
    9868*Fintype.card (Labels (modulus p) n) < 10000*L.card := by
  let A := Fintype.card (Labels (modulus p) n)
  let T := Nat.card (Pairs n (modulus p))
  have pos : 0<(T:ℝ) := by
    haveI : Nonempty (Pairs n (modulus p)) := ⟨⟨(1,n),one_mul _⟩⟩
    exact_mod_cast Nat.card_pos
  have m : 1000*(∑ s∈Lᶜ,(weight n s.val:ℝ)) ≤ (T:ℝ) := by exact_mod_cast miss
  have cap := omitted p distinct n odd unit limit Lᶜ
  have bound : ((7581413:ℝ)/100000000)*(Lᶜ.card:ℕ)*1000*(T:ℝ) ≤ (A:ℝ)*T := by
    have x := mul_le_mul_of_nonneg_right cap (by norm_num : (0:ℝ)≤1000)
    have y := mul_le_mul_of_nonneg_left m (Nat.cast_nonneg A)
    change _ ≤ (A:ℝ)*_ * 1000 at x
    nlinarith only [x,y]
  have b := le_of_mul_le_mul_right bound pos
  have allPos : 0<(A:ℝ) := by exact_mod_cast (Fintype.card_pos : 0<A)
  have split : (Lᶜ.card:ℝ)+L.card=A := by exact_mod_cast card_compl_add_card L
  have final : (9868:ℝ)*A<10000*L.card := by linarith only [b,split,allPos]
  exact_mod_cast final

end PrimeFactors.BudgetedSumGuesses
