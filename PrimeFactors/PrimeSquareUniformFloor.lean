import PrimeFactors.JointSumGuessFloor

/-! A uniform component in the distribution of every attainable sum
remainder for any fixed unit product at distinct odd prime squares. -/
namespace PrimeFactors.PrimeSquareUniformFloor

open Finset PrimeSquareSumWeights PrimeSquareExpectedRank CoprimeGuessTables
open scoped Classical
open private PrimeFactors.JointSumGuessFloor.sum_labels from PrimeFactors.JointSumGuessFloor
open private PrimeFactors.PrimeSquareExpectedRank.class_count
  PrimeFactors.PrimeSquareExpectedRank.class_formula PrimeFactors.PrimeSquareExpectedRank.pairs_formula
  PrimeFactors.PrimeSquareExpectedRank.triangular from PrimeFactors.PrimeSquareExpectedRank

/-- Numerator of the uniform component, with denominator `pairs p`.
At three, every attained sum has the same multiplicity. -/
def numerator (p : ℕ) := if p=3 then pairs p else 2*classes p

private theorem numerator_le {p : ℕ} [Fact p.Prime] (odd : p≠2) : numerator p≤pairs p := by
  unfold numerator
  split_ifs with small
  · exact le_rfl
  · have hp : (3:ℚ)≤p := by exact_mod_cast (by have := (Fact.out : p.Prime).two_le; omega : 3≤p)
    have : (2:ℚ)*classes p≤pairs p := by
      rw [PrimeFactors.PrimeSquareExpectedRank.class_formula odd,
        PrimeFactors.PrimeSquareExpectedRank.pairs_formula (p:=p)]
      linarith
    exact_mod_cast this

private theorem local_total {p n : ℕ} [Fact p.Prime] (unit : ¬p∣n) :
    (∑ s : Allowed p n,weight n s.val)=pairs p :=
  PrimeFactors.JointSumGuessFloor.sum_labels.trans (pair_count unit)

/-- Lower bound for the weight of each single attained sum, scaled by
the size of its alphabet. Nonsquare unit products have a uniform table. -/
theorem local_bound {p n : ℕ} [Fact p.Prime] (odd : p≠2) (unit : ¬p∣n) (s : Allowed p n) :
    numerator p≤Fintype.card (Allowed p n)*weight n s.val := by
  classical
  by_cases sq : IsSquare (n:ZMod p)
  · have count := PrimeFactors.PrimeSquareExpectedRank.class_count odd unit sq
    by_cases small : p=3
    · subst p
      have total := local_total unit
      have cap (t : Allowed 3 n) : weight n t.val≤3 := by
        rw [weight_formula odd n t.val]
        split_ifs <;> decide
      have same : weight n s.val=3 := by
        by_contra ne
        have strict := sum_lt_sum (s:=univ) (f:=fun t : Allowed 3 n => weight n t.val)
          (g:=fun _ => 3) (fun t _ => cap t)
          ⟨s,mem_univ _,lt_of_le_of_ne (cap s) ne⟩
        rw [total,sum_const,card_univ,count] at strict
        norm_num [classes,pairs] at strict
      rw [same,count]
      decide
    · have two : 2≤weight n s.val := by
        rw [weight_formula odd n s.val,if_pos s.property]
        split_ifs
        · exact (Fact.out : p.Prime).two_le
        · exact le_rfl
      simpa only [numerator,if_neg small,count,Nat.mul_comm 2] using Nat.mul_le_mul_left (classes p) two
  · have zero := StableDiscriminantClasses.zero_count odd unit 1
    rw [if_neg sq] at zero
    have each (t : Allowed p n) : weight n t.val=2 := by
      apply regular_weight odd n _ t.property
      intro hit
      haveI : Nonempty {s : ZMod (p^(1+1)) // s^2-4*(n:ZMod (p^(1+1)))=0} := ⟨⟨t.val,hit⟩⟩
      exact (Nat.card_pos.ne' zero)
    have total := local_total unit
    simp only [each,sum_const,card_univ,nsmul_eq_mul] at total
    rw [each]
    exact (numerator_le odd).trans total.ge

variable {ι : Type*} [Fintype ι] (p : ι→ℕ) [∀ i,Fact (p i).Prime]

/-- Every individual label retains at least the product of the uniform
components even when its weight is correlated with an arbitrary loss. -/
theorem label_bound (distinct : Function.Injective p) (n : ℕ) (odd : ∀ i,p i≠2)
    (unit : ∀ i,¬p i∣n) (s : Labels (modulus p) n) :
    (∏ i,numerator (p i)) ≤ Fintype.card (Labels (modulus p) n)*weight n s.val := by
  let e := allowedEquiv p distinct n
  rw [Fintype.card_congr e,Fintype.card_pi,weight_equiv p distinct n s,←prod_mul_distrib]
  exact prod_le_prod' (fun i _ => local_bound (odd i) (unit i) (e s i))

/-- In finite integer arithmetic, every nonnegative loss on sum labels
has at least this much of its uniformly weighted cost. -/
theorem loss_bound (distinct : Function.Injective p) (n : ℕ) (odd : ∀ i,p i≠2)
    (unit : ∀ i,¬p i∣n) (cost : Labels (modulus p) n → ℕ) :
    (∏ i,numerator (p i))*(∑ s,cost s) ≤
      Fintype.card (Labels (modulus p) n)*∑ s,weight n s.val*cost s := by
  simp only [mul_sum]
  apply sum_le_sum
  intro s _
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (cost s) (label_bound p distinct n odd unit s)

/-- Actual mean one-based guess count divided by the random-order mean
is at least the product of the local uniform components, for every order. -/
theorem rank_floor (distinct : Function.Injective p) (n : ℕ) (odd : ∀ i,p i≠2)
    (unit : ∀ i,¬p i∣n) (e : Fin (Fintype.card (Labels (modulus p) n)) ≃ Labels (modulus p) n) :
    (∏ i, (numerator (p i):ℝ)/pairs (p i))*((Fintype.card (Labels (modulus p) n):ℝ)+1)/2 ≤
      IndependentGuessRanks.meanRank (fun s : Labels (modulus p) n => (weight n s.val:ℝ)) e := by
  let A := Fintype.card (Labels (modulus p) n)
  let T := ∏ i, pairs (p i)
  let U := ∏ i, numerator (p i)
  have pos : 0<(T:ℝ) := by
    exact_mod_cast (prod_pos (fun i _ => Nat.mul_pos (Fact.out : (p i).Prime).pos
      (Nat.sub_pos_of_lt (Fact.out : (p i).Prime).one_lt)) : 0<T)
  have total : IndependentGuessRanks.total (fun s : Labels (modulus p) n => (weight n s.val:ℝ))=T := by
    unfold IndependentGuessRanks.total
    rw [←Nat.cast_sum]
    apply congrArg (fun t : ℕ => (t:ℝ))
    rw [PrimeFactors.JointSumGuessFloor.sum_labels,JointSumGuessFloor.total_pairs p distinct n unit]
    simp only [T,pairs,prod_mul_distrib,JointSumGuessFloor.cap,JointSumGuessFloor.spread]
  have flat := PrimeFactors.PrimeSquareExpectedRank.triangular A
  have lo : U*(A*(A+1))≤A*(2*∑ i, (i.val+1)*weight n (e i).val) := by
    rw [←flat,mul_sum,mul_sum, mul_sum]
    apply sum_le_sum
    intro i _
    simpa only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using
      Nat.mul_le_mul_right (2*(i.val+1)) (label_bound p distinct n odd unit (e i))
  have short : U*(A+1)≤2*∑ i,(i.val+1)*weight n (e i).val := by
    apply Nat.le_of_mul_le_mul_left (c:=A) _ Fintype.card_pos
    simpa only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using lo
  rw [prod_div_distrib,←Nat.cast_prod,←Nat.cast_prod,IndependentGuessRanks.meanRank,total]
  change (U:ℝ)/T*((A:ℝ)+1)/2≤_/(T:ℝ)
  rw [div_mul_eq_mul_div,div_right_comm]
  apply div_le_div_of_nonneg_right _ pos.le
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  rw [mul_comm _ (2:ℝ)]
  exact_mod_cast short

end PrimeFactors.PrimeSquareUniformFloor
