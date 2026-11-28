import PrimeFactors.PrimePowerUniformShare

/-! Absolute lower bounds, relative to the number of attained labels, under
a combined modulus budget allowing any depths of at least two digits. -/
namespace PrimeFactors.DeepBudgetedSumGuesses

open Finset PrimePowerUniformShare CoprimeGuessTables PrimeSquareSumWeights
open scoped Classical
open private PrimeFactors.BudgetedSumGuesses.coeff from PrimeFactors.BudgetedSumGuesses
open private PrimeFactors.PrimeSquareExpectedRank.triangular from PrimeFactors.PrimeSquareExpectedRank
open private PrimeFactors.JointSumGuessFloor.sum_labels from PrimeFactors.JointSumGuessFloor

variable (S : Finset ℕ) [∀ i:S, Fact i.val.Prime] (E : ℕ→ℕ)

private theorem square_budget (deep : ∀ i:S,2≤E i.val) (limit : period S E≤2^2048) :
    modulus (fun i:S => i.val)≤2^2048 :=
  (prod_le_prod' (s:=univ) (fun i _ => Nat.pow_le_pow_right (Fact.out : i.val.Prime).pos (deep i))).trans limit

/-- Every label retains more than 1.89535325% of its uniform probability
at a unit product, regardless of the depths ≥2. -/
theorem per_label (n : ℕ) (odd : ∀ i:S,i.val≠2) (unit : ∀ i:S,¬i.val∣n)
    (deep : ∀ i:S,2≤E i.val) (limit : period S E≤2^2048) (s : Labels (period S E) n) :
    (7581413:ℝ)/400000000*Nat.card (Pairs n (period S E)) <
      (Fintype.card (Labels (period S E) n):ℝ)*weight n s.val := by
  have sq := PrimeFactors.BudgetedSumGuesses.coeff (fun i:S => i.val) Subtype.val_injective odd
    (square_budget S E deep limit)
  haveI : Nonempty (Pairs n (period S E)) := ⟨⟨(1,n),one_mul _⟩⟩
  have pos : (0:ℝ)<Nat.card (Pairs n (period S E)) := Nat.cast_pos.mpr Nat.card_pos
  apply lt_of_lt_of_le _ (label_bound S E n odd unit deep s)
  apply mul_lt_mul_of_pos_right _ pos
  linarith only [sq]

private theorem rank_from_labels {α : Type*} [Fintype α] [Nonempty α] (w : α→ℝ)
    (e : Fin (Fintype.card α) ≃ α) {T c : ℝ} (mass : IndependentGuessRanks.total w=T)
    (tp : 0<T) (each : ∀ s,c*T≤(Fintype.card α:ℝ)*w s) :
    c*((Fintype.card α:ℝ)+1)/2 ≤ IndependentGuessRanks.meanRank w e := by
  let A := Fintype.card α
  have ap : (0:ℝ)<A := by dsimp [A]; exact_mod_cast (Fintype.card_pos : 0<Fintype.card α)
  have flat : (∑ i : Fin A,2*((i.val:ℝ)+1))=(A:ℝ)*(A+1) := by
    exact_mod_cast PrimeFactors.PrimeSquareExpectedRank.triangular A
  rw [←mul_sum] at flat
  have row (i : Fin A) : c*T/(A:ℝ)≤w (e i) :=
    (div_le_iff₀ ap).mpr (by simpa only [mul_comm (w _)] using each (e i))
  have bound := sum_le_sum (s:=univ) (fun (i : Fin A) _ =>
    mul_le_mul_of_nonneg_left (row i) (by positivity : 0≤(i.val:ℝ)+1))
  rw [←sum_mul] at bound
  rw [IndependentGuessRanks.meanRank,mass,le_div_iff₀ tp]
  apply le_trans _ bound
  have sumVal : (∑ i : Fin A, ((i.val:ℝ)+1))=(A:ℝ)*(A+1)/2 := by linarith only [flat]
  rw [sumVal]
  change c*((A:ℝ)+1)/2*T≤_
  apply le_of_eq
  field_simp
  ring

/-- Mean inclusive rank for any order is at least 1.89535325% of the
uniform random-order mean on the same support. -/
theorem rank (n : ℕ) (odd : ∀ i:S,i.val≠2) (unit : ∀ i:S,¬i.val∣n)
    (deep : ∀ i:S,2≤E i.val) (limit : period S E≤2^2048)
    (e : Fin (Fintype.card (Labels (period S E) n)) ≃ Labels (period S E) n) :
    (7581413:ℝ)/400000000*((Fintype.card (Labels (period S E) n):ℝ)+1)/2 ≤
      IndependentGuessRanks.meanRank (fun s : Labels (period S E) n => (weight n s.val:ℝ)) e := by
  haveI : Nonempty (Pairs n (period S E)) := ⟨⟨(1,n),one_mul _⟩⟩
  apply rank_from_labels _ e (T:=(Nat.card (Pairs n (period S E)):ℝ)) _
    (Nat.cast_pos.mpr Nat.card_pos) (fun s => (per_label S E n odd unit deep limit s).le)
  unfold IndependentGuessRanks.total
  rw [←Nat.cast_sum,PrimeFactors.JointSumGuessFloor.sum_labels]

/-- Covering 99.9% of the ordered residue pairs requires strictly more
than 94.72% of the attained sum labels. -/
theorem near_complete (n : ℕ) (odd : ∀ i:S,i.val≠2) (unit : ∀ i:S,¬i.val∣n)
    (deep : ∀ i:S,2≤E i.val) (limit : period S E≤2^2048) (L : Finset (Labels (period S E) n))
    (miss : 1000*(∑ s∈Lᶜ,weight n s.val)≤Nat.card (Pairs n (period S E))) :
    9472*Fintype.card (Labels (period S E) n)<10000*L.card := by
  let A := Fintype.card (Labels (period S E) n)
  let T := Nat.card (Pairs n (period S E))
  haveI : Nonempty (Pairs n (period S E)) := ⟨⟨(1,n),one_mul _⟩⟩
  have pos : (0:ℝ)<T := Nat.cast_pos.mpr Nat.card_pos
  have c := sum_le_sum (s:=Lᶜ) (fun s _ => (per_label S E n odd unit deep limit s).le)
  simp only [sum_const,nsmul_eq_mul,←mul_sum] at c
  have m : 1000*(∑ s∈Lᶜ,(weight n s.val:ℝ))≤(T:ℝ) := by exact_mod_cast miss
  have bound : ((7581413:ℝ)/400000000)*(Lᶜ.card:ℕ)*1000*(T:ℝ) ≤ (A:ℝ)*T := by
    have x := mul_le_mul_of_nonneg_right c (by norm_num : (0:ℝ)≤1000)
    have y := mul_le_mul_of_nonneg_left m (Nat.cast_nonneg A)
    change (Lᶜ.card:ℝ)*((7581413:ℝ)/400000000*T)*1000≤(A:ℝ)*_*1000 at x
    nlinarith only [x,y]
  have b := le_of_mul_le_mul_right bound pos
  have allPos : 0<(A:ℝ) := by exact_mod_cast (Fintype.card_pos : 0<A)
  have split : (Lᶜ.card:ℝ)+L.card=A := by exact_mod_cast card_compl_add_card L
  have result : (9472:ℝ)*A<10000*L.card := by linarith only [b,split,allPos]
  exact_mod_cast result

end PrimeFactors.DeepBudgetedSumGuesses
