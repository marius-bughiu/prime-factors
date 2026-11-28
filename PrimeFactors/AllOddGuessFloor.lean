import PrimeFactors.DeepBudgetedSumGuesses
import PrimeFactors.FirstPowerGuessOverlap
import PrimeFactors.GuessRadicalBudget

/-! An inclusive mean-rank floor for all positive odd moduli, obtained
by adjoining the primes of exponent one to the higher-power table. -/
namespace PrimeFactors.AllOddGuessFloor

open Finset PrimeSquareSumWeights CoprimeGuessTables GuessTableOverlap GuessModulusBudget
open scoped Classical
open private PrimeFactors.JointSumGuessFloor.sum_labels from PrimeFactors.JointSumGuessFloor
open private PrimeFactors.PrimeSquareUniformFloor.numerator_le from PrimeFactors.PrimeSquareUniformFloor

private structure Certified (m n : ℕ) (c : ℝ) : Prop where
  bound : ∀ [NeZero m], Share (fun s : Labels m n => weight n s.val) c

private theorem ratio_nonneg (p : ℕ) : 0≤ratio p := by unfold ratio; positivity

private theorem attach_first (S : Finset ℕ) {m n : ℕ} {c : ℝ} (positive : 0<m) (cn : 0≤c)
    (base : Certified m n c)
    (good : ∀ p∈S,p.Prime ∧ p≠2 ∧ ¬p∣n ∧ p.Coprime m) :
    Certified ((∏p∈S,p)*m) n ((∏p∈S,ratio p)*c) := by
  induction S using Finset.induction_on with
  | empty => simpa only [prod_empty,one_mul] using base
  | @insert p S miss ih =>
    obtain ⟨hp,odd,unit,cop⟩ := good p (mem_insert_self ..)
    have rest := fun q (h : q∈S) => good q (mem_insert_of_mem h)
    have copS : p.Coprime (∏q∈S,q) := Nat.Coprime.prod_right fun q h =>
      (Nat.coprime_primes hp (rest q h).1).mpr (fun eq => miss (eq ▸ h))
    have nz : 0<(∏q∈S,q)*m := Nat.mul_pos (prod_pos (fun q h => (rest q h).1.pos)) positive
    haveI : NeZero ((∏q∈S,q)*m) := ⟨nz.ne'⟩
    haveI : Fact p.Prime := ⟨hp⟩
    rw [prod_insert miss,prod_insert miss,Nat.mul_assoc,mul_assoc]
    constructor
    intro _
    exact crt (copS.mul_right cop) n (ratio_nonneg p)
      (mul_nonneg (prod_nonneg (fun q _ => ratio_nonneg q)) cn)
      (FirstPowerGuessOverlap.share odd unit) (ih rest).bound

private theorem all_powers (S : Finset ℕ) (E : ℕ→ℕ) (n : ℕ)
    (good : ∀ p∈S,p.Prime ∧ p≠2 ∧ ¬p∣n ∧ 0<E p) :
    Certified (∏p∈S,p^(E p)) n ((∏p∈S,ratio p)/4) := by
  let F := S.filter (fun p => E p=1)
  let D := S.filter (fun p => E p≠1)
  have Dgood (i:D) := good i.val (mem_filter.mp i.property).1
  haveI : ∀ i:D, Fact i.val.Prime := fun i => ⟨(Dgood i).1⟩
  have depths (i:D) : 2≤E i.val := by
    have lo := (Dgood i).2.2.2
    have ne := (mem_filter.mp i.property).2
    omega
  let Q := PrimePowerUniformShare.period D E
  have Qeq : Q=∏p∈D,p^(E p) := prod_coe_sort D (fun p => p^E p)
  have Qpos : 0<Q := Nat.pos_of_ne_zero (NeZero.ne (PrimePowerUniformShare.period D E))
  have supported : Certified Q n ((∏p∈D,ratio p)/4) := by
    constructor
    intro _
    apply from_uniform
    intro s
    unfold tableMass
    rw [←Nat.cast_sum,PrimeFactors.JointSumGuessFloor.sum_labels]
    have h := PrimePowerUniformShare.label_bound D E n (fun i => (Dgood i).2.1)
      (fun i => (Dgood i).2.2.1) depths s
    simpa only [ratio,prod_coe_sort D (fun p => (PrimeSquareUniformFloor.numerator p:ℝ)/PrimeSquareExpectedRank.pairs p)] using h
  have first (p : ℕ) (h : p∈F) : p.Prime ∧ p≠2 ∧ ¬p∣n ∧ p.Coprime Q := by
    obtain ⟨inS,one⟩ := mem_filter.mp h
    obtain ⟨pp,odd,unit,_⟩ := good p inS
    refine ⟨pp,odd,unit,?_⟩
    rw [Qeq]
    apply Nat.Coprime.prod_right
    intro q hq
    have qgood := good q (mem_filter.mp hq).1
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_primes pp qgood.1).mpr (fun eq => (mem_filter.mp hq).2 (eq ▸ one))
  have step := attach_first F Qpos (div_nonneg (prod_nonneg (fun p _ => ratio_nonneg p)) (by norm_num))
    supported first
  have power_eq : (∏p∈F,p)*Q=∏p∈S,p^(E p) := by
    have f : (∏p∈F,p)=(∏p∈F,p^(E p)) := prod_congr rfl fun p h => by rw [(mem_filter.mp h).2,pow_one]
    rw [f,Qeq]
    exact prod_filter_mul_prod_filter_not S (fun p => E p=1) _
  have coeff_eq : (∏p∈F,ratio p)*((∏p∈D,ratio p)/4)=(∏p∈S,ratio p)/4 := by
    rw [←mul_div_assoc,prod_filter_mul_prod_filter_not S (fun p => E p=1) ratio]
  rwa [power_eq,coeff_eq] at step

/-- A radical-dependent lower bound on the pairwise overlap of the
actual table for a fixed unit product at an arbitrary positive odd modulus. -/
theorem share (m n : ℕ) [NeZero m] (odd : Odd m) (unit : n.Coprime m) :
    Share (fun s : Labels m n => weight n s.val) ((∏p∈m.primeFactors,ratio p)/4) := by
  have step := all_powers m.primeFactors m.factorization n (by
    intro p h
    have pp := Nat.prime_of_mem_primeFactors h
    have d := Nat.dvd_of_mem_primeFactors h
    exact ⟨pp,fun eq => odd.not_two_dvd_nat (eq ▸ d),
      pp.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_right d unit).symm,
      pp.factorization_pos_of_dvd (NeZero.ne m) d⟩)
  have factorization : (∏p∈m.primeFactors,p^m.factorization p)=m := Nat.factorization_prod_pow_eq_self (NeZero.ne m)
  rw [factorization] at step
  exact step.bound

/-- No ordering of the attained sum labels can have mean inclusive
rank as small as 1/64 of a uniformly shuffled order under this budget.
The distribution samples ordered remainder pairs with fixed unit product. -/
theorem rank (m n : ℕ) [NeZero m] (odd : Odd m) (unit : n.Coprime m) (limit : m≤2^2048)
    (e : Fin (Fintype.card (Labels m n)) ≃ Labels m n) :
    (1:ℝ)/64*((Fintype.card (Labels m n):ℝ)+1)/2 <
      IndependentGuessRanks.meanRank (fun s : Labels m n => (weight n s.val:ℝ)) e := by
  have members (p : ℕ) (h : p∈m.primeFactors) : p.Prime ∧ p≠2 :=
    ⟨Nat.prime_of_mem_primeFactors h,fun eq => odd.not_two_dvd_nat (eq ▸ Nat.dvd_of_mem_primeFactors h)⟩
  have budget : GuessRadicalBudget.radical m.primeFactors≤2^2048 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m)) (Nat.prod_primeFactors_dvd m)).trans limit
  have lower := GuessRadicalBudget.sixteenth m.primeFactors members budget
  have upper : (∏p∈m.primeFactors,ratio p)≤1 := by
    apply prod_le_one (fun p _ => ratio_nonneg p)
    intro p h
    haveI : Fact p.Prime := ⟨(members p h).1⟩
    have pos : (0:ℝ)<PrimeSquareExpectedRank.pairs p := by
      exact_mod_cast Nat.mul_pos (members p h).1.pos (Nat.sub_pos_of_lt (members p h).1.one_lt)
    exact (div_le_one pos).mpr (by exact_mod_cast PrimeFactors.PrimeSquareUniformFloor.numerator_le (members p h).2)
  have pos : 0<tableMass (fun s : Labels m n => weight n s.val) := by
    unfold tableMass
    rw [←Nat.cast_sum,PrimeFactors.JointSumGuessFloor.sum_labels]
    haveI : Nonempty (Pairs n m) := ⟨⟨(1,n),one_mul _⟩⟩
    exact Nat.cast_pos.mpr Nat.card_pos
  apply lt_of_lt_of_le _ (rank_floor _ (by linarith only [upper]) (share m n odd unit) pos e)
  apply div_lt_div_of_pos_right _ (by norm_num)
  exact mul_lt_mul_of_pos_right (by linarith only [lower]) (by positivity)

end PrimeFactors.AllOddGuessFloor
