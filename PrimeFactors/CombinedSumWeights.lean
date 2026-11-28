import PrimeFactors.PrimeSquareExpectedRank
import PrimeFactors.FactorSumCRT
import Mathlib.Algebra.Order.Rearrangement

/-! Guessing the sum residue of a uniformly sampled ordered pair with a fixed
product residue. CRT multiplies the local multiplicities. The finite example
uses product one modulo 25 and 49. -/

namespace PrimeFactors.CombinedSumWeights

open PrimeSquareSumWeights

private theorem weight_first {m : ℕ} (n : ℕ) (s : ZMod m) :
    weight n s = Nat.card {x : ZMod m // x * (s - x) = n} := by
  apply Nat.card_congr
  refine {
    toFun := fun v => ⟨v.val.val.1, ?_⟩
    invFun := fun x => ⟨⟨(x.val, s - x.val), x.property⟩, ?_⟩
    left_inv := ?_
    right_inv := fun _ => rfl }
  · have eq : s-v.val.val.1 = v.val.val.2 := sub_eq_iff_eq_add.mpr (v.property.symm.trans (add_comm _ _))
    simpa only [eq] using v.val.property
  · simp [sumOf]
  · intro v
    apply Subtype.ext ∘ Subtype.ext
    refine Prod.ext rfl ?_
    change s - v.val.val.1 = v.val.val.2
    exact sub_eq_iff_eq_add.mpr (v.property.symm.trans (add_comm _ _))

/-- For any fixed natural product, each global ordered pair with a specified
sum is uniquely a choice of one such pair at each coprime modulus. -/
theorem weight_crt {a b : ℕ} (cop : a.Coprime b) (n : ℕ) (s : ZMod (a*b)) :
    weight n s = weight n ((ZMod.chineseRemainder cop s).1) *
      weight n ((ZMod.chineseRemainder cop s).2) := by
  let e := ZMod.chineseRemainder cop
  rw [weight_first, weight_first, weight_first, ←Nat.card_prod]
  apply Nat.card_congr
  refine Equiv.trans ?_ Equiv.subtypeProdEquivProd
  apply e.toEquiv.subtypeEquiv
  intro u
  change u*(s-u) = n ↔ (e u).1*((e s).1-(e u).1) = n ∧
    (e u).2*((e s).2-(e u).2) = n
  calc
    _ ↔ e (u*(s-u)) = e n := e.injective.eq_iff.symm
    _ ↔ _ := by simp only [map_mul, map_sub, map_natCast, Prod.ext_iff,
      Prod.fst_mul, Prod.snd_mul, Prod.fst_sub, Prod.snd_sub, Prod.fst_natCast, Prod.snd_natCast]

private noncomputable def heavy25 : List (ZMod 25) := [2,23]
private noncomputable def light25 : List (ZMod 25) := [0,5,10,15,20]
private noncomputable def heavy49 : List (ZMod 49) := [2,47]
private noncomputable def light49 : List (ZMod 49) := [1,6,8,13,15,20,22,27,29,34,36,41,43,48]

private noncomputable def countAt {m : ℕ} [NeZero m] (s : ZMod m) :=
  (Finset.univ.filter (fun x : ZMod m => x*(s-x)=1)).card

private theorem one_weight {m : ℕ} [NeZero m] (s : ZMod m) :
    weight 1 s = countAt s := by
  rw [weight_first, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [countAt]

private noncomputable def localWeight {α : Type*} [DecidableEq α] (p : ℕ) (high low : List α) (x : α) :=
  if x ∈ high then p else if x ∈ low then 2 else 0

private theorem table25 : ∀ s : ZMod 25, countAt s = localWeight 5 heavy25 light25 s := by
  decide +kernel

private theorem table49 : ∀ s : ZMod 49, countAt s = localWeight 7 heavy49 light49 s := by
  decide +kernel

abbrev Coordinates := ZMod 25 × ZMod 49

/-- The guess order, in CRT coordinates. Ties are broken by the local lists. -/
noncomputable def order : List Coordinates :=
  heavy25.product heavy49 ++ light25.product heavy49 ++
  heavy25.product light49 ++ light25.product light49

noncomputable def localProduct (v : Coordinates) :=
  localWeight 5 heavy25 light25 v.1 * localWeight 7 heavy49 light49 v.2

/-- Translate a guess to the corresponding residue modulo 1,225. -/
noncomputable def residue : Coordinates ≃+* ZMod (25*49) :=
  (ZMod.chineseRemainder (by decide : Nat.Coprime 25 49)).symm

theorem weight_residue (v : Coordinates) : weight 1 (residue v) = localProduct v := by
  rw [weight_crt (by decide : Nat.Coprime 25 49), ← RingEquiv.symm_symm residue]
  simp only [residue, RingEquiv.symm_symm, RingEquiv.apply_symm_apply, one_weight, table25, table49]
  rfl

/-- Exactly the positive-weight sum residues occur, each once. -/
theorem order_support : order.Nodup ∧ ∀ v : Coordinates, v ∈ order ↔
    0 < weight 1 (residue v) := by
  constructor
  · decide +kernel
  · rintro ⟨x,y⟩
    rw [weight_residue]
    simp only [order, List.mem_append, List.mem_product, localProduct]
    unfold localWeight
    split_ifs <;> simp_all

/-- All four weight blocks, in the order in which their sum residues are guessed. -/
theorem weight_blocks : order.map (fun v => weight 1 (residue v)) =
    List.replicate 4 35 ++ List.replicate 10 14 ++ List.replicate 28 10 ++
      List.replicate 70 4 := by
  simp only [weight_residue]
  decide +kernel

/-- Total number of equally likely ordered local pairs for the combined modulus. -/
theorem pair_count : Nat.card (Pairs 1 (25*49)) = 840 := by
  rw [total (by norm_num)]
  decide +kernel

/-- Sum of the one-based ranks, weighted by the number of pairs at each rank. -/
noncomputable def rankMass (weights : List ℕ) : ℕ :=
  ((weights.zipIdx 1).map fun (w, rank) => w*rank).sum

theorem expected_rank :
    (rankMass (order.map (fun v => weight 1 (residue v))) : ℚ) /
      Nat.card (Pairs 1 (25*49)) = 112/3 := by
  rw [weight_blocks, pair_count]
  rw [show rankMass (List.replicate 4 35 ++ List.replicate 10 14 ++
    List.replicate 28 10 ++ List.replicate 70 4) = 31360 by decide +kernel]
  norm_num

/-- Any reassignment of the 112 guess ranks has weighted cost at least 31,360. -/
theorem optimal_order (assign : Equiv.Perm (Fin 112)) :
    31360 ≤ ∑ i : Fin 112, weight 1 (residue order[i.val]) * ((assign i).val+1) := by
  let w (i : Fin 112) := if i.val < 4 then 35 else if i.val < 14 then 14
      else if i.val < 42 then 10 else 4
  have block : ∀ i : Fin 112, localProduct order[i.val] = w i := by decide +kernel
  have sorted : Antitone w := by
    intro i j h
    have le : i.val ≤ j.val := h
    unfold w
    split_ifs <;> omega
  have rank : Monotone (fun i : Fin 112 => i.val+1) := fun _ _ h => Nat.add_le_add_right h _
  have min := (sorted.antivary rank).sum_mul_le_sum_mul_comp_perm (σ := assign)
  simp only [weight_residue, block]
  calc
    31360 = ∑ i : Fin 112, w i*(i.val+1) := by decide +kernel
    _ ≤ _ := min

open scoped Classical in
/-- Averaging over all orders gives one-based rank 113/2 for each of the 112
labels, and hence for any distribution on them. -/
theorem uniform_rank {α : Type*} [Fintype α] {A : ℕ} (size : A = 112) (x : α) :
    2*(∑ r : α ≃ Fin A, ((r x).val+1)) =
      Fintype.card (α ≃ Fin A)*113 := by
  have h := PrimeSquareExpectedRank.uniform_order (A := A) x
  rwa [show A+1=113 by omega] at h

/-- Fraction saved against uniform random ordering of all admissible sums. -/
theorem relative_saving :
    order.length = 112 ∧ 1 - (112/3 : ℚ)/(113/2) = 115/339 ∧
      ∀ {p : ℕ} [Fact p.Prime], p ≠ 2 → PrimeSquareExpectedRank.saving p < 115/339 := by
  refine ⟨by decide, by norm_num, ?_⟩
  intro p _ odd
  exact lt_of_le_of_lt (PrimeSquareExpectedRank.sharp_saving odd).1 (by norm_num)

/-- A chosen semiprime exhibits one of the four classes of weight 35. -/
theorem worked_product :
    Nat.Prime 1049 ∧ Nat.Prime 1399 ∧ 1049*1399=1467551 ∧ 1467551%1225=1 ∧
    (1049+1399)%1225=1223 ∧ weight 1 (1223 : ZMod (25*49))=35 := by
  refine ⟨by norm_num, by norm_num, rfl, rfl, rfl, ?_⟩
  rw [one_weight]
  decide +kernel

end PrimeFactors.CombinedSumWeights
