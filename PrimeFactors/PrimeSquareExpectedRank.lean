import PrimeFactors.PrimeSquareSumWeights
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Perm

/-! Expected rank in a list of distinct sum residues, conditional on a fixed
square unit product modulo an odd prime square. Each ordered local factor
pair has equal probability. -/

namespace PrimeFactors.PrimeSquareExpectedRank

open PrimeSquareSumWeights
open scoped Classical

def classes (p : ℕ) := (p-3)/2*p+2
def pairs (p : ℕ) := p*(p-1)
abbrev Allowed (p n : ℕ) := {s : ZMod (p^2) // AdmissibleSum (n : ZMod (p^2)) s}
abbrev Order (p n : ℕ) := Allowed p n ≃ Fin (classes p)

/-- Unnormalized expected number of guesses, including the successful guess. -/
noncomputable def score {p n : ℕ} [NeZero p] (r : Order p n) :=
  ∑ s : Allowed p n, weight n s.val * ((r s).val+1)

noncomputable def baseline (p : ℕ) : ℚ := (classes p + 1 : ℚ)/2
noncomputable def optimum (p : ℕ) : ℚ :=
  ((classes p : ℚ)*(classes p+1) + 3*(p-2 : ℚ))/pairs p
noncomputable def saving (p : ℕ) : ℚ := 1-optimum p/baseline p

/-- For every target class, the uniform mean over all orders is (A+1)/2:
reversing the ranks pairs complementary guess numbers. -/
theorem uniform_order {α : Type*} [Fintype α] {A : ℕ} (x : α) :
    2*(∑ r : α ≃ Fin A, ((r x).val+1)) = Fintype.card (α ≃ Fin A)*(A+1) := by
  classical
  let rev := (Equiv.refl α).equivCongr (@Fin.revPerm A)
  have pair (r : α ≃ Fin A) : ((r x).val+1) + (((rev r) x).val+1) = A+1 := by
    change ((r x).val+1) + ((r x).rev.val+1) = A+1
    rw [Fin.val_rev]
    have := (r x).isLt
    omega
  have h := Finset.sum_congr (rfl : (Finset.univ : Finset (α ≃ Fin A)) = Finset.univ) (fun r _ => pair r)
  rw [Finset.sum_add_distrib,rev.sum_comp (fun r => (r x).val+1)] at h
  simpa [two_mul] using h

private theorem triangular (a : ℕ) : (∑ i : Fin a, 2*(i.val+1))=a*(a+1) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc,Fin.val_last,ih]
    ring

private theorem class_count {p n : ℕ} [Fact p.Prime] (odd : p≠2) (unit : ¬p∣n)
    (sq : IsSquare (n : ZMod p)) : Fintype.card (Allowed p n)=classes p := by
  have nz : firstPrimeDigit p 1 (n : ZMod (p^2)) ≠ 0 := by
    rw [map_natCast]
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd n p).mp.mt unit
  simpa only [Nat.card_eq_fintype_card,map_natCast,sq,decide_true,primePowerSumCount,
    collidingDigitCount,primePowerSquareCount,pow_one,mul_one,ite_true,classes]
    using card_primePower_admissibleSum odd 1 (n : ZMod (p^2)) nz

private theorem two_labels {p n : ℕ} [Fact p.Prime] (odd : p≠2) (unit : ¬p∣n)
    (sq : IsSquare (n : ZMod p)) :
    ∃ a b : Allowed p n, a≠b ∧ a.val^2-4*(n : ZMod (p^2))=0 ∧
      b.val^2-4*(n : ZMod (p^2))=0 ∧ ∀ s : Allowed p n,
      weight n s.val = 2+(if s=a then p-2 else 0)+(if s=b then p-2 else 0) := by
  classical
  let D := Finset.univ.filter (fun s : ZMod (p^2) => s^2-4*(n : ZMod (p^2))=0)
  have size : D.card=2 := by
    simpa only [D,Nat.card_eq_fintype_card,Fintype.card_subtype,sq,if_true]
      using StableDiscriminantClasses.zero_count odd unit 1
  obtain ⟨a,b,ne,ab⟩ := Finset.card_eq_two.mp size
  have spec (s : ZMod (p^2)) : s^2-4*(n : ZMod (p^2))=0 ↔ s=a ∨ s=b := by
    have h : s ∈ D ↔ s^2-4*(n : ZMod (p^2))=0 := by simp [D]
    rw [←h,ab]
    simp
  have two := (ZMod.isUnit_iff_coprime 2 (p^2)).mpr
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two Fact.out).mpr odd.symm))
  have allowed (s : ZMod (p^2)) (h : s^2-4*(n : ZMod (p^2))=0) :
      AdmissibleSum (n : ZMod (p^2)) s := by
    apply (admissibleSum_iff_isSquare_of_two_unit two _ _).mpr
    rw [h]
    exact ⟨0,by simp⟩
  have za := (spec a).mpr (Or.inl rfl)
  have zb := (spec b).mpr (Or.inr rfl)
  let aa : Allowed p n := ⟨a,allowed a za⟩
  let bb : Allowed p n := ⟨b,allowed b zb⟩
  have abne : aa≠bb := fun h => ne (congrArg Subtype.val h)
  refine ⟨aa,bb,abne,za,zb,fun s => ?_⟩
  have lo := (Fact.out : p.Prime).two_le
  by_cases x : s=aa
  · subst s
    rw [zero_weight odd n za,if_pos rfl,if_neg abne]
    omega
  by_cases y : s=bb
  · subst s
    rw [zero_weight odd n zb,if_neg abne.symm,if_pos rfl]
    omega
  have nz : s.val^2-4*(n : ZMod (p^2))≠0 := fun h =>
    ((spec s.val).mp h).elim (fun e => x (Subtype.ext e)) (fun e => y (Subtype.ext e))
  simp [regular_weight odd n nz s.property,x,y]

private theorem score_eq {p n : ℕ} [NeZero p] (r : Order p n) (a b : Allowed p n)
    (weights : ∀ s : Allowed p n,
      weight n s.val=2+(if s=a then p-2 else 0)+(if s=b then p-2 else 0)) :
    score r = classes p*(classes p+1)+(p-2)*(((r a).val+1)+((r b).val+1)) := by
  classical
  unfold score
  simp_rw [weights,add_mul,ite_mul,zero_mul,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [r.sum_comp (fun i => 2*(i.val+1)),triangular]
  ring

private theorem first_two {α : Type*} {A : ℕ} (r : α ≃ Fin A) (lo : 2≤A) {a b : α} (ne : a≠b) :
    ∃ t : α ≃ Fin A, (t a).val=0 ∧ (t b).val=1 := by
  classical
  let z : Fin A := ⟨0,by omega⟩
  let o : Fin A := ⟨1,by omega⟩
  let t := r.trans (Equiv.swap (r a) z)
  have first : t a=z := by simp [t]
  have no : z ≠ t b := by rw [←first]; exact t.injective.ne ne
  have zo : z≠o := by simp [z,o]
  refine ⟨t.trans (Equiv.swap (t b) o),?_,?_⟩
  · simp [first,Equiv.swap_apply_of_ne_of_ne no zo,z]
  · simp [o]

/-- This exact minimum is attained by putting the two singular classes first.
The universal bound applies to every enumeration of every admissible class. -/
theorem optimal_order {p n : ℕ} [Fact p.Prime] (odd : p≠2) (unit : ¬p∣n)
    (sq : IsSquare (n : ZMod p)) :
    (∀ r : Order p n, classes p*(classes p+1)+3*(p-2) ≤ score r) ∧
      ∃ r : Order p n, score r = classes p*(classes p+1)+3*(p-2) := by
  classical
  obtain ⟨a,b,ne,_,_,w⟩ := two_labels odd unit sq
  constructor
  · intro r
    have diff : (r a).val ≠ (r b).val := fun h => ne (r.injective (Fin.ext h))
    rw [score_eq r a b w,mul_comm 3]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  · let r : Order p n := Fintype.equivFinOfCardEq (class_count odd unit sq)
    obtain ⟨t,first,second⟩ := first_two r (by unfold classes; omega) ne
    exact ⟨t,by rw [score_eq t a b w,first,second]; ring⟩

/-- Exactly the orders placing the two zero-discriminant classes at the first
two positions attain the minimum. Ranks in this condition start at zero. -/
theorem optimal_positions {p n : ℕ} [Fact p.Prime] (odd : p≠2) (unit : ¬p∣n)
    (sq : IsSquare (n : ZMod p)) :
    ∃ a b : Allowed p n, a≠b ∧ a.val^2-4*(n : ZMod (p^2))=0 ∧
      b.val^2-4*(n : ZMod (p^2))=0 ∧ ∀ r : Order p n,
        score r=classes p*(classes p+1)+3*(p-2) ↔ (r a).val+(r b).val=1 := by
  classical
  obtain ⟨a,b,ne,za,zb,w⟩ := two_labels odd unit sq
  refine ⟨a,b,ne,za,zb,fun r => ?_⟩
  rw [score_eq r a b w,Nat.add_left_cancel_iff,mul_comm 3]
  have lo := (Fact.out : p.Prime).two_le
  have pos : 0<p-2 := by omega
  constructor
  · intro h
    have := Nat.eq_of_mul_eq_mul_left pos h
    omega
  · intro h
    congr 1
    omega

/-- The denominator is the number of equally likely ordered local pairs. -/
theorem pair_count {p n : ℕ} [Fact p.Prime] (unit : ¬p∣n) :
    Nat.card (Pairs n (p^2))=pairs p := by
  have prime := (Fact.out : p.Prime)
  have cop := (prime.coprime_iff_not_dvd.mpr unit).symm
  rw [total ((ZMod.isUnit_iff_coprime _ _).mpr (cop.pow_right 2)),
    Nat.totient_prime_pow_succ prime 1,pow_one,pairs]

/-- Normalized by the cardinality of the local sample space, the formula
`optimum` is the least possible mean number of guesses. -/
theorem normalized_optimum {p n : ℕ} [Fact p.Prime] (odd : p≠2) (unit : ¬p∣n)
    (sq : IsSquare (n : ZMod p)) :
    IsLeast (Set.range (fun r : Order p n => (score r : ℚ)/Nat.card (Pairs n (p^2))))
      (optimum p) := by
  have prime := (Fact.out : p.Prime)
  have lower := prime.two_le
  have formula : optimum p = ((classes p*(classes p+1)+3*(p-2) : ℕ):ℚ)/pairs p := by
    simp [optimum,Nat.cast_sub lower]
  rw [pair_count unit,formula]
  obtain ⟨bound,⟨r,eq⟩⟩ := optimal_order odd unit sq
  constructor
  · exact ⟨r,by dsimp only; rw [eq]⟩
  · rintro _ ⟨t,rfl⟩
    exact div_le_div_of_nonneg_right (by exact_mod_cast bound t) (by positivity)

private theorem class_formula {p : ℕ} [Fact p.Prime] (odd : p≠2) :
    (classes p : ℚ)=((p : ℚ)^2-3*p+4)/2 := by
  have prime := (Fact.out : p.Prime)
  obtain ⟨k,hk⟩ := prime.odd_of_ne_two odd
  have lower := prime.two_le
  have h : 2*((p-3)/2)+3=p := by omega
  have q : (2 : ℚ)*((p-3)/2 : ℕ)+3=p := by exact_mod_cast h
  unfold classes
  push_cast
  linear_combination ((p : ℚ)/2)*q

private theorem pairs_formula {p : ℕ} [Fact p.Prime] : (pairs p : ℚ)=p*(p-1 : ℚ) := by
  unfold pairs
  rw [Nat.cast_mul,Nat.cast_sub (Fact.out : p.Prime).one_le,Nat.cast_one]

/-- Relative reduction from uniformly random guessing without replacement. -/
theorem saving_formula {p : ℕ} [Fact p.Prime] (odd : p≠2) :
    saving p = 2*(p-2 : ℚ)*(classes p-2)/((classes p+1 : ℚ)*pairs p) := by
  have pp : (1 : ℚ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have pc : (0 : ℚ)<classes p+1 := by positivity
  have pw : (0 : ℚ)<pairs p := by rw [pairs_formula]; exact mul_pos (by linarith) (by linarith)
  unfold saving optimum baseline
  field_simp [pc.ne',pw.ne']
  rw [class_formula odd,pairs_formula]
  ring

/-- The maximum occurs at seven, with strict inequality at all other odd primes. -/
theorem sharp_saving {p : ℕ} [Fact p.Prime] (odd : p≠2) :
    saving p ≤ 10/51 ∧ (saving p=10/51 ↔ p=7) := by
  have prime := (Fact.out : p.Prime)
  by_cases large : 7<p
  · have h : (7 : ℚ)<p := by exact_mod_cast large
    have pc : (0 : ℚ)<classes p+1 := by positivity
    have pw : (0 : ℚ)<pairs p := by rw [pairs_formula]; exact mul_pos (by linarith) (by linarith)
    have lt : saving p<10/51 := by
      rw [saving_formula odd]
      apply (div_lt_div_iff₀ (mul_pos pc pw) (by norm_num)).mpr
      rw [class_formula odd,pairs_formula]
      have h7 : (0 : ℚ)<p-7 := by linarith
      have hp : (0 : ℚ)<p := by linarith
      have g : (0 : ℚ)<p*(p-7 : ℚ)*(10*((p:ℚ)-7)^2+68*(p-7 : ℚ)+82) := by positivity
      linarith only [show (2 : ℚ)*(10*((((p:ℚ)^2-3*p+4)/2+1)*(p*(p-1)))-
        2*(p-2 : ℚ)*(((p:ℚ)^2-3*p+4)/2-2)*51)>0 by linear_combination g]
    exact ⟨lt.le,by constructor <;> intro h' <;> first | exact (lt.ne h').elim | omega⟩
  · obtain ⟨k,hk⟩ := prime.odd_of_ne_two odd
    have hp := prime.two_le
    have cases : p=3 ∨ p=5 ∨ p=7 := by omega
    rcases cases with rfl | rfl | rfl <;> norm_num [saving,optimum,baseline,classes,pairs]

theorem control_five : saving 5=3/16 := by norm_num [saving,optimum,baseline,classes,pairs]
theorem control_seven : baseline 7=17/2 ∧ optimum 7=41/6 ∧ saving 7=10/51 := by
  norm_num [saving,optimum,baseline,classes,pairs]

end PrimeFactors.PrimeSquareExpectedRank
