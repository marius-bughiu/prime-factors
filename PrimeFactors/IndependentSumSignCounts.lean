import PrimeFactors.QuarticHalfSumResidues
import PrimeFactors.ResidueCount
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Fintype.Parity

/-! Independent local sign observations on distinct modular sums over one
complete period. A sign must reverse when both local factors are negated.
The observation model assumes the sign values are supplied. -/
namespace PrimeFactors.IndependentSumSignCounts

open Finset QuarticHalfSumResidues
open scoped Classical
open private PrimeFactors.QuarticHalfSumResidues.mem_sums
  PrimeFactors.QuarticHalfSumResidues.neg_sum from PrimeFactors.QuarticHalfSumResidues

variable {k : ℕ} (m : Fin k → ℕ) [∀ i, NeZero (m i)]
  (cop : Pairwise fun i j => (m i).Coprime (m j))

private local instance : NeZero (∏ i, m i) :=
  ⟨prod_ne_zero_iff.mpr fun i _ => NeZero.ne (m i)⟩

private noncomputable def joint (A : (i : Fin k) → Finset (ZMod (m i))) :
    Finset (ZMod (∏ i, m i)) := univ.filter fun s => ∀ i, ZMod.prodEquivPi m cop s i ∈ A i

private theorem joint_card (A : (i : Fin k) → Finset (ZMod (m i))) :
    (joint m cop A).card = ∏ i, (A i).card := by
  let e := ZMod.prodEquivPi m cop
  let equiv : (joint m cop A) ≃ ((i : Fin k) → A i) :=
    (e.toEquiv.subtypeEquiv (p := fun s => s ∈ joint m cop A)
      (q := fun z => ∀ i, z i ∈ A i) (by intro s; simp only [joint, mem_filter, mem_univ, true_and]; rfl)).trans
      Equiv.subtypePiEquivPi
  simpa only [Fintype.card_coe, Fintype.card_pi] using Fintype.card_congr equiv

private theorem joint_all (N : ℤ) : joint m cop (fun i => sums (m i) N) = sums (∏ i, m i) N := by
  ext s
  simp only [joint, mem_filter, mem_univ, true_and, PrimeFactors.QuarticHalfSumResidues.mem_sums]
  let e := ZMod.prodEquivPi m cop
  change (∀ i, AdmissibleSum (N : ZMod (m i)) (e s i)) ↔ AdmissibleSum (N : ZMod _) s
  constructor
  · intro h
    choose x y hxy hsum using h
    refine ⟨e.symm x,e.symm y,e.injective ?_,e.injective ?_⟩
    · rw [map_mul, e.apply_symm_apply, e.apply_symm_apply, map_intCast]
      exact funext hxy
    · rw [map_add, e.apply_symm_apply, e.apply_symm_apply]
      exact funext hsum
  · rintro ⟨x,y,hxy,hsum⟩ i
    refine ⟨e x i,e y i,?_,?_⟩
    · simpa only [map_mul,map_intCast,Pi.mul_apply,Pi.intCast_apply] using congrFun (congrArg e hxy) i
    · simpa only [map_add,Pi.add_apply] using congrFun (congrArg e hsum) i

variable (N : ℤ) (tag : (i : Fin k) → ZMod (m i) → Bool)

/-- The local answer changes when both factors are negated. -/
def Reverses : Prop := ∀ i s, s ∈ sums (m i) N → tag i (-s) = !(tag i s)

private noncomputable def choice {a : ℕ} [NeZero a] (f : ZMod a → Bool) (b : Bool) :=
  (sums a N).filter fun s => f s = b

private theorem half_choice {a : ℕ} [NeZero a] (f : ZMod a → Bool)
    (flip : ∀ s ∈ sums a N, f (-s) = !(f s)) (b : Bool) :
    2 * (choice N f b).card = (sums a N).card := by
  have swap (c : Bool) (s : ZMod a) (h : s ∈ choice N f c) : -s ∈ choice N f (!c) := by
    obtain ⟨hs,hc⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨PrimeFactors.QuarticHalfSumResidues.neg_sum hs, by rw [flip s hs,hc]⟩
  have balanced : (choice N f true).card = (choice N f false).card := by
    exact card_nbij' Neg.neg Neg.neg (swap true) (swap false) (fun s _ => neg_neg s) (fun s _ => neg_neg s)
  have dis : Disjoint (choice N f true) (choice N f false) := by
    apply disjoint_left.mpr
    intro s ht hf
    exact Bool.noConfusion ((mem_filter.mp ht).2.symm.trans (mem_filter.mp hf).2)
  have union : choice N f true ∪ choice N f false = sums a N := by
    ext s
    cases h : f s <;> simp [choice,h]
  have total := congrArg Finset.card union
  rw [card_union_of_disjoint dis] at total
  cases b <;> omega

/-- Distinct complete-period sum labels whose local values give the supplied vector. -/
noncomputable def pattern (b : Fin k → Bool) : Finset (ZMod (∏ i, m i)) :=
  joint m cop fun i => choice N (tag i) (b i)

/-- Membership entails a genuine modular pair with the given product and sum. -/
theorem mem_pattern {b : Fin k → Bool} {s : ZMod (∏ i, m i)} :
    s ∈ pattern m cop N tag b ↔ s ∈ sums (∏ i, m i) N ∧
      ∀ i, tag i (ZMod.prodEquivPi m cop s i) = b i := by
  rw [←joint_all m cop N]
  simp only [pattern,joint,choice,mem_filter,mem_univ,true_and,forall_and]

/-- A fixed vector of k supplied signs keeps exactly one in 2^k distinct labels. -/
theorem pattern_count (flip : Reverses m N tag) (b : Fin k → Bool) :
    2^k * (pattern m cop N tag b).card = (sums (∏ i, m i) N).card := by
  rw [pattern,joint_card,←joint_all m cop N,joint_card]
  calc
    _ = ∏ i, 2 * (choice N (tag i) (b i)).card := by simp [prod_mul_distrib]
    _ = _ := prod_congr rfl fun i _ => half_choice N (tag i) (flip i) (b i)

/-- An observation can leave a set of possible sign vectors. -/
noncomputable def compatible (G : Finset (Fin k → Bool)) := G.biUnion (pattern m cop N tag)

/-- Any collection G of possible vectors retains exactly the fraction |G|/2^k. -/
theorem menu_count (flip : Reverses m N tag) (G : Finset (Fin k → Bool)) :
    2^k * (compatible m cop N tag G).card = G.card * (sums (∏ i, m i) N).card := by
  have dis : (G : Set (Fin k → Bool)).PairwiseDisjoint (pattern m cop N tag) := by
    intro u _ v _ ne
    apply disjoint_left.mpr
    intro s hu hv
    apply ne
    exact funext fun i => ((mem_pattern m cop N tag).mp hu).2 i |>.symm.trans (((mem_pattern m cop N tag).mp hv).2 i)
  rw [compatible,card_biUnion dis,mul_sum]
  simp only [pattern_count m cop N tag flip,sum_const,nsmul_eq_mul]
  rfl

/-- Comparing the least representatives of s and −s gives a reversing tag
exactly when negation fixes no attained sum. -/
def orientation {a : ℕ} [NeZero a] (s : ZMod a) : Bool := decide (s.val < (-s).val)

theorem orientation_iff : Reverses m N (fun _ s => orientation s) ↔
    ∀ i s, s ∈ sums (m i) N → s ≠ -s := by
  constructor
  · intro flip i s hs fixed
    have h := flip i s hs
    rw [←fixed] at h
    exact (show ∀ b : Bool, b ≠ !b by decide) _ h
  · intro free i s hs
    have different : s.val ≠ (-s).val := fun eq => free i s hs (ZMod.val_injective _ eq)
    rcases lt_or_gt_of_ne different with h|h
    · simp only [orientation,neg_neg,h,not_lt_of_gt h,decide_true,decide_false,Bool.not_true]
    · simp only [orientation,neg_neg,h,not_lt_of_gt h,decide_true,decide_false,Bool.not_false]

/-! At the three moduli 3, 7, 11 the fixed product 1 has 48 distinct sums.
Each of the eight supplied orientation vectors still leaves six labels. -/
namespace Control

def moduli : Fin 3 → ℕ := ![3,7,11]

private theorem facts (i : Fin 3) : (moduli i).Prime ∧ moduli i ≠ 2 := by
  fin_cases i <;> decide
instance (i : Fin 3) : NeZero (moduli i) := ⟨(facts i).1.ne_zero⟩

theorem coprime : Pairwise fun i j => (moduli i).Coprime (moduli j) := by
  unfold Pairwise
  decide +kernel

private theorem free : ∀ i x y, (x : ZMod (moduli i))*y = 1 → x+y ≠ -(x+y) := by
  intro i
  fin_cases i <;> decide +kernel

private theorem size (i : Fin 3) : (sums (moduli i) 1).card = (moduli i + 1) / 2 := by
  letI : Fact (moduli i).Prime := ⟨(facts i).1⟩
  let e : sums (moduli i) 1 ≃ {s : ZMod (moduli i) // AdmissibleSum 1 s} :=
    Equiv.subtypeEquivRight fun s => by simp only [PrimeFactors.QuarticHalfSumResidues.mem_sums,Int.cast_one]
  rw [←Fintype.card_coe,←Nat.card_eq_fintype_card,Nat.card_congr e,
    card_admissibleSum_eq _ _ one_ne_zero,card_factorSumResidues_of_square _ (facts i).2 _ one_ne_zero IsSquare.one]

theorem period : (∏ i, moduli i) = 231 := by decide +kernel

theorem size_all : (sums (∏ i, moduli i) 1).card = 48 := by
  rw [←joint_all moduli coprime 1,joint_card]
  simp_rw [size]
  decide +kernel

theorem six (b : Fin 3 → Bool) : (pattern moduli coprime 1 (fun _ s => orientation s) b).card = 6 := by
  have flip : Reverses moduli 1 (fun _ s => orientation s) := by
    apply (orientation_iff moduli 1).mpr
    intro i s hs
    obtain ⟨x,y,xy,ss⟩ := PrimeFactors.QuarticHalfSumResidues.mem_sums.mp hs
    rw [←ss]
    exact free i x y (by simpa only [Int.cast_one] using xy)
  have count := pattern_count moduli coprime 1 _ flip b
  rw [size_all] at count
  omega

/-- The sum labels with square first factor for the fixed product 1. -/
noncomputable def factorTag (i : Fin 3) (s : ZMod (moduli i)) : Bool :=
  s.val == 2 || (i == 1 && s.val == 6) || (i == 2 && (s.val == 3 || s.val == 7))

/-- Each factor has the same quadratic character and its sign is a function
of the sum for these three primes. -/
theorem factor_sign (i : Fin 3) : ∀ x y : ZMod (moduli i), x*y=1 →
    (factorTag i (x+y) = true ↔ IsSquare x) ∧ (factorTag i (x+y) = true ↔ IsSquare y) := by
  fin_cases i <;> decide +kernel

/-- Supplying the three actual quadratic characters of a factor gives exactly
six possible sum labels for every sign vector. -/
theorem six_from_factor_signs (b : Fin 3 → Bool) : (pattern moduli coprime 1 factorTag b).card = 6 := by
  have flipped (i : Fin 3) : ∀ x y : ZMod (moduli i), x*y=1 →
      factorTag i (-(x+y)) = !(factorTag i (x+y)) := by
    fin_cases i <;> decide +kernel
  have flip : Reverses moduli 1 factorTag := by
    intro i s hs
    obtain ⟨x,y,xy,ss⟩ := PrimeFactors.QuarticHalfSumResidues.mem_sums.mp hs
    rw [←ss]
    exact flipped i x y (by simpa only [Int.cast_one] using xy)
  have count := pattern_count moduli coprime 1 _ flip b
  rw [size_all] at count
  omega

end Control
end PrimeFactors.IndependentSumSignCounts
