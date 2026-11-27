import PrimeFactors.JacobiSquareClassPopulation
import PrimeFactors.SuccessorSquareScale

/-! Number of full-width prime pairs whose predecessor or successor product is a
small integer times a square. Distinctness supplies two divisor witnesses for
each sorted pair and ensures a strict product bound at the upper endpoint. -/
open private PrimeFactors.JacobiSquareClassPopulation.values
  PrimeFactors.JacobiSquareClassPopulation.values_card
  PrimeFactors.JacobiSquareClassPopulation.cover from PrimeFactors.JacobiSquareClassPopulation

namespace PrimeFactors.OppositeSquareScalePopulation

open Finset MixedPrefixSample SquareAnchorCoverage
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
attribute [local irreducible] X eligible primes ordered

/-- Eligible pairs for which a positive successor scale through L gives the true sum. -/
noncomputable def successor (L : ℕ) : Finset (ℕ × ℕ) := by
  classical exact eligible.filter fun z => ∃ t : ℕ, 0 < t ∧ t ≤ L ∧
    SuccessorSquareScale.sum (z.1*z.2) t = z.1+z.2

/-- Every strictly ordered pair gives two different divisor witnesses, by reversal. -/
theorem sorted_capacity (pairs : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (valid : ∀ z ∈ pairs, 1 < z.1 ∧ z.1 < z.2 ∧ predProduct z < 2^2048 ∧ predProduct z ∈ V) :
    2*pairs.card ≤ V.card*2^240 := by
  classical
  have dis : Disjoint pairs (pairs.image Prod.swap) := by
    apply disjoint_left.mpr
    intro z hz hr
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hr
    exact Nat.lt_asymm (valid w hw).2.1 (valid w.swap hz).2.1
  have both := count_with_values (pairs ∪ pairs.image Prod.swap) V (by
    intro z hz
    rcases mem_union.mp hz with h | h
    · obtain ⟨p,lt,cap,mem⟩ := valid z h
      exact ⟨p,p.trans lt,cap,mem⟩
    · obtain ⟨w,hw,rfl⟩ := mem_image.mp h
      obtain ⟨p,lt,cap,mem⟩ := valid w hw
      have swapped : predProduct w.swap = predProduct w := Nat.mul_comm ..
      exact ⟨p.trans lt,p,swapped.trans_lt cap,swapped ▸ mem⟩)
  simpa only [card_union_of_disjoint dis, card_image_of_injective _ Prod.swap_injective,
    two_mul] using both

private theorem bounds {p q : ℕ} (ok : (p,q) ∈ eligible) :
    1 < p ∧ p < q ∧ q < 2*p ∧ q < 2^1024 := by
  rw [eligible,sample,mem_filter] at ok
  obtain ⟨pm,qm,_,_,_⟩ := mem_ordered.mp ok.1
  rw [primes,mem_filter,mem_Ico] at pm qm
  have lower : X ≤ p := pm.1.1
  have upper : q < 2*X := qm.1.2
  have boundary : 2*X = 2^1024 := by unfold X; decide +kernel
  exact ⟨pm.2.one_lt,ok.2,by omega,by omega⟩

/-- For the upper sign the larger shifted prime is allowed to attain H, but the
strictly smaller shifted prime is below H. Their product is strictly below H². -/
private theorem cap {a b : ℕ} (lt : a < b) (le : b ≤ 2^1024) : a*b < 2^2048 := by
  rw [show (2:ℕ)^2048 = 2^1024*2^1024 by decide +kernel]
  exact Nat.mul_lt_mul_of_lt_of_le (lt.trans_le le) le (by positivity)

private abbrev vals := PrimeFactors.JacobiSquareClassPopulation.values

private theorem mem_vals {F H L t y : ℕ} (tp : 0<t) (budget : t≤L) (fp : 0<F)
    (square : t*y^2=F) (bounded : F≤H^2) : F∈vals H L := by
  have yp : 0<y := by
    by_contra! zero
    rw [Nat.eq_zero_of_le_zero zero] at square
    simp at square
    omega
  have root := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le tp).mpr
    (show y^2*t ≤ H^2 by simpa only [Nat.mul_comm (y^2),square] using bounded))
  have idx := Nat.sub_add_cancel tp
  apply mem_biUnion.mpr
  refine ⟨t-1,mem_range.mpr (by omega),mem_image.mpr ⟨y,?_,?_⟩⟩
  · rw [mem_Icc,idx]; exact ⟨yp,root⟩
  · rw [idx,square]

private def shift : (ℕ × ℕ) ↪ (ℕ × ℕ) where
  toFun z := (z.1+2,z.2+2)
  inj' := by
    intro x y h
    have p : x.1+2=y.1+2 := congrArg Prod.fst h
    have q : x.2+2=y.2+2 := congrArg Prod.snd h
    exact Prod.ext (by omega) (by omega)

private theorem capacities (L : ℕ) :
    2*(JacobiSquareClassPopulation.direct L).card ≤ (vals (2^1024) L).card*2^240 ∧
    2*(successor L).card ≤ (vals (2^1024) L).card*2^240 := by
  classical
  constructor
  · apply sorted_capacity
    rintro ⟨p,q⟩ hz
    obtain ⟨ok,mem⟩ := mem_filter.mp (PrimeFactors.JacobiSquareClassPopulation.cover L hz)
    obtain ⟨hp,lt,_,qu⟩ := bounds ok
    exact ⟨hp,lt,cap (by change p-1<q-1; omega) (by omega),mem⟩
  · rw [←card_map (f:=shift)]
    apply sorted_capacity
    intro z hz
    obtain ⟨⟨p,q⟩,inside,rfl⟩ := mem_map.mp hz
    obtain ⟨ok,t,tp,budget,hit⟩ := mem_filter.mp inside
    obtain ⟨hp,lt,bal,qu⟩ := bounds ok
    obtain ⟨y,eq⟩ := (SuccessorSquareScale.sum_iff hp lt bal tp).mp hit
    have small := cap (Nat.add_lt_add_right lt 1) (show q+1≤2^1024 by omega)
    have ub : (p+1)*(q+1) ≤ (2^1024)^2 := small.le.trans_eq (by decide +kernel)
    change 1<p+2 ∧ p+2<q+2 ∧ (p+2-1)*(q+2-1)<2^2048 ∧ (p+2-1)*(q+2-1)∈_
    simpa only [Nat.add_sub_cancel_right] using
      (show 1 < p+2 ∧ p+2 < q+2 ∧ (p+1)*(q+1) < 2^2048 ∧ (p+1)*(q+1)∈_ from
        ⟨by omega,by omega,small,mem_vals tp budget (Nat.mul_pos (Nat.succ_pos p) (Nat.succ_pos q)) eq ub⟩)

private theorem values_bound : (vals (2^1024) (2^40)).card ≤ (2^1024)*(2*(2^20)) := by
  have root : Real.sqrt (((2^40 : ℕ):ℝ)) = (2^20:ℕ) := by
    rw [show (2^40:ℕ) = (2^20)^2 by decide +kernel, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)]
  have h := PrimeFactors.JacobiSquareClassPopulation.values_card (2^1024) (2^40)
  rw [root] at h
  exact_mod_cast h

/-- For each sign, scales up to 2^40 reach fewer than one in 2^737 sorted,
distinct 1024-bit prime pairs having a 2048-bit product. -/
theorem separate_fractions :
    2^737*(JacobiSquareClassPopulation.direct (2^40)).card < eligible.card ∧
    2^737*(successor (2^40)).card < eligible.card := by
  have bound (m : ℕ) (h : 2*m ≤ (vals (2^1024) (2^40)).card*2^240) :
      2^737*m < eligible.card := by
    have num : 21000000*(2^736*((2^1024)*(2*(2^20))*2^240)) < 2^2046 := by decide +kernel
    apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
    rw [show (2:ℕ)^737=2^736*2 by decide +kernel, Nat.mul_assoc (2^736)]
    exact ((Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left (2^736)
      (h.trans (Nat.mul_le_mul_right _ values_bound)))).trans_lt num).trans ChebyshevPrimeSample.eligible_count
  exact ⟨bound _ (capacities _).1,bound _ (capacities _).2⟩

/-- The union bound allows both signs and any choice of scales through 2^40. -/
theorem either_fraction :
    2^736*((JacobiSquareClassPopulation.direct (2^40)) ∪ successor (2^40)).card < eligible.card := by
  have unionCount := Nat.mul_le_mul_left (2^737)
    (card_union_le (JacobiSquareClassPopulation.direct (2^40)) (successor (2^40)))
  rw [Nat.mul_add] at unionCount
  have both := unionCount.trans_lt (Nat.add_lt_add separate_fractions.1 separate_fractions.2)
  rw [show (2:ℕ)^737=2*2^736 by decide +kernel,Nat.mul_assoc] at both
  omega

/-- The upper shift applies to exactly one of the two prime factors. -/
def mixedProduct (upperFirst : Bool) (z : ℕ × ℕ) : ℕ :=
  if upperFirst then (z.1+1)*(z.2-1) else (z.1-1)*(z.2+1)

noncomputable def mixed (upperFirst : Bool) (L : ℕ) : Finset (ℕ × ℕ) := by
  classical exact eligible.filter fun z => ∃ t y : ℕ, 0<t ∧ t≤L ∧ t*y^2=mixedProduct upperFirst z

private def mixedShift (first : Bool) : (ℕ × ℕ) ↪ (ℕ × ℕ) where
  toFun z := (z.1+(if first then 2 else 0),z.2+(if first then 0 else 2))
  inj' := by
    intro x y h
    exact Prod.ext (Nat.add_right_cancel (congrArg Prod.fst h)) (Nat.add_right_cancel (congrArg Prod.snd h))

/-- With mixed signs, shifted factors may coincide, so this bound counts one
divisor per pair. It also covers the diagonal that arises from twin primes. -/
private theorem mixed_capacity (first : Bool) (L : ℕ) :
    (mixed first L).card ≤ (vals (2^1024) L).card*2^240 := by
  classical
  rw [←card_map (f:=mixedShift first)]
  apply count_with_values
  intro z hz
  obtain ⟨⟨p,q⟩,inside,rfl⟩ := mem_map.mp hz
  obtain ⟨ok,t,y,tp,budget,eq⟩ := mem_filter.mp inside
  obtain ⟨hp,lt,_,qu⟩ := bounds ok
  have pbig : 1 < (mixedShift first (p,q)).1 := by
    change 1 < p+_
    omega
  have qbig : 1 < (mixedShift first (p,q)).2 := by
    change 1 < q+_
    omega
  have repr : predProduct (mixedShift first (p,q)) = mixedProduct first (p,q) := by
    cases first <;> rfl
  have positive : 0 < predProduct (mixedShift first (p,q)) :=
    Nat.mul_pos (Nat.sub_pos_of_lt pbig) (Nat.sub_pos_of_lt qbig)
  have ub {a b : ℕ} (ap : a<2^1024) (bq : b≤2^1024) : a*b < 2^2048 := by
    rw [show (2:ℕ)^2048=2^1024*2^1024 by decide +kernel]
    exact Nat.mul_lt_mul_of_lt_of_le ap bq (by positivity)
  have small : mixedProduct first (p,q)<2^2048 := by
    cases first
    · exact ub (by change p-1<2^1024; omega) (by omega)
    · exact ub (by change p+1<2^1024; omega) (by omega)
  refine ⟨pbig,qbig,repr.trans_lt small,?_⟩
  rw [repr]
  exact mem_vals tp budget (repr ▸ positive) eq (small.le.trans_eq (by decide +kernel))

/-- All four shifted products receive the full scale budget. The two mixed
signs may have a common shifted factor at a twin pair; no disjointness is used. -/
theorem four_fraction :
    2^735*(((JacobiSquareClassPopulation.direct (2^40) ∪ successor (2^40))
      ∪ mixed false (2^40)) ∪ mixed true (2^40)).card < eligible.card := by
  let V := (vals (2^1024) (2^40)).card*2^240
  let A := JacobiSquareClassPopulation.direct (2^40)
  let B := successor (2^40)
  let C := mixed false (2^40)
  let D := mixed true (2^40)
  obtain ⟨a,b⟩ := capacities (2^40)
  have ab : (A∪B).card ≤ V := by
    have n := card_union_le A B
    change 2*A.card ≤ V at a
    change 2*B.card ≤ V at b
    omega
  have c : C.card ≤ V := mixed_capacity ..
  have d : D.card ≤ V := mixed_capacity ..
  have all : (((A∪B)∪C)∪D).card ≤ 3*V := by
    have u := card_union_le (A∪B) C
    have v := card_union_le ((A∪B)∪C) D
    omega
  have ceiling : V ≤ ((2^1024)*(2*(2^20)))*2^240 := Nat.mul_le_mul_right _ values_bound
  have num : 21000000*(2^735*(3*(((2^1024)*(2*(2^20)))*2^240))) < 2^2046 := by decide +kernel
  exact Nat.lt_of_mul_lt_mul_left <| (Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left (2^735)
    (all.trans (Nat.mul_le_mul_left 3 ceiling)))).trans_lt (num.trans ChebyshevPrimeSample.eligible_count)

end PrimeFactors.OppositeSquareScalePopulation
