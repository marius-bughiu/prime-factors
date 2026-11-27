import PrimeFactors.OppositeSquareScalePopulation
import PrimeFactors.SquareScalePairCover
import PrimeFactors.SquareScaleHarmonicBound

/-! Frequency of four simultaneous square-scale searches among sorted pairs
of 1024-bit primes with a 2048-bit product. Each sign choice receives the full
scale budget, and the four events may overlap. -/

open private PrimeFactors.OppositeSquareScalePopulation.bounds
  from PrimeFactors.OppositeSquareScalePopulation

namespace PrimeFactors.FourNeighborScaleFrequency

open Finset MixedPrefixSample
set_option exponentiation.threshold 4096
set_option maxRecDepth 16384
attribute [local irreducible] X eligible primes ordered

/-- Select either neighbor of a prime. -/
def neighbor (upper : Bool) (p : ℕ) := if upper then p+1 else p-1

/-- Eligible pairs for which the selected product is t times a square for
at least one positive scale t at most L. -/
noncomputable def event (upperP upperQ : Bool) (L : ℕ) : Finset (ℕ × ℕ) := by
  classical exact eligible.filter fun z => ∃ t y : ℕ, 0<t ∧ t≤L ∧
    neighbor upperP z.1 * neighbor upperQ z.2 = t*y^2

private theorem neighbor_bounds {p : ℕ} (sign : Bool) (hp : 1<p) (small : p<2^1024) :
    0<neighbor sign p ∧ neighbor sign p≤2^1024 := by
  cases sign <;> simp only [neighbor,Bool.false_eq_true,if_false,if_true] <;> omega

private theorem mem_event {upperP upperQ : Bool} {L : ℕ} {p q : ℕ} :
    (p,q) ∈ event upperP upperQ L ↔ (p,q) ∈ eligible ∧ ∃ t y : ℕ,
      0<t ∧ t≤L ∧ neighbor upperP p*neighbor upperQ q=t*y^2 := by
  classical
  exact mem_filter

attribute [local irreducible] event

/-- Extend the predecessor on [1,H] to a permutation by sending zero to H.
This makes the coordinate map globally injective, including outside the sample. -/
private def shiftOne (H : ℕ) (upper : Bool) (p : ℕ) :=
  if upper then p+1 else if p=0 then H else if p≤H then p-1 else p

private theorem shiftOne_inj (H : ℕ) (upper : Bool) : Function.Injective (shiftOne H upper) := by
  intro p q same
  unfold shiftOne at same
  split_ifs at same <;> omega

private theorem shiftOne_eq {p H : ℕ} (upper : Bool) (hp : 1<p) (small : p<H) :
    shiftOne H upper p=neighbor upper p := by
  simp [shiftOne,neighbor,show p≠0 by omega,small.le]

private def shift (H : ℕ) (upperP upperQ : Bool) : (ℕ × ℕ) ↪ (ℕ × ℕ) where
  toFun z := (shiftOne H upperP z.1,shiftOne H upperQ z.2)
  inj' := fun _ _ h => Prod.ext (shiftOne_inj H upperP (congrArg Prod.fst h))
    (shiftOne_inj H upperQ (congrArg Prod.snd h))

private theorem shifted_witness {upperP upperQ : Bool} {L : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ (event upperP upperQ L).map (shift (2^1024) upperP upperQ)) :
    0 < z.1 ∧ z.1 ≤ 2^1024 ∧ 0 < z.2 ∧ z.2 ≤ 2^1024 ∧
    ∃ t y : ℕ, 0<t ∧ t≤L ∧ z.1*z.2=t*y^2 := by
  obtain ⟨⟨p,q⟩,hs,rfl⟩ := mem_map.mp hz
  obtain ⟨ok,witness⟩ := mem_event.mp hs
  obtain ⟨hp,ord,_,top⟩ := PrimeFactors.OppositeSquareScalePopulation.bounds ok
  have left := neighbor_bounds upperP hp (ord.trans top)
  have right := neighbor_bounds upperQ (hp.trans ord) top
  simp only [shift,Function.Embedding.coeFn_mk,shiftOne_eq upperP hp (ord.trans top),
    shiftOne_eq upperQ (hp.trans ord) top]
  exact ⟨left.1,left.2,right.1,right.2,witness⟩

private theorem signed_count (upperP upperQ : Bool) (L : ℕ) :
    ((event upperP upperQ L).card : ℝ) ≤ SquareScaleHarmonicBound.weight (2^1024) L := by
  have count := SquareScalePairCover.finite_count
    ((event upperP upperQ L).map (shift (2^1024) upperP upperQ)) (fun _ hz => shifted_witness hz)
  rwa [card_map] at count

/-- The four searches, each allowed every positive scale through L. -/
noncomputable def allSigns (L : ℕ) : Finset (ℕ × ℕ) :=
  ((event false false L ∪ event true true L) ∪ event false true L) ∪ event true false L

/-- Integer numerator bound for the selected sign at cutoff 2^(2b). -/
def numerator (b : ℕ) := 2*2^1024*2^b*1025*(2*b+1)

private theorem fraction_of_count (b e m : ℕ)
    (count : (m : ℝ) ≤ SquareScaleHarmonicBound.weight (2^1024) (2^(2*b)))
    (margin : 21000000*(2^e*numerator b) < 2^2046) : 2^e*m < eligible.card := by
  have bounded : m ≤ numerator b := by
    unfold numerator
    have ceiling := count.trans (SquareScaleHarmonicBound.dyadic_width 1024 b)
    rw [show ((1024 : ℕ) : ℝ)+1 = 1025 by norm_num] at ceiling
    exact_mod_cast ceiling
  exact Nat.lt_of_mul_lt_mul_left <| (Nat.mul_le_mul_left 21000000
    (Nat.mul_le_mul_left (2^e) bounded)).trans_lt (margin.trans ChebyshevPrimeSample.eligible_count)

/-- A single arithmetic comparison gives a bound for each sign at any
even-exponent power-of-two cutoff. -/
theorem dyadic_per_sign (upperP upperQ : Bool) (b e : ℕ)
    (margin : 21000000*(2^e*numerator b) < 2^2046) :
    2^e*(event upperP upperQ (2^(2*b))).card < eligible.card :=
  fraction_of_count b e _ (signed_count upperP upperQ _) margin

/-- Four sign choices cost two bits in the uniform bound for any cutoff. -/
theorem dyadic_four (b e : ℕ) (margin : 21000000*(2^(e+2)*numerator b) < 2^2046) :
    2^e*(allSigns (2^(2*b))).card < eligible.card := by
  let L := 2^(2*b)
  let A := event false false L
  let B := event true true L
  let C := event false true L
  let D := event true false L
  have total : (((A∪B)∪C)∪D).card ≤ A.card+B.card+C.card+D.card := by
    have ab := card_union_le A B
    have abc := card_union_le (A∪B) C
    have abcd := card_union_le ((A∪B)∪C) D
    omega
  have each (s t : Bool) := dyadic_per_sign s t b (e+2) margin
  have sum := (Nat.mul_le_mul_left (2^(e+2)) total).trans_lt <| calc
    _ = 2^(e+2)*A.card+2^(e+2)*B.card+2^(e+2)*C.card+2^(e+2)*D.card := by simp only [Nat.mul_add]
    _ < eligible.card+eligible.card+eligible.card+eligible.card :=
      Nat.add_lt_add (Nat.add_lt_add (Nat.add_lt_add (each ..) (each ..)) (each ..)) (each ..)
  rw [show (2:ℕ)^(e+2)=4*2^e by rw [pow_add,Nat.mul_comm]; rfl,Nat.mul_assoc] at sum
  change 2^e*(((A∪B)∪C)∪D).card < eligible.card
  omega

private theorem at_cutoff (b e m : ℕ) (width : 2*b=m)
    (margin : 21000000*(2^(e+2)*numerator b) < 2^2046) :
    2^e*(allSigns (2^m)).card < eligible.card := by
  subst m
  exact dyadic_four b e margin

attribute [local irreducible] allSigns

/-- At cutoff 2^40 each sign succeeds for fewer than one in 2^961 eligible pairs. -/
theorem per_sign (upperP upperQ : Bool) :
    2^961*(event upperP upperQ (2^40)).card < eligible.card :=
  dyadic_per_sign upperP upperQ 20 961 (by decide +kernel)

/-- All four signs at cutoff 2^40. -/
theorem four_fraction : 2^959*(allSigns (2^40)).card < eligible.card :=
  at_cutoff 20 959 40 (by decide) (by decide +kernel)

/-- Even at cutoff 2^1024 the four signs cover fewer than one in 2^462 pairs. -/
theorem full_factor_width : 2^462*(allSigns (2^1024)).card < eligible.card :=
  at_cutoff 512 462 1024 (by decide) (by decide +kernel)

/-- At cutoff 2^1792 the four signs cover fewer than one in 2^77 pairs. -/
theorem near_product_width : 2^77*(allSigns (2^1792)).card < eligible.card :=
  at_cutoff 896 77 1792 (by decide) (by decide +kernel)

end PrimeFactors.FourNeighborScaleFrequency
