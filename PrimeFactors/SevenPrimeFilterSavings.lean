import PrimeFactors.IndependentFilterOrdering
import PrimeFactors.IntervalWheelResidues
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Pi.Units

/-! Full-period scalar lookup savings for the seven odd primes from 3 through
19. The sample space for sign frequencies is the unit residues of the wheel. -/
namespace PrimeFactors.SevenPrimeFilterSavings
open Finset IndependentFilterOrdering

def prime : Fin 7 → ℕ := ![3,5,7,11,13,17,19]

private theorem prime_facts : ∀ i : Fin 7, (prime i).Prime ∧ prime i ≠ 2 := by decide +kernel
instance (i : Fin 7) : NeZero (prime i) := ⟨(prime_facts i).1.ne_zero⟩
private theorem coprime : Pairwise fun i j => (prime i).Coprime (prime j) := by
  unfold Pairwise
  decide +kernel

noncomputable def wheel : ℕ := ∏ i, prime i

theorem wheel_size : wheel = 4849845 := by decide +kernel

noncomputable def isSquareAt (i : Fin 7) (x : ZMod (prime i)) : Bool :=
  decide (∃ a : ZMod (prime i), a*a=x)

def localCount (i : Fin 7) (square : Bool) : ℕ :=
  if square then (prime i+1)/2 else (prime i-1)/2

noncomputable def rate (i : Fin 7) (square : Bool) : ℚ := (localCount i square:ℚ)/prime i

theorem true_rate (n : ℕ) (cop : wheel.Coprime n) (i : Fin 7) :
    (LocalSumMenu.count n (prime i):ℚ)/prime i = rate i (isSquareAt i n) := by
  letI : Fact (prime i).Prime := ⟨(prime_facts i).1⟩
  have div : prime i ∣ wheel := dvd_prod_of_mem prime (mem_univ i)
  have unit := (prime_facts i).1.coprime_iff_not_dvd.mp (cop.of_dvd_left div)
  have nz := (ZMod.natCast_zmod_eq_zero_iff_dvd n (prime i)).mp.mt unit
  unfold rate localCount isSquareAt
  rw [LocalSumMenu.count,card_admissibleSum_eq (prime i) _ nz]
  by_cases h : ∃ a : ZMod (prime i), a*a=n
  · obtain ⟨a,ha⟩ := h
    rw [if_pos (by simpa using (show ∃ a : ZMod (prime i), a*a=n from ⟨a,ha⟩)),
      card_factorSumResidues_of_square _ (prime_facts i).2 _ nz ⟨a,ha.symm⟩]
  · rw [if_neg (by simpa using h),card_factorSumResidues_of_nonsquare _ _ nz
      (fun ⟨a,ha⟩ => h ⟨a,ha.symm⟩)]

/-- For any prefix of distinct tests, the surviving fraction over a whole
wheel is exactly the product of its local pass fractions. -/
theorem survivor_fraction (n : ℕ) (A : Finset (Fin 7)) :
    (Nat.card {z : ZMod wheel // ∀ i ∈ A, AdmissibleSum (n:ZMod (prime i))
      (ZMod.prodEquivPi prime coprime z i)}:ℚ) / wheel =
      ∏ i ∈ A, (LocalSumMenu.count n (prime i):ℚ)/prime i := by
  let good (i : Fin 7) (x : ZMod (prime i)) := i ∈ A → AdmissibleSum (n:ZMod (prime i)) x
  let e := (ZMod.prodEquivPi prime coprime).toEquiv
  let f := (e.subtypeEquiv (p:=fun z => ∀ i, good i (e z i))
      (q:=fun a => ∀ i, good i (a i)) (fun _ => Iff.rfl)).trans Equiv.subtypePiEquivPi
  have local_size (i : Fin 7) : Nat.card {x : ZMod (prime i) // good i x} =
      if i ∈ A then LocalSumMenu.count n (prime i) else prime i := by
    by_cases hi : i ∈ A
    · simp [good,hi,LocalSumMenu.count]
    · simp [good,hi,Nat.card_eq_fintype_card,ZMod.card]
  have hs := Nat.card_congr f
  rw [Nat.card_pi] at hs
  simp only [local_size] at hs
  change (Nat.card {z // ∀ i, good i (e z i)}:ℚ) / wheel = _
  rw [hs,wheel,Nat.cast_prod,Nat.cast_prod,←Finset.prod_div_distrib]
  calc
    _ = ∏ i : Fin 7, (if i∈A then (LocalSumMenu.count n (prime i):ℚ)/prime i else 1) := by
      apply prod_congr rfl
      intro i _
      by_cases hi : i∈A <;> simp [hi,(prime_facts i).1.ne_zero]
    _ = _ := by simp

/-- The low bit refers to 3 and the high bit to 19. A set bit means square. -/
noncomputable def rates (m : Fin 128) : List ℚ := List.ofFn fun i => rate i (m.val.testBit i.val)
noncomputable def ascending (m : Fin 128) := expected (rates m)
noncomputable def best (m : Fin 128) := expected ((rates m).insertionSort (· ≤ ·))
noncomputable def saving (m : Fin 128) := (ascending m-best m)/ascending m

theorem minimal (m : Fin 128) (other : List ℚ) (perm : other.Perm (rates m)) :
    best m ≤ expected other := by
  apply optimal (List.sorted_insertionSort ..) ((List.perm_insertionSort ..).trans perm.symm)
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (perm.subset hp)
  unfold rate
  positivity

private def bitsOf (m : Fin 128) (i : Fin 7) := m.val.testBit i.val

private theorem bits_injective : Function.Injective bitsOf := by
  intro a b equal
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases short : j < 7
  · exact congrFun equal ⟨j,short⟩
  · have bound : 128 ≤ 2^j := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ j)
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le bound),Nat.testBit_lt_two_pow (b.isLt.trans_le bound)]

private theorem signs_covered (f : Fin 7 → Bool) :
    ∃ m : Fin 128, ∀ i : Fin 7, m.val.testBit i.val = f i := by
  have bij : Function.Bijective bitsOf :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨bits_injective,by simp⟩
  obtain ⟨m,eq⟩ := bij.2 f
  exact ⟨m,congrFun eq⟩

/-- The table exhausts the possible local pass fractions for every input
coprime to the odd wheel. -/
theorem input_rates (n : ℕ) (cop : wheel.Coprime n) :
    ∃ m : Fin 128, rates m = List.ofFn (fun i => (LocalSumMenu.count n (prime i):ℚ)/prime i) := by
  obtain ⟨m,bits⟩ := signs_covered (fun i => isSquareAt i n)
  exact ⟨m,congrArg List.ofFn (funext fun i => (bits i ▸ true_rate n cop i).symm)⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
/-- Exact census and endpoints of the savings relative to testing in
ascending prime order. The two nonzero endpoints each have a unique mask. -/
theorem census : ∀ m : Fin 128,
    (best m = ascending m ↔ m.val=0 ∨ m.val=64) ∧
    (m.val≠0 → m.val≠64 → 18/760513 ≤ saving m) ∧
    (saving m = 18/760513 ↔ m.val=96) ∧
    saving m ≤ 2992699/11977429 ∧
    (saving m = 2992699/11977429 ↔ m.val=7) := by decide +kernel

/-- For an actual product coprime to the wheel, ascending prime order is
optimal precisely when the product is a nonsquare at each prime through 17. -/
theorem ascending_optimal_iff (n : ℕ) (cop : wheel.Coprime n) :
    let qs := List.ofFn (fun i => (LocalSumMenu.count n (prime i):ℚ)/prime i)
    expected (qs.insertionSort (· ≤ ·)) = expected qs ↔
      ∀ i : Fin 7, i.val < 6 → ¬ IsSquare (n : ZMod (prime i)) := by
  dsimp only
  obtain ⟨m,bits⟩ := signs_covered (fun i => isSquareAt i n)
  have same : rates m = List.ofFn (fun i => (LocalSumMenu.count n (prime i):ℚ)/prime i) :=
    congrArg List.ofFn (funext fun i => (bits i ▸ true_rate n cop i).symm)
  rw [←same]
  change best m = ascending m ↔ _
  rw [(census m).1]
  have first : ∀ a : Fin 128, (a.val=0 ∨ a.val=64) ↔
      ∀ i : Fin 7, i.val<6 → a.val.testBit i.val=false := by decide +kernel
  rw [first]
  simp only [bits,isSquareAt,decide_eq_false_iff_not]
  constructor
  · intro h i hi square
    obtain ⟨x,hx⟩ := square
    exact h i hi ⟨x,hx.symm⟩
  · intro h i hi ⟨x,hx⟩
    exact h i hi ⟨x,hx.symm⟩

theorem strict_saving (m : Fin 128) :
    best m < ascending m ↔ m.val ≠ 0 ∧ m.val ≠ 64 := by
  have le := minimal m _ (List.Perm.refl _)
  change best m ≤ ascending m at le
  rw [lt_iff_le_and_ne]
  simp only [le,true_and,ne_eq,(census m).1,not_or]

theorem improving_masks : ((range 128).filter (fun m => m≠0 ∧ m≠64)).card=126 := by decide +kernel

theorem endpoint_costs :
    4849845*ascending 7=11977429 ∧ 4849845*best 7=8984730 ∧
    4849845*ascending 96=7605130 ∧ 4849845*best 96=7604950 := by decide +kernel

/-- Match the signs on all local nonzero residues under CRT. -/
def Matches (m : Fin 128) (z : ZMod wheel) : Prop :=
  ∀ i : Fin 7, let x := ZMod.prodEquivPi prime coprime z i
               x ≠ 0 ∧ isSquareAt i x = m.val.testBit i.val

/-- The sign patterns partition precisely the units of the wheel. -/
theorem unit_iff_pattern (z : ZMod wheel) : IsUnit z ↔ ∃! m : Fin 128, Matches m z := by
  let e := ZMod.prodEquivPi prime coprime
  constructor
  · intro unit
    obtain ⟨m,bits⟩ := signs_covered (fun i => isSquareAt i (e z i))
    have coords := Pi.isUnit_iff.mp (unit.map e.toMonoidHom)
    have match_m : Matches m z := by
      intro i
      letI : Fact (prime i).Prime := ⟨(prime_facts i).1⟩
      exact ⟨(coords i).ne_zero,(bits i).symm⟩
    refine ⟨m,match_m,fun a h => ?_⟩
    exact bits_injective (funext fun i => (h i).2.symm.trans (match_m i).2)
  · rintro ⟨m,h,_⟩
    have points : IsUnit (e z) := by
      apply Pi.isUnit_iff.mpr
      intro i
      letI : Fact (prime i).Prime := ⟨(prime_facts i).1⟩
      exact isUnit_iff_ne_zero.mpr (h i).1
    simpa using points.map e.symm.toMonoidHom

private theorem half_units (i : Fin 7) (b : Bool) :
    Nat.card {x : ZMod (prime i) // x ≠ 0 ∧ isSquareAt i x=b} = (prime i-1)/2 := by
  rw [Nat.card_eq_fintype_card]
  fin_cases i <;> cases b <;> decide +kernel

/-- Each of the 128 patterns occupies 12,960 unit residues in the odd wheel. -/
theorem residues_per_pattern (m : Fin 128) : Nat.card {z : ZMod wheel // Matches m z}=12960 := by
  let e := (ZMod.prodEquivPi prime coprime).toEquiv
  let good (i : Fin 7) (x : ZMod (prime i)) := x ≠ 0 ∧ isSquareAt i x=m.val.testBit i.val
  let f : {z : ZMod wheel // Matches m z} ≃ (∀ i : Fin 7, {x : ZMod (prime i) // good i x}) :=
    (e.subtypeEquiv (p:=Matches m) (q:=fun a => ∀ i, good i (a i)) (fun _ => Iff.rfl)).trans
      Equiv.subtypePiEquivPi
  rw [Nat.card_congr f,Nat.card_pi]
  simp only [good,half_units]
  decide +kernel

end PrimeFactors.SevenPrimeFilterSavings
