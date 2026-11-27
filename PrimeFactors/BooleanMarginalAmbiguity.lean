import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-! Counts of rows of Boolean observations. A cell is indexed by the set of
failed tests, so the empty cell is the full intersection of the passing tests.
Kahle identifies the parity kernel in *On Boundaries of Statistical Models*,
Example 2.5.1, p. 54 (https://d-nb.info/1006748466/34). -/
namespace PrimeFactors.BooleanMarginalAmbiguity
open Finset

variable {ι : Type*} [DecidableEq ι]

/-- A partial assignment fixes the failures outside the free coordinates. -/
noncomputable def marginal (T : Finset ι → ℕ) (fixed free : Finset ι) : ℕ :=
  ∑ b ∈ free.powerset, T (fixed ∪ b)

/-- The tables agree on every assignment with just one unspecified coordinate. -/
def SameFaces (T U : Finset ι → ℕ) : Prop :=
  ∀ s i, i ∉ s → T s + T (insert i s) = U s + U (insert i s)

/-- The difference at the all-pass cell controls every other difference.
Each coordinate flip reverses its sign. -/
theorem cell_difference {T U : Finset ι → ℕ} (faces : SameFaces T U) (s : Finset ι) :
    (T s:ℤ)-U s = (-1)^s.card*((T ∅:ℤ)-U ∅) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have edge : (T s:ℤ)+T (insert i s) = U s+U (insert i s) := by
      exact_mod_cast faces s i hi
    rw [card_insert_of_not_mem hi,pow_succ]
    linarith only [edge,ih]

/-- Agreement on faces implies agreement on every proper partial assignment,
including assignments which specify both passes and failures. -/
theorem proper_marginals {T U : Finset ι → ℕ} (faces : SameFaces T U)
    {fixed free : Finset ι} (disj : Disjoint fixed free) (nonempty : free.Nonempty) :
    marginal T fixed free = marginal U fixed free := by
  have step (b : Finset ι) (inside : b ∈ free.powerset) :
      (T (fixed ∪ b):ℤ)-U (fixed ∪ b) =
        ((-1)^fixed.card*((T ∅:ℤ)-U ∅)) * (-1)^b.card := by
    rw [cell_difference faces,card_union_of_disjoint (disj.mono_right (mem_powerset.mp inside)),pow_add]
    ring
  have h := sum_congr rfl step
  rw [sum_sub_distrib, ←mul_sum, sum_powerset_neg_one_pow_card_of_nonempty nonempty, mul_zero,
    sub_eq_zero] at h
  exact_mod_cast h

/-- For two tables of the same size, the all-pass difference multiplied by
the number of Boolean cells is at most twice their size. -/
theorem ambiguity_bound [Fintype ι] [Nonempty ι] {T U : Finset ι → ℕ}
    (faces : SameFaces T U) :
    (2:ℤ)^(Fintype.card ι) * |(T ∅:ℤ)-U ∅| ≤ 2*(marginal T ∅ univ:ℕ) := by
  have total := proper_marginals faces (fixed:=∅) (free:=univ) (by simp) univ_nonempty
  have step (b : Finset ι) (_ : b ∈ (univ : Finset ι).powerset) :
      |(T ∅:ℤ)-U ∅| ≤ (T b:ℤ)+U b := by
    have eq := congrArg abs (cell_difference faces b)
    simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] at eq
    rw [←eq,abs_le]
    constructor <;> omega
  have h := sum_le_sum step
  simp only [sum_const, card_powerset, card_univ, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat, sum_add_distrib] at h
  have sumT : (marginal T ∅ univ:ℤ) = ∑ b ∈ (univ:Finset ι).powerset, (T b:ℤ) := by
    simp [marginal]
  have sumU : (marginal U ∅ univ:ℤ) = ∑ b ∈ (univ:Finset ι).powerset, (U b:ℤ) := by
    simp [marginal]
  rw [←sumT,←sumU,←total] at h
  linarith only [h]

/-- Place w rows in each even cell, or in each odd cell. -/
def parityTable (w : ℕ) (even : Bool) (s : Finset ι) : ℕ :=
  if decide (Even s.card) = even then w else 0

theorem parity_faces (w : ℕ) : SameFaces (parityTable (ι:=ι) w true) (parityTable w false) := by
  intro s i hi
  rw [parityTable,parityTable,parityTable,parityTable,card_insert_of_not_mem hi]
  by_cases e : Even s.card <;> simp [e,Nat.even_add_one]

/-- A common row multiplicity gives identical counts on all proper assignments
while the full intersection takes the two values w and zero. -/
theorem parity_example (w : ℕ) :
    (∀ fixed free : Finset ι, Disjoint fixed free → free.Nonempty →
      marginal (parityTable w true) fixed free = marginal (parityTable w false) fixed free) ∧
    parityTable (ι:=ι) w true ∅ = w ∧ parityTable (ι:=ι) w false ∅ = 0 := by
  refine ⟨fun _ _ => proper_marginals (parity_faces w), ?_⟩
  simp [parityTable]

/-- Each table in the example has exactly half of all 2^k cells, with w rows
per occupied cell. Hence the upper bound is sharp. -/
theorem parity_mass [Fintype ι] [Nonempty ι] (w : ℕ) :
    2*marginal (parityTable (ι:=ι) w true) ∅ univ = 2^(Fintype.card ι)*w := by
  have eq := proper_marginals (parity_faces (ι:=ι) w) (fixed:=∅) (free:=univ)
    (by simp) univ_nonempty
  have pair (b : Finset ι) : parityTable w true b + parityTable w false b = w := by
    by_cases e : Even b.card <;> simp [parityTable,e]
  have sums : marginal (parityTable (ι:=ι) w true) ∅ univ +
      marginal (parityTable (ι:=ι) w false) ∅ univ = 2^(Fintype.card ι)*w := by
    simp only [marginal,empty_union,←sum_add_distrib,pair,sum_const,card_powerset,card_univ,
      nsmul_eq_mul]
    norm_cast
  omega

/-- With k+1 tests and n observations, the greatest possible difference
at the full intersection is at most floor(n/2^k). -/
theorem full_intersection_bound {k : ℕ} {T U : Finset (Fin (k+1)) → ℕ}
    (faces : SameFaces T U) :
    ((T ∅:ℤ)-U ∅).natAbs ≤ marginal T ∅ univ / 2^k := by
  have h := ambiguity_bound faces
  simp only [Fintype.card_fin, pow_succ, ←Int.natCast_natAbs] at h
  apply (Nat.le_div_iff_mul_le (by positivity)).mpr
  have cast : ((T ∅:ℤ)-U ∅).natAbs * (2:ℤ)^k ≤ (marginal T ∅ univ:ℤ) := by
    linarith only [h]
  exact_mod_cast cast

/-- Below the first possible parity ambiguity, the same marginals determine
the whole table. -/
theorem unique_of_small {k : ℕ} {T U : Finset (Fin (k+1)) → ℕ}
    (faces : SameFaces T U) (small : marginal T ∅ univ < 2^k) : T = U := by
  have bound := full_intersection_bound faces
  rw [Nat.div_eq_of_lt small] at bound
  have eq : (T ∅:ℤ)-U ∅ = 0 := Int.natAbs_eq_zero.mp (by omega)
  funext s
  have h := cell_difference faces s
  rw [eq,mul_zero] at h
  omega

/-- Add the same r all-pass rows to a table. -/
private def pad (r : ℕ) (T : Finset ι → ℕ) (s : Finset ι) := T s + if s = ∅ then r else 0

private theorem pad_faces {T U : Finset ι → ℕ} (faces : SameFaces T U) (r : ℕ) :
    SameFaces (pad r T) (pad r U) := by
  intro s i hi
  have h := faces s i hi
  unfold pad
  omega

private theorem pad_mass [Fintype ι] (r : ℕ) (T : Finset ι → ℕ) :
    marginal (pad r T) ∅ univ = marginal T ∅ univ + r := by
  simp [marginal,pad,sum_add_distrib]

/-- The bound is attained at every sample size. The common remainder rows
leave all marginal equalities intact. -/
theorem sharp (k n : ℕ) : ∃ T U : Finset (Fin (k+1)) → ℕ,
    SameFaces T U ∧ marginal T ∅ univ = n ∧ marginal U ∅ univ = n ∧ T ∅ = U ∅ + n/2^k := by
  let w := n/2^k
  let r := n%2^k
  let T := parityTable (ι:=Fin (k+1)) w true
  let U := parityTable (ι:=Fin (k+1)) w false
  have same : SameFaces T U := parity_faces w
  have mass := parity_mass (ι:=Fin (k+1)) w
  simp only [Fintype.card_fin, pow_succ] at mass
  have tm : marginal T ∅ univ = 2^k*w := by
    change marginal (parityTable (ι:=Fin (k+1)) w true) ∅ univ = _
    nlinarith only [mass]
  have um : marginal U ∅ univ = 2^k*w :=
    (proper_marginals same (fixed:=∅) (free:=univ) (by simp) univ_nonempty).symm.trans tm
  have size : 2^k*w+r=n := by
    simpa only [Nat.add_comm] using Nat.mod_add_div n (2^k)
  refine ⟨pad r T,pad r U,pad_faces same r,?_,?_,?_⟩
  · rw [pad_mass,tm,size]
  · rw [pad_mass,um,size]
  · simp [pad,T,U,parityTable,w,Nat.add_comm]

end PrimeFactors.BooleanMarginalAmbiguity
