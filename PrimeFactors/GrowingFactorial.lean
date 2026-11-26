import PrimeFactors.BatchIntervals
import PrimeFactors.FactorialProgressions
import PrimeFactors.FoldedFactorial
import PrimeFactors.ShortPascalRow
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! Inspect the block products already present at each interpolation stage.
Growing tables only after a miss bounds their size by the distance to the
first prime, even when the far end of the requested interval is much larger. -/
namespace PrimeFactors.GrowingFactorial

open Finset FactorialProgressions

/-- Consecutive wheel cycles whose products are available at block length h.
There are rho*h+1 samples, truncated to complete blocks of the requested range. -/
def covered (rho cycles h : ℕ) := h * min (rho*h+1) (cycles/h)

theorem within_budget (rho cycles h : ℕ) : covered rho cycles h ≤ cycles :=
  (Nat.mul_le_mul_left h (min_le_right ..)).trans (Nat.mul_div_le ..)

/-- A truncated stage is as far as any larger, aligned doubling can go. -/
theorem previous_full {rho cycles h : ℕ} (pos : 0<h)
    (extendsRange : covered rho cycles h < covered rho cycles (2*h)) :
    covered rho cycles h = h*(rho*h+1) := by
  by_cases full : rho*h+1 ≤ cycles/h
  · simp [covered,full]
  exfalso
  rw [covered, min_eq_right (le_of_not_ge full)] at extendsRange
  let t := min (rho*(2*h)+1) (cycles/(2*h))
  have lim : h*(2*t) ≤ cycles := by
    simpa [covered,t,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using
      within_budget rho cycles (2*h)
  have div : 2*t ≤ cycles/h := (Nat.le_div_iff_mul_le pos).mpr (by simpa [Nat.mul_comm] using lim)
  have hi := Nat.mul_le_mul_left h div
  change h*(cycles/h) < 2*h*t at extendsRange
  nlinarith only [hi,extendsRange]

/-- Let D count wheel cycles through the target. Every doubling actually
launched after a miss has next polynomial degree squared less than 4*rho*D. -/
theorem degree_before_hit {rho cycles h D : ℕ} (rp : 0<rho) (hp : 0<h)
    (extendsRange : covered rho cycles h < covered rho cycles (2*h))
    (miss : covered rho cycles h < D) : (rho*(2*h))^2 < 4*rho*D := by
  rw [previous_full hp extendsRange] at miss
  have z := Nat.mul_lt_mul_of_pos_left miss rp
  nlinarith only [z,Nat.zero_le (rho*h)]

/-- Each full doubling from degree d requests at most d+1 weights and
4d+1 reciprocal entries for its one convolution. -/
def inputBudget (rho : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => inputBudget rho k + (5*(rho*2^k)+2)

theorem input_budget (rho k : ℕ) :
    inputBudget rho k + 5*rho = 5*(rho*2^k) + 2*k := by
  induction k with
  | zero => simp [inputBudget]
  | succ k ih =>
    rw [inputBudget,pow_succ]
    nlinarith only [ih]

/-- The same bound applies to a clipped final convolution. -/
theorem last_cost {rho h count : ℕ} (cap : count ≤ rho*(2*h)+1) :
    (rho*h+1)+(2*count-1) ≤ 5*(rho*h)+2 := by
  rw [show rho*(2*h)=2*(rho*h) by ring] at cap
  omega

/-- Pairing opposite blocks uses two weights per sample and reciprocal
indices through last+degree+1, still linear in the current degree. -/
theorem folded_last_cost {d count : ℕ} (cap : count≤2*d+1) :
    2*(d+1) + ((2*count-1)+d+1) ≤ 7*d+4 := by omega

/-- With the terminal size fixed in advance, an early stop pays only the
convolutions from the completed levels. The final convolution is still unspent. -/
theorem skipped_final {rho g k stop : ℕ} (le : stop≤k) :
    (∑ i ∈ range stop, (7*rho*2^i+4)) + (3*rho*2^k + 2*g + 2)
      ≤ FoldedFactorial.foldedInputs rho g k := by
  have part := sum_le_sum_of_subset (f := fun i => 7*rho*2^i+4) (range_mono le)
  change (∑ i ∈ range stop, (7*rho*2^i+4)) ≤ (∑ i ∈ range k, (7*rho*2^i+4)) at part
  unfold FoldedFactorial.foldedInputs
  omega

/-- Appending factorial inverses in a group of units. If a new factorial
is a unit, walking backwards from it yields the old inverse factorial and
reciprocal without changing any of the stored entries. -/
theorem inverse_step {G : Type*} [CommGroup G] (previous step : G) :
    (previous*step)⁻¹ * step = previous⁻¹ ∧
      previous*(previous*step)⁻¹ = step⁻¹ := by
  simp [mul_assoc,mul_left_comm,mul_comm]

/-- Drop the previously checked whole blocks from the next gcd. An overlap
at the boundary is harmless because the old prefix was coprime to n. -/
private theorem checkpoint_gcd (cycleValue group : ℕ → ℕ) {n old h samples : ℕ}
    (size : 0<h) (growth : old ≤ h*samples)
    (all : ∀ k, (∏ j ∈ range k, group j) = ∏ i ∈ range (h*k), cycleValue i)
    (unit : (∏ i ∈ range old, cycleValue i).Coprime n) :
    n.gcd (∏ j ∈ Ico (old/h) samples, group j) =
    n.gcd (∏ i ∈ range (h*samples), cycleValue i) := by
  have bound := Nat.mul_div_le old h
  have divides : (∏ i ∈ range (h*(old/h)), cycleValue i) ∣ ∏ i ∈ range old, cycleValue i := by
    exact prod_dvd_prod_of_subset _ _ _ (range_mono bound)
  have cop : (∏ j ∈ range (old/h), group j).Coprime n := by
    rw [all]
    exact Nat.Coprime.of_dvd_left divides unit
  have le : old/h ≤ samples := by
    calc
      _ ≤ (h*samples)/h := Nat.div_le_div_right growth
      _ = _ := Nat.mul_div_cancel_left _ size
  rw [←all samples,←prod_range_mul_prod_Ico group le]
  exact (Nat.Coprime.gcd_mul_left_cancel_right _ cop).symm

theorem suffix_gcd (cycleValue : ℕ → ℕ) {n old h samples : ℕ}
    (size : 0<h) (growth : old ≤ h*samples)
    (unit : (∏ i ∈ range old, cycleValue i).Coprime n) :
    n.gcd (∏ j ∈ Ico (old/h) samples, ∏ s ∈ range h, cycleValue (h*j+s)) =
    n.gcd (∏ i ∈ range (h*samples), cycleValue i) := by
  apply checkpoint_gcd _ _ size growth _ unit
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [prod_range_succ,ih,Nat.mul_succ,prod_range_add]

/-- For a fixed midpoint the same one gcd checks both newly accessible
rings of cycles. The inner blocks may be discarded after a unit result. -/
theorem centered_gcd (f : ℤ → ℕ) {n old h samples : ℕ}
    (size : 0<h) (growth : old ≤ h*samples)
    (unit : (∏ i ∈ range old, (f i * f (-(i+1 : ℤ)))).Coprime n) :
    n.gcd (∏ j ∈ Ico (old/h) samples, FoldedFactorial.paired f h j) =
    n.gcd (∏ i ∈ range (h*samples), (f i * f (-(i+1 : ℤ)))) := by
  apply checkpoint_gcd _ _ size growth _ unit
  intro k
  rw [FoldedFactorial.paired_coverage,prod_mul_distrib]

/-- Multiplying a newly checked list of actual wheel candidates only needs
the first prime's position; the larger prime cannot enter the search strip. -/
theorem membership {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (balanced : q≤2*p) (candidates : List ℕ)
    (band : ∀ x∈candidates, 0<x ∧ x≤(p*q).sqrt) :
    (p*q).gcd candidates.prod = if p∈candidates then p else 1 :=
  batchIntervals_balanced_gcd hp hq lt balanced candidates band

/-- Exact distance from the public starting point to the smaller factor.
Either prime approaching its bit-range boundary makes the distance small. -/
theorem endpoint_distance {p q B : ℕ} (pp : 0<p) (qp : 0<q)
    (hi : q≤2*B-1) :
    p - ShortPascalRow.lower (p*q) B =
      min (p-B) (p*((2*B-1)-q)/(2*B-1)) := by
  let M := 2*B-1
  change q≤M at hi
  have mp : 0<M := by omega
  let t := (p*q-1)/M
  have npos := Nat.mul_pos pp qp
  have bot : t*M ≤ p*q-1 := Nat.div_mul_le_self ..
  have top : p*q-1 < (t+1)*M := (Nat.div_lt_iff_lt_mul mp).mp (Nat.lt_succ_self t)
  have lim : p*q ≤ p*M := Nat.mul_le_mul_left p hi
  have tp : t < p := (Nat.div_lt_iff_lt_mul mp).mpr (by omega)
  have gap : p = (p-(t+1))+(t+1) := (Nat.sub_add_cancel (by omega)).symm
  have split := congrArg (·*M) gap
  dsimp only at split
  rw [Nat.add_mul] at split
  have diff := Nat.sub_add_cancel hi
  have diffMul := congrArg (p*·) diff
  dsimp only at diffMul
  rw [Nat.mul_add] at diffMul
  have ceilBound : p*q ≤ (t+1)*M := by omega
  have need : p*(M-q)/M = p-(t+1) := by
    apply Nat.div_eq_of_lt_le
    · nlinarith only [split,ceilBound,diffMul]
    · nlinarith only [split,bot,diffMul,npos,Nat.sub_add_cancel (show 1≤p*q by omega)]
  unfold ShortPascalRow.lower
  change p-max B (t+1) = min (p-B) (p*(M-q)/M)
  rw [need]
  omega

end PrimeFactors.GrowingFactorial
