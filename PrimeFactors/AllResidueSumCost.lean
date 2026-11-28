import PrimeFactors.NormalizedSumWork
import PrimeFactors.MeanSumOrderGeometry

/-! Cost of leaving the ascending traversal unchanged on nonsquare units modulo five.
Every complete block of 100 integers has ten passing sums on these inputs. -/

namespace PrimeFactors.AllResidueSumCost

open Finset FactorSumPrefixCost GlobalSumOrderCost
open PeriodicSumRank (favored passes row complete_group window)
open NormalizedSumWork (ascending coord saved prioritized)
open WideResiduePrimeSupply (B)
open scoped Classical

open private PrimeFactors.GlobalSumOrderCost.cover from PrimeFactors.GlobalSumOrderCost
open private PrimeFactors.NormalizedSumWork.before_identity
  PrimeFactors.NormalizedSumWork.floor_endpoint PrimeFactors.NormalizedSumWork.target_low
  from PrimeFactors.NormalizedSumWork

private theorem rows : ∀ r : Fin 100, r.val % 5 = 2 ∨ r.val % 5 = 3 →
    (row r.val true).card = 0 ∧ (row r.val false).card = 10 := by decide +kernel

private theorem residue {n : ℕ} (ns : n % 5 = 2 ∨ n % 5 = 3) :
    (n % 100) % 5 = 2 ∨ (n % 100) % 5 = 3 := by
  simpa only [Nat.mod_mod_of_dvd n (by decide : 5 ∣ 100)] using ns

/-- No sum can be favored on a nonsquare product. -/
theorem no_favored {n : ℕ} (ns : n % 5 = 2 ∨ n % 5 = 3) (s : ℕ) :
    favored (n % 100) (s % 100) = false := by
  have table : ∀ a b : Fin 5, a.val = 2 ∨ a.val = 3 →
      (b.val * b.val) % 5 ≠ (4 * a.val) % 5 := by decide
  have neq := table ⟨n % 5, Nat.mod_lt _ (by decide)⟩ ⟨s % 5, Nat.mod_lt _ (by decide)⟩ ns
  apply Bool.eq_false_iff.mpr
  intro eq
  rw [favored, beq_iff_eq, Nat.mul_mod (s % 100), Nat.mul_mod 4,
    Nat.mod_mod_of_dvd n (by decide : 5 ∣ 100),
    Nat.mod_mod_of_dvd s (by decide : 5 ∣ 100)] at eq
  exact neq eq

/-- For nonsquare units both global prefixes are exactly the same set of tests. -/
theorem same_prefix {n : ℕ} (ns : n % 5 = 2 ∨ n % 5 = 3) (lo hi s : ℕ) :
    globalPrefix n lo hi s = passingPrefix n lo s := by
  have empty : favoredPrefix n (s+1) hi = ∅ := by
    ext t
    simp [favoredPrefix, no_favored ns]
  simp [globalPrefix, no_favored ns, empty]

theorem unchanged {p q : ℕ} (ns : (p*q) % 5 = 2 ∨ (p*q) % 5 = 3) :
    prioritized p q = ascending p q ∧ saved p q = 0 := by
  have eq : prioritized p q = ascending p q := by
    simp only [prioritized, ascending, same_prefix ns]
  exact ⟨eq, by rw [NormalizedSumWork.saved_eq, eq, sub_self]⟩

/-- The complete count holds starting at any offset. -/
theorem complete_count {n : ℕ} (ns : n % 5 = 2 ∨ n % 5 = 3) (a : ℕ) :
    ((Ico a (a+100)).filter fun x => passes (n%100) (x%100) = true).card = 10 := by
  have sizes := rows ⟨n%100, Nat.mod_lt _ (by decide)⟩ (residue ns)
  have eq := (complete_group (r := n%100) a false).trans sizes.2
  rw [Finset.filter_true_of_mem (fun x _ => no_favored ns x)] at eq
  simpa only [window, show a+99+1=a+100 by omega, min_self] using eq

theorem prefix_upper {n lo s : ℕ} (ns : n % 5 = 2 ∨ n % 5 = 3) (lower : lo ≤ s) :
    100 * (passingPrefix n lo s).card ≤ 10 * (s-lo) + 1000 := by
  let k := (s-lo)/100+1
  have top : s+1 ≤ lo+100*k := by dsimp [k]; omega
  have bound := PrimeFactors.GlobalSumOrderCost.cover _ (complete_count ns) top
  change (passingPrefix n lo s).card ≤ 10*k at bound
  dsimp only [k] at bound
  omega

/-- Ten tests per complete block and one incomplete block bound the work on
the nonsquare half of the unit residue pairs. -/
theorem non_square_bound {p q : ℕ} (ns : (p*q) % 5 = 2 ∨ (p*q) % 5 = 3) :
    100 * ascending p q ≤ 10 * (B : ℝ) * MeanSumOrderGeometry.D (coord p) (coord q) + 1000 := by
  let s := p+q
  let lo := ceilSqrt (4*(p*q))
  have lower : lo ≤ s := PrimeFactors.NormalizedSumWork.target_low p q
  have work : 100 * ascending p q ≤ 10 * ((s-lo : ℕ) : ℝ) + 1000 := by
    unfold ascending
    exact_mod_cast prefix_upper ns lower
  rw [Nat.cast_sub lower] at work
  have rad := PrimeFactors.NormalizedSumWork.floor_endpoint (p*q)
  rw [MeanSumOrderGeometry.D, mul_assoc, PrimeFactors.NormalizedSumWork.before_identity]
  have sum : (s : ℝ) = (p : ℝ) + q := Nat.cast_add ..
  rw [sum] at work
  exact work.trans (add_le_add_right (mul_le_mul_of_nonneg_left (sub_le_sub_left rad _) (by norm_num)) _)

/-- Convert the pointwise cost to the units used by the rectangle totals. -/
theorem base_units {b q d hi a : ℝ} (bp : 0 < b) (qp : 0 ≤ q)
    (rounding : 1000*q ≤ b) (corner : q*d ≤ hi) (bound : 100*a ≤ 10*b*d+1000) :
    (100*q/b)*a ≤ 10*hi+1 := by
  apply (mul_le_mul_iff_of_pos_right bp).mp
  field_simp [bp.ne']
  nlinarith only [mul_le_mul_of_nonneg_left corner bp.le,
    mul_le_mul_of_nonneg_left bound qp,rounding]

/-- One group of four prime residue pairs saves tests, another four costs
tests, and the eight remaining pairs use ascending order. These bounds in
common units imply a saving strictly greater than one ninety-fifth. -/
theorem pooled_margin {l u f r a o : ℝ} (pos : 0 < l) (mass : 1000*u ≤ 1018*l)
    (gain : l*5*18546979888483033 ≤ f + u*5124)
    (loss : -r ≤ u*(2*41811592525905920+5124))
    (base : a ≤ 2*u*(7*20783259569430118+5124))
    (other : o ≤ 2*u*(10*20783259569430118+5124)) :
    a + o < 95 * (f+r) := by
  linarith only [pos,mass,gain,loss,base,other]

end PrimeFactors.AllResidueSumCost
