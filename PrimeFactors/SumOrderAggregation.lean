import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-! Summing signed savings across a partition. The same upper mass bound
accounts for unsuccessful guesses, incomplete periods, and baseline work. -/

namespace PrimeFactors.SumOrderAggregation

open Finset
open scoped BigOperators

/-- Lower bound on positive work saved in a cell. The one-unit allowance
is charged to every member and rounded up using the upper population. -/
theorem gain {α : Type*} (S : Finset α) (v : α → ℝ) {l u c : ℝ}
    (lc : l≤S.card) (uc : (S.card:ℝ)≤u) (pos : 0≤c)
    (test : ∀ x∈S, c≤v x+1) : l*c≤(∑ x∈S,v x)+u := by
  have all := sum_le_sum test
  simp only [sum_const,nsmul_eq_mul,sum_add_distrib,mul_one] at all
  linarith only [mul_le_mul_of_nonneg_right lc pos,uc,all]

/-- Upper bound for baseline work or for additional work in a cell. -/
theorem expense {α : Type*} (S : Finset α) (v : α → ℝ) {u c : ℝ}
    (uc : (S.card:ℝ)≤u) (pos : 0≤c) (test : ∀ x∈S, v x≤c) :
    (∑ x∈S,v x)≤u*c := by
  have all := sum_le_sum test
  simpa only [sum_const,nsmul_eq_mul] using all.trans (by
    simpa only [sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right uc pos)

/-- Keep positive credits for complete cells. The others still pay the
same upper allowance for the final incomplete block. -/
theorem gains_over_cells {ι : Type*} [DecidableEq ι] (cells whole : Finset ι)
    (sub : whole ⊆ cells) (v d : ι → ℝ) {l u : ℝ}
    (u0 : 0≤u) (inside : ∀ j∈whole, l*(5*d j)≤v j+u)
    (outside : ∀ j∈cells, j∉whole → 0≤v j) :
    l*5*(∑ j∈whole,d j)≤(∑ j∈cells,v j)+u*cells.card := by
  classical
  have all : ∀ j∈cells, (if j∈whole then l*(5*d j) else 0)≤v j+u := by
    intro j hj
    split_ifs with h
    · exact inside j h
    · exact add_nonneg (outside j hj h) u0
  have h := sum_le_sum all
  simp only [←sum_filter,sum_add_distrib,sum_const,nsmul_eq_mul] at h
  have filtered : cells.filter (fun j => j∈whole)=whole := by
    ext j
    simp only [mem_filter]
    exact ⟨And.right,fun hj => ⟨sub hj,hj⟩⟩
  rw [filtered] at h
  simpa only [←mul_assoc,←mul_sum,mul_comm u] using h

/-- Charge each cell a geometric allowance and a single rounding allowance
per possible element. The inequality works for losses and baseline tests. -/
theorem expenses_over_cells {ι : Type*} (cells : Finset ι) (v d : ι → ℝ) {u c : ℝ}
    (each : ∀ j∈cells, v j≤u*(c*d j+1)) :
    (∑ j∈cells,v j)≤u*(c*(∑ j∈cells,d j)+cells.card) := by
  have h := sum_le_sum each
  simpa only [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one] using h

/-- Scale square-test counts to the same units as the integer grid
certificate. Less than one unit covers endpoint and period rounding. -/
theorem gain_units {b q d lo s : ℝ} (bp : 0<b) (qp : 0≤q)
    (rounding : 505*q≤b) (corner : lo≤q*d) (bound : 5*b*d-505≤100*s) :
    5*lo≤(100*q/b)*s+1 := by
  apply (mul_le_mul_iff_of_pos_right bp).mp
  field_simp [bp.ne']
  nlinarith only [mul_le_mul_of_nonneg_left corner bp.le,
    mul_le_mul_of_nonneg_left bound qp,rounding]

theorem loss_units {b q g hi s : ℝ} (bp : 0<b) (qp : 0≤q)
    (rounding : 200*q≤b) (corner : q*g≤hi) (bound : -(2*b*g)-200≤100*s) :
    -((100*q/b)*s)≤2*hi+1 := by
  apply (mul_le_mul_iff_of_pos_right bp).mp
  rw [show -((100*q/b)*s)*b= -(100*q*s) by
    rw [neg_mul,div_mul_eq_mul_div,div_mul_cancel₀ _ bp.ne']]
  nlinarith only [mul_le_mul_of_nonneg_left corner bp.le,
    mul_le_mul_of_nonneg_left bound qp,rounding]

theorem base_units {b q d hi a : ℝ} (bp : 0<b) (qp : 0≤q)
    (rounding : 700*q≤b) (corner : q*d≤hi) (bound : 100*a≤7*b*d+700) :
    (100*q/b)*a≤7*hi+1 := by
  apply (mul_le_mul_iff_of_pos_right bp).mp
  field_simp [bp.ne']
  nlinarith only [mul_le_mul_of_nonneg_left corner bp.le,
    mul_le_mul_of_nonneg_left bound qp,rounding]

/-- Explicit budgets for the two groups and the baseline imply a strict
one-fortieth reduction in square tests. Weights are in identical units. -/
theorem pooled {f r a l u dl dh gh k : ℝ}
    (gain : l*5*dl≤f+u*k) (loss : -r≤u*(2*gh+k))
    (base : a≤2*u*(7*dh+k))
    (margin : u*(80*gh+14*dh+82*k)<l*200*dl) : a<40*(f+r) := by
  linarith only [gain,loss,base,margin]

/-- The finite-grid arithmetic and a ratio on cell populations suffice. -/
theorem grid_margin {l u : ℝ} (pos : 0<l) (mass : 1000*u≤1018*l) :
    u*(80*41811592525905920+14*20783259569430118+82*5124) <
      l*200*18546979888483033 := by
  linarith only [mass,pos]

end PrimeFactors.SumOrderAggregation
