import PrimeFactors.TwoCharacterWindow
import Mathlib.Data.Nat.Periodic
import PrimeFactors.FiniteUnitDensity

/-! Explicit arithmetic for a negative prime character witness. The analytic
bounds of Rosser–Schoenfeld and Frolenkov–Soundararajan enter as hypotheses. -/
namespace PrimeFactors.UnconditionalSignBudget

open Finset Real

set_option exponentiation.threshold 3000
set_option maxRecDepth 6000

def X : ℕ := 2^1047
def Y : ℕ := 2^940

private theorem cofactor_block (z : ℕ) :
    ((Ico (z+1) (z+1+30)).filter (fun m => m.Coprime 30)).card = 8 := by
  rw [Nat.filter_Ico_card_eq_of_periodic]
  · decide +kernel
  · intro n
    exact propext Nat.coprime_add_self_left

/-- A full block has eight allowed cofactors. An incomplete initial block
raises the upper discrepancy by less than one. -/
theorem cofactors_thirty (z : ℕ) :
    15 * ((Icc 1 z).filter (fun m => m.Coprime 30)).card ≤ 4*z+15 := by
  induction z using Nat.strong_induction_on with
  | h z ih =>
    by_cases short : z < 30
    · have check : ∀ i : Fin 30,
          15 * ((Icc 1 i.val).filter (fun m => m.Coprime 30)).card ≤ 4*i.val+15 := by
        decide +kernel
      exact check ⟨z, short⟩
    · let t := z-30
      have tz : z = t+30 := by dsimp [t]; omega
      have prev := ih t (by dsimp [t]; omega)
      have block := cofactor_block t
      have split : Icc 1 z = Icc 1 t ∪ Ico (t+1) (t+1+30) := by
        rw [← Nat.Ico_succ_right, ← Nat.Ico_succ_right]
        convert (Ico_union_Ico_eq_Ico (show 1 ≤ t+1 by omega)
          (show t+1 ≤ t+1+30 by omega)).symm using 2; omega
      have disj : Disjoint (Icc 1 t) (Ico (t+1) (t+1+30)) := by
        rw [← Nat.Ico_succ_right]
        exact Ico_disjoint_Ico_consecutive _ _ _
      rw [split, filter_union, card_union_of_disjoint
        (disj.mono (filter_subset _ _) (filter_subset _ _)), block]
      omega

/-- Every modulus divisible by 30 inherits the same cofactor bound. -/
theorem cofactors {M : ℕ} (div : 30 ∣ M) (z : ℕ) :
    (((Icc 1 z).filter (fun m => m.Coprime M)).card : ℝ) ≤ (4/15)*z + 1 := by
  have subset : (Icc 1 z).filter (fun m => m.Coprime M) ⊆
      (Icc 1 z).filter (fun m => m.Coprime 30) := by
    intro m hm
    obtain ⟨inside, cop⟩ := mem_filter.mp hm
    exact mem_filter.mpr ⟨inside, Nat.Coprime.of_dvd_right div cop⟩
  have n := (Nat.mul_le_mul_left 15 (card_le_card subset)).trans (cofactors_thirty z)
  have r : (15:ℝ)*↑((Icc 1 z).filter (fun m => m.Coprime M)).card ≤ 4*z+15 := by
    exact_mod_cast n
  linarith only [r]

private theorem log_sizes :
    640 < log (Y:ℝ) ∧ 700 < log (X:ℝ) := by
  simp only [Y, X, Nat.cast_pow, Nat.cast_ofNat, log_pow]
  constructor <;> linarith [Real.log_two_gt_d9]

/-- The endpoint error in the reciprocal-prime sum is under 0.115.
Rosser–Schoenfeld, Theorem 5 (3.17–18), supplies the expression on the left. -/
theorem reciprocal_tail_budget :
    log (log (X:ℝ)) - log (log (Y:ℝ)) +
      1/(2*(log (X:ℝ))^2) + 1/(2*(log (Y:ℝ))^2) < 115/1000 := by
  obtain ⟨ly,lx⟩ := log_sizes
  have ex : log (X:ℝ) = 1047*log 2 := by simp only [X, Nat.cast_pow, Nat.cast_ofNat, log_pow]
  have ey : log (Y:ℝ) = 940*log 2 := by simp only [Y, Nat.cast_pow, Nat.cast_ofNat, log_pow]
  have quotient : log (X:ℝ) / log (Y:ℝ) = 1047/940 := by
    rw [ex,ey]; field_simp [ne_of_gt (log_pos (show (1:ℝ)<2 by norm_num))]; ring
  have main := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1047/940)
  rw [← log_div (by linarith : log (X:ℝ) ≠ 0) (by linarith : log (Y:ℝ) ≠ 0), quotient]
  have term {l : ℝ} (h : 600 < l) : 1/(2*l^2) < 1/700000 := by
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith [sq_nonneg (l-600)]
  linarith [term (lt_trans (by norm_num) ly), term (lt_trans (by norm_num) lx)]

/-- Rosser–Schoenfeld (3.6) supplies 1.25506/log X. -/
theorem prime_count_budget : (1.25506:ℝ)/log (X:ℝ) < 2/1000 := by
  have lx := log_sizes.2
  apply (div_lt_iff₀ (by linarith)).mpr
  linarith


/-- The contiguous character-sum inequality in the form of
Frolenkov–Soundararajan, Corollary 1, fits well below the lower sign budget. -/
theorem pv_budget {M : ℕ} (low : 0 < M) (high : M < 2^2057) :
    sqrt M * ((log M + 6)/(Real.pi*sqrt 2)+1) ≤ (X:ℝ)/512 := by
  have root : M ≤ (2^1029)^2 := high.le.trans (by norm_num)
  have h := TwoCharacterWindow.integer_error (r:=2^1029) (b:=2057) (E:=2^1038)
    low root high.le (by norm_num)
  exact h.trans (by norm_num [X])

/-- Combining a coprime-count discrepancy, the count of negative signs,
and the three published analytic bounds gives a contradiction. All three counts
A,B,P are represented as reals to avoid normalization of large finite sets. -/
theorem contradiction {M : ℕ} {A B P R S : ℝ} (low : Y < M) (high : M < 2^2057)
    (units : (X:ℝ) * (M.totient:ℝ) / M - 2*sqrt M ≤ A)
    (negative : B ≤ (4/15)*(X:ℝ)*R + P)
    (total : S = A-2*B)
    (tail_estimate : R ≤ log (log (X:ℝ)) - log (log (Y:ℝ)) +
      1/(2*(log (X:ℝ))^2) + 1/(2*(log (Y:ℝ))^2))
    (count_estimate : P/(X:ℝ) ≤ 1.25506/log (X:ℝ))
    (pv_estimate : |S| ≤ sqrt M * ((log M+6)/(Real.pi*sqrt 2)+1)) : False := by
  have pos : 0<M := (Nat.zero_le Y).trans_lt low
  have mr : 0<(M:ℝ) := by exact_mod_cast pos
  have xp : 0<(X:ℝ) := by norm_num [X]
  have ratio : (M:ℝ) < 14 * M.totient := by exact_mod_cast FiniteUnitDensity.density pos high
  have density : (X:ℝ)/14 < (X:ℝ) * M.totient / M := by
    apply (lt_div_iff₀ mr).mpr
    linarith only [mul_lt_mul_of_pos_left ratio xp]
  have sr : sqrt (M:ℝ) ≤ (2:ℝ)^1029 := by
    apply sqrt_le_iff.mpr
    exact ⟨by positivity, (show (M:ℝ)≤(2:ℝ)^2057 by exact_mod_cast high.le).trans (by norm_num)⟩
  have rootBound : 2*sqrt (M:ℝ) ≤ (X:ℝ)/131072 := by
    calc 2*sqrt (M:ℝ) ≤ 2*(2:ℝ)^1029 := by gcongr
         _ = _ := by norm_num [X]
  have tail := mul_lt_mul_of_pos_left (tail_estimate.trans_lt reciprocal_tail_budget)
    (show (0:ℝ)<4/15*(X:ℝ) by positivity)
  have pc := (div_lt_iff₀ xp).mp (count_estimate.trans_lt prime_count_budget)
  have pv := (le_abs_self S).trans (pv_estimate.trans (pv_budget pos high))
  linarith only [units, density, rootBound, negative, tail, pc, total, pv, xp]

end PrimeFactors.UnconditionalSignBudget
