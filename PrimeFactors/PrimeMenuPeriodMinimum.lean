import PrimeFactors.ArbitraryMidpointMenu
import PrimeFactors.PrimeMenuDensityOrder

/-! The smallest complete-period lower bound among all prime menus that
fit the early window, including menus chosen separately for each product. -/
namespace PrimeFactors.PrimeMenuPeriodMinimum

open Finset ArbitraryMidpointMenu PrimeMenuDensityOrder
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

abbrev W : ℕ := 2^896
noncomputable abbrev first := core 643

/-- Arithmetic for the complete period of the initial segment. -/
theorem constants : period first≤W ∧ W/period first=1 ∧ 2^765<lanes first ∧
    W<3456*(647*(∏ p∈first,p)) := by decide +kernel

attribute [local irreducible] core period lanes

private theorem valid_first (p : ℕ) (h : p∈first) : p.Prime ∧ 5≤p :=
  ⟨(mem_core.mp h).1,(mem_core.mp h).2.1⟩

private theorem lower_period {S : Finset ℕ} (valid : ∀ p∈S,p.Prime ∧ 5≤p) : 0<period S := by
  rw [period]
  exact Nat.mul_pos (by decide) (prod_pos (fun p hp => (valid p hp).1.pos))

private theorem core_density : (lanes first:ℚ) =
    (period first:ℚ)/432*(∏ p∈first,density p) := by
  have ratio := density_eq first (fun p hp => (valid_first p hp).1) (fun p hp => (valid_first p hp).2)
  have pos : (0:ℚ)<period first := by exact_mod_cast lower_period valid_first
  have id := (div_eq_iff pos.ne').mp ratio
  rw [id]
  unfold density
  ring

/-- This certificate is attained by the initial segment. It only counts
guaranteed residue classes in complete periods of the window. -/
theorem minimum (S : Finset ℕ) (valid : ∀ p∈S,p.Prime ∧ 5≤p) (budget : period S≤W) :
    lanes first≤W/period S*lanes S := by
  have cheap : (∏ p∈S,p)<647*(∏ p∈first,p) := by
    have h := budget.trans_lt constants.2.2.2
    rw [period] at h
    omega
  have size := (order643 S valid cheap).1
  rcases lt_or_eq_of_le size with fewer|equal
  · have twice := double_density_of_fewer S valid fewer
    have pos : 0≤∏ p∈first,density p := by
      apply prod_nonneg
      intro p hp
      have ge : (5:ℚ)≤p := by exact_mod_cast (valid_first p hp).2
      unfold density
      exact div_nonneg (by linarith) (by positivity)
    have wide : (period first:ℚ)≤(W:ℕ) := by exact_mod_cast constants.1
    have sufficient : (lanes first:ℚ)≤((W/period S*lanes S:ℕ):ℚ) := calc
      _ = (period first:ℚ)/432*(∏ p∈first,density p) := core_density
      _ ≤ (W:ℚ)/432*(∏ p∈first,density p) := by gcongr
      _ = (W:ℚ)/864*(2*(∏ p∈first,density p)) := by ring
      _ ≤ (W:ℚ)/864*(∏ p∈S,density p) := mul_le_mul_of_nonneg_left twice (by positivity)
      _ ≤ _ := certificate_half_density S W (fun p hp => (valid p hp).1) (fun p hp => (valid p hp).2) budget
    exact_mod_cast sufficient
  · have one : 1≤W/period S := (Nat.le_div_iff_mul_le (lower_period valid)).mpr (by simpa using budget)
    have raw : lanes first≤lanes S := by
      rw [lanes,lanes]
      exact Nat.mul_le_mul_left 8 (lanes_of_same S valid equal)
    exact raw.trans (by simpa only [one_mul] using Nat.mul_le_mul_right (lanes S) one)

theorem attained : W/period first*lanes first=lanes first := by rw [constants.2.1,one_mul]

theorem count (S : Finset ℕ) (start N : ℕ) (valid : ∀ p∈S,p.Prime ∧ 5≤p)
    (budget : period S≤2^896) (unit : ∀ p∈bases S, ¬p∣N) :
    2^765 < Nat.card (survivors S start (2^896) N) :=
  constants.2.2.1.trans_le ((minimum S valid budget).trans
    (interval S start W N (fun p hp => (valid p hp).1) (fun p hp => (valid p hp).2) unit))

end PrimeFactors.PrimeMenuPeriodMinimum
