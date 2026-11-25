import PrimeFactors.QuotientBudget
import Mathlib.Data.Nat.Sqrt

namespace PrimeFactors

/-- The actual rounded midpoint and half-gap bounds at target size give a
uniform lower bound on the area used to choose the radix. -/
theorem midpoint_weight_volume {N : ℕ} (size : 2^2047 ≤ N) :
    let H := (9*N/8).sqrt - ((N-1).sqrt+1)
    2^2043 ≤ 8*H*(N/8).sqrt := by
  let s := N.sqrt
  let J : ℕ := 2^1018
  have s0 : 2^1023 ≤ s := Nat.le_sqrt.mpr
    ((by decide +kernel : 2^1023 * 2^1023 ≤ (2:ℕ)^2047).trans size)
  have margin : 20*(J+1) ≤ s := (by decide +kernel : 20*(J+1) ≤ 2^1023).trans s0
  have sq := Nat.mul_self_le_mul_self (show 20*(s+J+1) ≤ 21*s by omega)
  have bound : 8*((s+J+1)*(s+J+1)) ≤ 9*N := by
    have hs : s*s ≤ N := Nat.sqrt_le N
    nlinarith
  have up : s+J+1 ≤ (9*N/8).sqrt := Nat.le_sqrt.mpr (by omega)
  have down : (N-1).sqrt ≤ s := Nat.sqrt_le_sqrt (Nat.sub_le ..)
  have height : J ≤ (9*N/8).sqrt - ((N-1).sqrt+1) := by omega
  have width : 2^1022 ≤ (N/8).sqrt := Nat.le_sqrt.mpr (by
    have e : 8*(2^1022 * 2^1022) = (2:ℕ)^2047 := by decide +kernel
    omega)
  exact (by decide +kernel : 2^2043 ≤ 8*J*2^1022).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ height) width)

/-- Choosing the smaller member of each pair leaves representatives which,
together with their partners, cover the original set. Fixed points are allowed. -/
theorem swap_orbits_cover {α : Type*} [LinearOrder α] (s : Finset α) (f : α → α)
    (swap : ∀ x ∈ s, f (f x) = x) :
    s.card ≤ 2*(s.image (fun x => min x (f x))).card := by
  classical
  let reps := s.image (fun x => min x (f x))
  have cover : s ⊆ reps ∪ reps.image f := by
    intro x hx
    have hit : min x (f x) ∈ reps := Finset.mem_image_of_mem _ hx
    by_cases h : x ≤ f x
    · exact Finset.mem_union_left _ (by rwa [min_eq_left h] at hit)
    · rw [min_eq_right (le_of_not_ge h)] at hit
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f x, hit, swap x hx⟩)
  have total := (Finset.card_le_card cover).trans (Finset.card_union_le ..)
  have image := Finset.card_image_le (s := reps) (f := f)
  change s.card ≤ 2*reps.card
  omega

set_option exponentiation.threshold 4096 in
/-- Regardless of the radix policy, a full search through swap orbits at
this uniform width needs over 2^676 orbits on every target-size input.
Each orbit covers at most two of the totient-many unit residues. -/
theorem midpoint_weight_orbit_budget {N R C : ℕ} (size : 2^2047 ≤ N)
    (width : 8*((9*N/8).sqrt - ((N-1).sqrt+1))*(N/8).sqrt < R^3)
    (cover : R.totient ≤ 2*C) : 2^676 < C := by
  have vol := (midpoint_weight_volume size).trans_lt width
  by_contra! small
  have hphi := cover.trans (Nat.mul_le_mul_left 2 small)
  by_cases bounded : R ≤ 2^1366
  · have pos : 0 < R := by by_contra! hr; simp [Nat.eq_zero_of_le_zero hr] at vol
    have ratio := quotientBudget_wheel_ratio pos bounded
    have upper := Nat.pow_le_pow_left (ratio.le.trans (Nat.mul_le_mul_left 13 hphi)) 3
    have check : (13*(2*2^676))^3 ≤ (2:ℕ)^2043 := by decide +kernel
    exact (not_lt_of_ge (upper.trans check)) vol
  · have limit := quotientBudget_totient_square R
    have upper := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hphi 2)
    exact bounded ((limit.trans upper).trans (by decide +kernel))

end PrimeFactors
