import PrimeFactors.JacobiPeriodProbe
import PrimeFactors.DiscriminantStride

/-! Which working periods also recover the sum through the existing
square-class decoder? -/
namespace PrimeFactors.JacobiPeriodScales

open JacobiMomentPeriod JacobiPeriodProbe

/-- At a multiple mR, removing the common factor R leaves m*h²=g².
Thus the useful multiples are indexed by the positive divisors of g. -/
theorem square_at_multiple {R g m : ℕ} (hR : 0 < R) (hg : 0 < g) :
    (∃ h : ℕ, (R*m)*h^2 = R*g^2) ↔ ∃ k : ℕ, k ∣ g ∧ m = k^2 := by
  constructor
  · rintro ⟨h,eq⟩
    have reduced : m*h^2 = g^2 := Nat.eq_of_mul_eq_mul_left hR (by simpa [mul_assoc] using eq)
    have hd : h ∣ g := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
      (show h^2 ∣ g^2 by rw [← reduced]; exact dvd_mul_left ..)
    obtain ⟨k,hk⟩ := hd
    have pos : 0 < h^2 := by
      have h0 : h ≠ 0 := by rintro rfl; simp at hk; omega
      positivity
    refine ⟨k, ⟨h, hk.trans (Nat.mul_comm ..)⟩, Nat.eq_of_mul_eq_mul_right pos ?_⟩
    rw [reduced,hk]
    ring
  · rintro ⟨k,⟨h,rfl⟩,rfl⟩
    exact ⟨h, by ring⟩

/-- On balanced inputs, a scale gives the correct sum exactly when the
predecessor product divided by that scale is a square with zero remainder. -/
theorem sum_iff_square {P Q t : ℕ} (pos : 0 < P) (ord : P ≤ Q)
    (bal : Q+1 ≤ 2*(P+1)) (ht : 0 < t) :
    predecessorSquareSum ((P+1)*(Q+1)) t = (P+1)+(Q+1) ↔ ∃ y : ℕ, t*y^2 = P*Q := by
  constructor
  · let n := (P+1)*(Q+1)
    let y := if t=1 then n.sqrt-1 else (n/t).sqrt
    intro good
    change n+1-t*y^2 = (P+1)+(Q+1) at good
    have decomp : n+1 = (P+1)+(Q+1)+P*Q := by dsimp only [n]; ring
    exact ⟨y, by omega⟩
  · rintro ⟨y,hy⟩
    exact predecessorSquareSum_correct pos ord bal ht hy.symm

/-- Among *all* valid periods mR, exactly the squares of divisors of the common
predecessor g are useful multipliers for the factor-sum decoder. -/
theorem useful_multiples {g a b m : ℕ} (hg : 0 < g) (ha : 0 < a) (ab : a ≤ b)
    (bal : g*b+1 ≤ 2*(g*a+1)) (hm : 0 < m) :
    predecessorSquareSum ((g*a+1)*(g*b+1)) ((a*b)*m) = (g*a+1)+(g*b+1) ↔
      ∃ k : ℕ, k ∣ g ∧ m = k^2 := by
  have hR := Nat.mul_pos ha (ha.trans_le ab)
  rw [sum_iff_square (Nat.mul_pos hg ha) (Nat.mul_le_mul_left g ab) bal (Nat.mul_pos hR hm),
    show g*a*(g*b) = a*b*g^2 by ring]
  exact square_at_multiple hR hg

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Screening for valid periods can discard a successful sum guess. At 221,
scale 3 gives the true sum although the stride period must be a multiple of
12. Conversely, 24 is a period and gives the wrong sum. -/
theorem opposite_outcomes_221 :
    ¬ AllOffsets (completeEven (13*17)) ((13*17-1)/2) 3 ∧
    predecessorSquareSum 221 3 = 30 ∧
    AllOffsets (completeEven (13*17)) ((13*17-1)/2) 24 ∧
    predecessorSquareSum 221 24 = 6 := by
  rw [canonical_period (by decide) (by decide) (by decide),
    canonical_period (by decide) (by decide) (by decide)]
  decide

/-- The square-totient control used to distinguish scale one from period 400. -/
theorem square_control_factors : ExactFactorization 14647 [97,151] := by
  norm_num [ExactFactorization]

end PrimeFactors.JacobiPeriodScales
