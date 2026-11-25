import PrimeFactors.QuarticFactorLane

namespace PrimeFactors.QuarticFactorLane

/-- A positive pair in the reflected residue class gives a negative integer root of the
original polynomial. The certificate is evaluated at the two signed factor coordinates. -/
theorem reflected_mem_candidates {w : Weights} {N R u x y : ℤ} (pos : N ≠ 0)
    (nonzero : w.a ≠ 0 ∨ w.b ≠ 0 ∨ w.c ≠ 0 ∨ w.d ≠ 0 ∨ w.e ≠ 0) (cop : IsCoprime R N)
    (divisions : conditions w N R u) (lane : x ≡ -u [ZMOD R]) (pair : x*y = N)
    (short : |trace w (-x) (-y)| < R^4) : -x ∈ candidates w N :=
  mem_candidates pos nonzero cop divisions (by simpa using lane.neg)
    (by simpa only [neg_mul_neg] using pair : (-x)*(-y) = N) short

/-- One quartic yields at most four candidate magnitudes across both signs together. -/
theorem signed_candidates_card (w : Weights) (N : ℤ) :
    ((candidates w N).image Int.natAbs).card ≤ 4 :=
  Finset.card_image_le.trans (candidates_card w N)

/-- Exactly one nonfixed unordered pair has coordinate sum below the radix. Equality
retains a pair whose two digits are already each other's negatives. -/
theorem reflected_sum {u v R : ℕ} (hu : u ≤ R) (hv : v ≤ R) :
    (R-u)+(R-v) < R ↔ R < u+v := by omega

end PrimeFactors.QuarticFactorLane
