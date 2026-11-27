import PrimeFactors.IntermediateShiftCount
import PrimeFactors.IntervalGap

/-! A weighted divisor exclusion applied to a known totient certifies a contiguous range
of shifts that cannot add a hit. The application to a semiprime requires its private factors. -/
namespace PrimeFactors.IntermediatePrivateShiftWindow

/-- An integer strictly between consecutive nonnegative squares cannot be a square. -/
private theorem nonsquare {s : ℕ} {T : ℤ} (lo : (s:ℤ)^2<T) (hi : T<((s:ℤ)+1)^2) :
    ¬ IsSquare T := by
  rintro ⟨z,eq⟩
  rw [←pow_two] at eq
  by_cases below : |z|≤(s:ℤ)
  · have le := pow_le_pow_left₀ (abs_nonneg z) below 2
    rw [sq_abs] at le
    omega
  · have gt : (s:ℤ)+1≤|z| := by omega
    have ge := pow_le_pow_left₀ (by positivity : (0:ℤ)≤(s:ℤ)+1) gt 2
    rw [sq_abs] at ge
    omega

/-- Endpoint arithmetic and one nonsquare certify the absence of every divisor in the
entire interval (D,D+K]. The product F may be even and need not come with a factorization. -/
theorem no_divisor {F D K a b m r s : ℕ}
    (ml : (m-1)^2<4*a*b*F) (mu : 4*a*b*F≤m^2) (rad : r^2≤2*m)
    (left : m+1≤2*a*(D+1)+r) (right : 2*a*(D+K)≤m+1+r)
    (lo : (s:ℤ)^2<(m:ℤ)^2-4*(a:ℤ)*b*F)
    (hi : (m:ℤ)^2-4*(a:ℤ)*b*F<((s:ℤ)+1)^2)
    {d : ℕ} (dl : D<d) (du : d≤D+K) : ¬d∣F := by
  have hm : ceilSqrt (4*a*b*F)=m := by
    apply le_antisymm (ceilSqrt_le_iff.mpr mu)
    by_contra! h
    have short := ceilSqrt_le_iff.mp (show ceilSqrt (4*a*b*F)≤m-1 by omega)
    omega
  apply weightedBand_excludes (a:=a) (b:=b)
  · rw [hm]
    exact nonsquare lo hi
  · rw [hm]
    exact weightedBand_of_bounds rad (left.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ dl) _))
      ((Nat.mul_le_mul_left _ du).trans right)

/-- Once the private deficit and totient are known, show the claimed shift exclusion for
every possible exponent simultaneously. -/
theorem empty {N F D K : ℕ} (fp : 0<F) (fn : F<N) (deficit : N-F=D) (cap : K≤D)
    (clear : ∀ d, D<d → d≤D+K → ¬d∣F) :
    ∀ k, 0<k → k≤K → ¬ IntermediateShiftCount.Extra N F k := by
  intro k kp within hit
  have div := ((IntermediateShiftCount.exact_criterion fp fn kp (by omega)).mp hit).1
  rw [deficit] at div
  exact clear (D+k) (by omega) (by omega) div

end PrimeFactors.IntermediatePrivateShiftWindow
