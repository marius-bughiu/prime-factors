import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeFactors.FareyAllocation

private theorem endpoint {p q a b A B : ℤ}
    (side : (a*p≤b*q ∧ a*B≤b*A ∧ B*q≤A*p) ∨ (b*q≤a*p ∧ b*A≤a*B ∧ A*p≤B*q))
    (pp : 0≤p) (qp : 0≤q) (aa : 0≤a) (bp : 0≤b) (ap : 0≤A) (bb : 0≤B) :
    (a*p+b*q)^2*A*B ≤ (p*q)*(a*B+b*A)^2 := by
  have area : 0 ≤ (A*p-B*q)*((b*A)*(b*q)-(a*B)*(a*p)) := by
    rcases side with ⟨h₁,h₂,h₃⟩ | ⟨h₁,h₂,h₃⟩
    · exact mul_nonneg (sub_nonneg.mpr h₃) (sub_nonneg.mpr
        (mul_le_mul h₂ h₁ (mul_nonneg aa pp) (mul_nonneg bp ap)))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h₃) (sub_nonpos.mpr
        (mul_le_mul h₂ h₁ (mul_nonneg bp qp) (mul_nonneg aa bb)))
  nlinarith only [area]

/-- A rational cut at either side of a slope is priced by an exact integer inequality.
If both endpoints fit below the first omitted label, so does every balanced sum in its cell. -/
theorem cell {p q a b A B C D T : ℕ} (bp : 0 < B) (dp : 0 < D) (ap : 0 < A) (cp : 0 < C)
    (leftCenter : A*b ≤ a*B) (rightCenter : a*D ≤ C*b)
    (leftTrue : A*p ≤ q*B) (rightTrue : q*D ≤ C*p)
    (leftCert : p*q*(a*B+b*A)^2 < A*B*T^2)
    (rightCert : p*q*(a*D+b*C)^2 < C*D*T^2) : a*p+b*q < T := by
  have compare (X Y : ℕ) (xp : 0<X) (yp : 0<Y)
      (cert : p*q*(a*Y+b*X)^2 < X*Y*T^2)
      (side : (a*p≤b*q ∧ a*Y≤b*X ∧ Y*q≤X*p) ∨ (b*q≤a*p ∧ b*X≤a*Y ∧ X*p≤Y*q)) :
      a*p+b*q < T := by
    have eb : (a*p+b*q)^2*X*Y ≤ p*q*(a*Y+b*X)^2 := by
      zify at side ⊢
      exact endpoint side (by positivity) (by positivity) (by positivity) (by positivity)
        (by positivity) (by positivity)
    by_contra! rev
    have h := Nat.mul_le_mul_left (X*Y) (Nat.pow_le_pow_left rev 2)
    nlinarith only [h,eb,cert]
  rcases le_total (b*q) (a*p) with l | r
  · exact compare A B ap bp leftCert (Or.inr ⟨l,by simpa [mul_comm] using leftCenter,
      by simpa [mul_comm] using leftTrue⟩)
  · exact compare C D cp dp rightCert (Or.inl ⟨r,by simpa [mul_comm] using rightCenter,
      by simpa [mul_comm] using rightTrue⟩)

/-- At an interior cut for adjacent or skipped slopes, the two normalized weighted sums agree.
The cut is a ratio of integers even when the individual interval endpoints are irrational. -/
theorem interior_cut (a b c d T U : ℤ) :
    let A := c*T-a*U
    let B := b*U-d*T
    a*B+b*A = (b*c-a*d)*T ∧ c*B+d*A = (b*c-a*d)*U := by
  dsimp
  constructor <;> ring

end PrimeFactors.FareyAllocation
