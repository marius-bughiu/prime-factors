import PrimeFactors.Fermat

namespace PrimeFactors

/-- The integer upper root of the quadratic with constant term `N` and
estimated factor sum `H`. Both the square root and the division round down. -/
def estimatedLargerFactor (N H : ℕ) : ℕ :=
  (H + (H^2-4*N).sqrt)/2

/-- Rounding an upper sum estimate produces an upper estimate of the larger
factor. Its error satisfies the full quadratic inequality, including equal
factors, with no additive rounding loss. -/
theorem approximateTotient_upper_root {p q H E : ℕ} (ordered : p ≤ q)
    (lower : p+q ≤ H) (upper : H ≤ p+q+E) :
    let U := estimatedLargerFactor (p*q) H
    q ≤ U ∧ (U-q)*(U-p) ≤ E*U := by
  let U := estimatedLargerFactor (p*q) H
  let D := H^2-4*(p*q)
  have identity : (q-p)^2+4*(p*q)=(p+q)^2 := by
    obtain ⟨g,rfl⟩ := Nat.exists_eq_add_of_le ordered
    simp
    ring
  have sq := Nat.pow_le_pow_left lower 2
  have disc : D+4*(p*q)=H^2 := by dsimp [D]; omega
  have baseGap : q-p ≤ D.sqrt := Nat.le_sqrt'.mpr (by omega)
  have below : q ≤ U := by
    change q ≤ (H+D.sqrt)/2
    omega
  refine ⟨below,?_⟩
  have rootBound : 2*U ≤ H+D.sqrt := by
    change 2*((H+D.sqrt)/2) ≤ H+D.sqrt
    omega
  have quadratic : U^2+p*q ≤ H*U := by
    by_cases near : 2*U ≤ H
    · have mono : U+q ≤ H := by omega
      obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le below
      rw [hd] at mono ⊢
      nlinarith only [Nat.mul_le_mul_left d mono, Nat.mul_le_mul_right q lower]
    · have high : H ≤ 2*U := by omega
      have offset : 2*U-H ≤ D.sqrt := by omega
      have hs := (Nat.pow_le_pow_left offset 2).trans (Nat.sqrt_le' D)
      have recover := Nat.sub_add_cancel high
      nlinarith only [hs,disc,congrArg (fun n : ℕ => n^2) recover,
        congrArg (fun n : ℕ => H*n) recover]
  obtain ⟨g,hg⟩ := Nat.exists_eq_add_of_le ordered
  obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le below
  change (U-q)*(U-p) ≤ E*U
  have du : U-q=z := by omega
  have dp : U-p=g+z := by omega
  have total := quadratic.trans (Nat.mul_le_mul_right U upper)
  rw [du,dp,hz,hg] at *
  nlinarith only [total]

/-- Dropping the squared-error term gives the factor-gap bound. -/
theorem approximateTotient_gap_bound {p q H E : ℕ} (ordered : p ≤ q)
    (lower : p+q ≤ H) (upper : H ≤ p+q+E) :
    let U := estimatedLargerFactor (p*q) H
    (U-q)*(q-p) ≤ E*U := by
  obtain ⟨below,quad⟩ := approximateTotient_upper_root ordered lower upper
  exact (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right below p)).trans quad

/-- A public interval for the larger factor remains valid when the two
factors coincide. -/
theorem approximateTotient_sqrt_interval {p q H E : ℕ} (ordered : p ≤ q)
    (lower : p+q ≤ H) (upper : H ≤ p+q+E) :
    let U := estimatedLargerFactor (p*q) H
    U-(E*U).sqrt ≤ q ∧ q ≤ U := by
  let U := estimatedLargerFactor (p*q) H
  obtain ⟨below,quad⟩ := approximateTotient_upper_root ordered lower upper
  have compare : U-q ≤ U-p := Nat.sub_le_sub_left ordered U
  have error : U-q ≤ (E*U).sqrt :=
    Nat.le_sqrt.mpr ((Nat.mul_le_mul_left (U-q) compare).trans quad)
  change U-(E*U).sqrt ≤ q ∧ q ≤ U
  exact ⟨by omega,below⟩

/-- With a positive public denominator, integer division gives a second
interval. Both endpoints use only the product, the estimated sum and its
stated error cap. -/
theorem approximateTotient_div_interval {p q H E : ℕ} (ordered : p ≤ q)
    (lower : p+q ≤ H) (upper : H ≤ p+q+E)
    (separated : (p*q).sqrt < estimatedLargerFactor (p*q) H) :
    let U := estimatedLargerFactor (p*q) H
    U - E*U/(U-(p*q).sqrt) ≤ q ∧ q ≤ U := by
  let U := estimatedLargerFactor (p*q) H
  obtain ⟨below,quad⟩ := approximateTotient_upper_root ordered lower upper
  have small : p ≤ (p*q).sqrt := Nat.le_sqrt.mpr (Nat.mul_le_mul_left p ordered)
  have denom : 0 < U-(p*q).sqrt := Nat.sub_pos_of_lt separated
  have error : U-q ≤ E*U/(U-(p*q).sqrt) :=
    (Nat.le_div_iff_mul_le denom).mpr ((Nat.mul_le_mul_left (U-q)
      (Nat.sub_le_sub_left small U)).trans quad)
  change U-E*U/(U-(p*q).sqrt) ≤ q ∧ q ≤ U
  exact ⟨by omega,below⟩

private theorem predecessorProduct_add_sum {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (p-1)*(q-1)+(p+q)=p*q+1 := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  simp
  ring

/-- A two-sided approximation to the predecessor product gives the upper
sum estimate required by the root bounds. Adding the tolerance before
subtracting the approximation keeps all arithmetic in natural numbers. -/
theorem approximateTotient_sum_estimate {p q v E : ℕ} (hp : 0 < p) (hq : 0 < q)
    (lo : (p-1)*(q-1) ≤ v+E) (hi : v ≤ (p-1)*(q-1)+E) :
    let H := p*q+1+E-v
    p+q ≤ H ∧ H ≤ p+q+2*E := by
  have h := predecessorProduct_add_sum hp hq
  dsimp
  omega

/-- For factors within a ratio of two and tolerance at most the square root
of their product, a scaled square near the predecessor product has at most
three possible square roots for each positive scale. -/
theorem approximateTotient_square_candidates {p q d y E : ℕ} (hp : 0 < p)
    (ordered : p ≤ q) (balanced : q ≤ 2*p) (hd : 0 < d)
    (budget : E ≤ (p*q).sqrt) (lo : (p-1)*(q-1) ≤ d*y^2+E)
    (hi : d*y^2 ≤ (p-1)*(q-1)+E) :
    let t := ((p*q)/d).sqrt
    t-2 ≤ y ∧ y ≤ t := by
  have rq : (p*q).sqrt ≤ q := by
    simpa only [Nat.sqrt_eq] using Nat.sqrt_le_sqrt (Nat.mul_le_mul_right q ordered)
  have eqSum := predecessorProduct_add_sum hp (hp.trans_le ordered)
  have prod : d*y^2 ≤ p*q := by omega
  refine ⟨?_, Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le hd).mpr (by simpa [mul_comm] using prod))⟩
  suffices upper : p*q < d*(y+3)^2 by
    have := Nat.sqrt_lt'.mpr ((Nat.div_lt_iff_lt_mul hd).mpr (by simpa [mul_comm] using upper))
    omega
  by_cases small : p ≤ 2
  · have pq : p*q ≤ 8 := Nat.mul_le_mul small (by omega : q ≤ 4)
    obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le (show 1 ≤ d by omega)
    rw [hz]
    nlinarith only [pq, Nat.zero_le y, Nat.zero_le (y^2), Nat.zero_le z,
      Nat.zero_le (z*y), Nat.zero_le (z*y^2)]
  have h₁ : p-1=(p-2)+1 := by omega
  have h₂ : q-1=(q-2)+1 := by omega
  have h₃ : p=(p-2)+2 := by omega
  have h₄ : q=(q-2)+2 := by omega
  have near : (p-2)*(q-2) ≤ d*y^2 := by
    rw [h₁,h₂] at lo
    nlinarith only [lo, budget.trans rq, h₃, h₄, show 3 ≤ p by omega]
  have square : (p-2)^2 ≤ (d*y)^2 := calc
    _ ≤ (p-2)*(q-2) := by
      rw [pow_two]
      exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right ordered _)
    _ ≤ d*y^2 := near
    _ ≤ (d*y)^2 := by
      rw [mul_pow]
      exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by decide) d)
  have side := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp square
  have expand : p*q=(p-2)*(q-2)+2*(p-2)+2*(q-2)+4 := by
    calc p*q = ((p-2)+2)*((q-2)+2) := congrArg₂ (· * ·) h₃ h₄
         _ = _ := by ring
  nlinarith only [expand, near, side, h₃, h₄, balanced, hd]

end PrimeFactors
