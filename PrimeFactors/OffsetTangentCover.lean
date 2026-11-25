import PrimeFactors.OffsetArcLines

namespace PrimeFactors.OffsetTangentCover

/-- The integer tangent uses the floor of the height at the left endpoint. -/
theorem tangent_identity {A u e P x w : ℤ}
    (base : A^2-P=u^2+e) (curve : w^2=(A+x)^2-P) :
    (u*w-u^2-A*x)*(u*w+u^2+A*x)=u^2*e-(P+e)*x^2 := by
  linear_combination u^2*curve + (u^2-x^2)*base

/-- A signed integer error enclosure, including rounding the starting root down. -/
theorem tangent_bounds {A u e P x w X : ℤ} (ap : 0≤A) (up : 0<u)
    (ep : 0≤e) (er : e≤2*u) (pp : 0≤P) (xp : 0≤x) (cap : x≤X) (wp : 0≤w)
    (base : A^2-P=u^2+e) (curve : w^2=(A+x)^2-P) :
    -((P+2*u)*X^2/(2*u^2)) ≤ u*w-u^2-A*x ∧ u*w-u^2-A*x ≤ u := by
  let V := u*w-u^2-A*x
  let B := u*w+u^2+A*x
  have uv : u≤w := by
    apply (sq_le_sq₀ up.le wp).mp
    nlinarith only [base,curve,ep,mul_nonneg ap xp,sq_nonneg x]
  have bp : 2*u^2≤B := by
    dsimp [B]
    nlinarith only [mul_le_mul_of_nonneg_left uv up.le,mul_nonneg ap xp]
  have two : 0<2*u^2 := by positivity
  have id : V*B=u^2*e-(P+e)*x^2 := tangent_identity base curve
  have term := mul_le_mul (show P+e≤P+2*u by omega)
    (pow_le_pow_left₀ xp cap 2) (sq_nonneg x) (by omega : 0≤P+2*u)
  constructor
  · change -((P+2*u)*X^2/(2*u^2)) ≤ V
    have goal : -V ≤ (P+2*u)*X^2/(2*u^2) := by
      apply (Int.le_ediv_iff_mul_le two).2
      by_cases v : 0≤V
      · exact (mul_nonpos_of_nonpos_of_nonneg (by omega) two.le).trans
          (mul_nonneg (by omega) (sq_nonneg X))
      · nlinarith only [id,term,mul_nonneg (sq_nonneg u) ep,
          mul_le_mul_of_nonpos_left bp (by omega : V≤0)]
    omega
  · change V≤u
    by_contra! h
    have high := mul_lt_mul_of_pos_right h two
    have keep := mul_le_mul_of_nonneg_left bp (show 0≤V by omega)
    nlinarith only [high,keep,id,mul_le_mul_of_nonneg_left er (sq_nonneg u),
      mul_nonneg (show 0≤P+e by omega) (sq_nonneg x)]

/-- Two integer width tests put the normalized tangent strip inside the one-line bound. -/
theorem thin {P u δ W M : ℤ} (up : 0<u) (wp : 0≤W)
    (rounding : 8*W≤M) (curvature : 4*(P+2*u)*δ^2*W^3≤M*u^3) :
    4*W*(u+(P+2*u)*(δ*W)^2/(2*u^2)) ≤ u*M := by
  have den : 0<2*u^2 := by positivity
  have div := Int.ediv_mul_le ((P+2*u)*(δ*W)^2) den.ne'
  have scaled := mul_le_mul_of_nonneg_left div (show 0≤4*W by omega)
  apply (mul_le_mul_iff_of_pos_left den).mp
  nlinarith only [scaled,curvature,mul_le_mul_of_nonneg_right rounding
    (show 0≤u^3 by positivity)]

/-- The same width works at every larger floor root in the epoch. -/
theorem advance {P u v δ W M : ℤ} (pp : 0≤P) (up : 0<u) (uv : u≤v)
    (mp : 0≤M) (curvature : 4*(P+2*u)*δ^2*W^3≤M*u^3) :
    4*(P+2*v)*δ^2*W^3≤M*v^3 := by
  have cube := pow_le_pow_left₀ up.le uv 3
  have square := pow_le_pow_left₀ up.le uv 2
  have exchange : (P+2*v)*u^3 ≤ (P+2*u)*v^3 := by
    nlinarith only [mul_le_mul_of_nonneg_left cube pp,
      mul_le_mul_of_nonneg_left square (mul_nonneg up.le (up.le.trans uv))]
  apply (mul_le_mul_iff_of_pos_left (show 0<P+2*u by omega)).mp
  nlinarith only [mul_le_mul_of_nonneg_right curvature (show 0≤P+2*v by omega),
    mul_le_mul_of_nonneg_left exchange mp]

/-- For every possible integer root on this arc the lifted height coordinate
lies on one public line, with the sign already incorporated in r and β. -/
theorem one_line {A u e P δ r β : ℤ} {M W : ℕ}
    (ap : 0≤A) (up : 0<u) (ep : 0≤e) (er : e≤2*u) (pp : 0≤P)
    (dp : 0≤δ) (mp : 0<M) (wp : 0<W) (base : A^2-P=u^2+e)
    (rounding : 8*(W:ℤ)≤M) (curvature : 4*(P+2*u)*δ^2*(W:ℤ)^3≤(M:ℤ)*u^3) :
    ∃ (q : ℕ) (p t : ℤ), 1≤q ∧ q≤2*W ∧ ∀ i y w : ℤ, 0 ≤ i → i ≤ W → 0 ≤ w →
      w = r+β*i+(M:ℤ)*y → w^2 = (A+δ*i)^2-P → (q:ℤ)*y-p*i=t := by
  let B := (P+2*u)*(δ*(W:ℤ))^2/(2*u^2)
  have Bpos : 0≤B := Int.ediv_nonneg (mul_nonneg (by omega) (sq_nonneg _)) (by positivity)
  have un : (u.toNat:ℤ)=u := Int.toNat_of_nonneg up.le
  have cast : ((u.toNat*M:ℕ):ℤ)=u*(M:ℤ) := by push_cast; rw [un]
  have weak := thin up (show 0≤(W:ℤ) by positivity) rounding curvature
  obtain ⟨q,p,t,qp,qw,cover⟩ := OffsetArcLines.public_line
    (D:=u.toNat*M) (W:=W) (A:=A*δ-u*β) (l:=u^2-B-u*r) (u:=u^2+u-u*r)
    (Nat.mul_pos (by omega) mp) wp (by omega) (by rw [cast]; dsimp [B] at *; linarith only [weak])
  refine ⟨q,p,t,qp,qw,?_⟩
  intro i y w ip iw positive label curve
  have bound := tangent_bounds ap up ep er pp (mul_nonneg dp ip)
    (mul_le_mul_of_nonneg_left iw dp) positive base curve
  rw [label] at bound
  apply cover i y ip iw <;> rw [cast] <;> try dsimp [B]
  all_goals linarith only [bound.1,bound.2]

end PrimeFactors.OffsetTangentCover
