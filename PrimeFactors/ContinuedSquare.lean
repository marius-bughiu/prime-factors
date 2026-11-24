import PrimeFactors.PredecessorCount
import Mathlib.NumberTheory.DiophantineApproximation.Basic

namespace PrimeFactors

/-- Recover the common scale of the two indices from a candidate convergent
of the public ratio `s/R`, where `s = floor(sqrt N)` and `R = N - s²`.
The candidate numerator and denominator are `u` and `v`. -/
def continuedSquareScale (s R u v : ℕ) : ℕ :=
  let w := (4*u+v).sqrt
  let C := s-u*(R/v)
  ((w^2+4*u*(C-1)).sqrt-w)/(2*u)

private theorem continuedSquare_legendre {s R u v C : ℕ} (hv : 0 < v)
    (cop : Nat.Coprime u v) (identity : v*s=u*R+v*C) (small : 2*C*v^2 < R) :
    ∃ n, let f := ((s : ℝ)/R).convergent n
         f.num.natAbs=u ∧ f.den=v := by
  have hpos : 0 < (v : ℤ) := by exact_mod_cast hv
  have reduced : (u : ℤ).natAbs.Coprime (v : ℤ).natAbs := by simpa using cop
  have num : ((u : ℚ)/v).num=(u : ℤ) := by
    simpa using Rat.num_div_eq_of_coprime hpos reduced
  have den : ((u : ℚ)/v).den=v := by
    apply Int.ofNat_inj.mp
    simpa only [Int.cast_natCast] using Rat.den_div_eq_of_coprime hpos reduced
  have vpos : 0 < (v : ℝ) := by exact_mod_cast hv
  have Rpos : 0 < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
  have cross : (v : ℝ)*s=u*R+v*C := by exact_mod_cast identity
  have err : (s : ℝ)/R-(u : ℝ)/v=(C : ℝ)/R := by
    field_simp
    nlinarith only [congrArg (fun z : ℝ => z*R) cross]
  have estimate : |(s : ℝ)/R-((u : ℚ)/v : ℚ)| < 1/(2*((((u : ℚ)/v).den : ℝ))^2) := by
    rw [den, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, err,
      abs_of_nonneg (by positivity)]
    apply (div_lt_div_iff₀ Rpos (by positivity)).mpr
    exact_mod_cast (by nlinarith only [small] : C*(2*v^2)<1*R)
  obtain ⟨n,hn⟩ := Real.exists_rat_eq_convergent estimate
  exact ⟨n,by simp [← hn,num,den]⟩

/-- On the family with indices `ga` and `g(a+d)`, one convergent of an
input-only rational gives both the reduced index ratio invariant and the
common scale. The final expression recovers the exact factor sum. -/
theorem continuedSquare_recovery {a d g t : ℕ} (ha : 0 < a) (hd : 0 < d)
    (cop : a.Coprime d) (balance : d^2 ≤ 2*a*(a+d))
    (separation : 2*((g*a+1)*(g*(a+d)+1))*(d^2)^2 < (g*d)^2*t) :
    let p := nearSquareForm (g*a) (t+1)
    let q := nearSquareForm (g*(a+d)) (t+1)
    let N := p*q
    let s := N.sqrt
    let R := N-s^2
    ∃ n, let f := ((s : ℝ)/R).convergent n
         let u := f.num.natAbs
         let v := f.den
         let scale := continuedSquareScale s R u v
         u=a*(a+d) ∧ v=d^2 ∧ scale=g ∧ correctedPredecessorSum N (scale*v.sqrt)=p+q := by
  let p := nearSquareForm (g*a) (t+1)
  let q := nearSquareForm (g*(a+d)) (t+1)
  let N := p*q
  let s := N.sqrt
  let R := N-s^2
  let u := a*(a+d)
  let v := d^2
  let C := (g*a+1)*(g*(a+d)+1)
  have scaled : (g*d)^2 ≤ 2*(g*a)*(g*a+g*d) := by
    nlinarith only [Nat.mul_le_mul_left (g^2) balance]
  have root : s=nearSquareCenter (g*a) (g*d) (t+1)+1 := by
    simpa only [s,N,p,q,Nat.mul_add] using nearSquare_floor (g*a) (g*d) t scaled
  have residual : R=(g*d)^2*t := by
    change N-s^2=_
    rw [root]
    dsimp [N,p,q]
    rw [Nat.mul_add,nearSquare_residual,Nat.add_sub_cancel_left]
  have ratio : v*s=u*R+v*C := by
    rw [root,residual]
    dsimp [v,u,C,nearSquareCenter]
    ring
  have reduced : u.Coprime v := by
    simpa only [u,v,Nat.coprime_pow_right_iff (by decide : 0 < 2),
      Nat.coprime_mul_iff_left,Nat.coprime_add_self_left,and_self] using cop
  have vpos : 0<v := pow_pos hd _
  obtain ⟨n,hn,hdn⟩ := continuedSquare_legendre vpos reduced ratio
    (by simpa only [residual,C,v] using separation)
  refine ⟨n,hn,hdn,?_⟩
  dsimp only
  change continuedSquareScale s R _ _ = g ∧ _
  rw [hn,hdn]
  have divided : R/v=g^2*t := by
    rw [residual]
    change (g*d)^2*t/d^2=_
    rw [mul_pow,mul_right_comm,Nat.mul_div_cancel _ vpos]
  have intercept : s-u*(R/v)=C := by
    apply Nat.sub_eq_of_eq_add
    rw [root,divided]
    dsimp [u,C,nearSquareCenter]
    ring
  have widths : (4*u+v).sqrt=2*a+d := by
    rw [show 4*u+v=(2*a+d)^2 by dsimp [u,v]; ring, Nat.sqrt_eq']
  have disc : ((2*a+d)^2+4*u*(C-1)).sqrt=2*u*g+(2*a+d) := by
    have minus : C-1=g^2*u+(2*a+d)*g := by
      apply Nat.sub_eq_of_eq_add
      dsimp [u,C]
      ring
    rw [minus,show (2*a+d)^2+4*u*(g^2*u+(2*a+d)*g)=(2*u*g+(2*a+d))^2 by ring,
      Nat.sqrt_eq']
  have scale : continuedSquareScale s R u v=g := by
    rw [continuedSquareScale,widths,intercept,disc,Nat.add_sub_cancel,
      Nat.mul_div_cancel_left g (show 0<2*u by dsimp [u]; positivity)]
  refine ⟨scale,?_⟩
  rw [scale,show v.sqrt=d from Nat.sqrt_eq' d]
  simpa only [N,p,q,Nat.mul_add] using nearSquare_sum (g*a) (g*d) t scaled

end PrimeFactors
