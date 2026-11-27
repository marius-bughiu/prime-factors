import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

/-! Candidate list for a supplied modular root. The rational bracket and
the root are input to this oracle. -/
namespace PrimeFactors.RectangularFareyOracle

private theorem primitive_scale {x y k v z : ℤ} (prim : IsCoprime x y)
    (kp : 0≤k) (hx : x=k*v) (hy : y=k*z) : k=1 := by
  obtain ⟨u,w,bez⟩ := prim
  have unit : IsUnit k := isUnit_iff_dvd_one.mpr ⟨u*v+w*z,by
    rw [hx,hy] at bez
    linear_combination -bez⟩
  rcases Int.isUnit_iff.mp unit with pos|neg <;> omega

/-- Every primitive point of the rectangular strip is one of the two
Farey endpoint vectors. Endpoints can themselves fail the height test.
The statement permits non-strict bracketing of r/N. -/
theorem classify {N r H B a b c d m y : ℤ} (np : 0<N) (hp : 0≤H)
    (bp : 0<b) (dp : 0<d) (bB : b≤B) (dB : d≤B) (sum : B<b+d)
    (det : b*c-a*d=1) (left : a*N≤b*r) (right : d*r≤c*N)
    (area : H*B<N) (yp : 0<y) (yB : y≤B)
    (near : |r*y-m*N|≤H) (prim : IsCoprime (r*y-m*N) y) :
    (m=a ∧ y=b) ∨ (m=c ∧ y=d) := by
  let l := c*y-d*m
  let u := b*m-a*y
  have yl : y=b*l+d*u := by dsimp [l,u]; linear_combination -y*det
  have ml : m=a*l+c*u := by dsimp [l,u]; linear_combination -m*det
  obtain ⟨down,up⟩ := abs_le.mp near
  have un : 0≤u := by
    by_contra! bad
    have um := mul_le_mul_of_nonneg_left (show u≤ -1 by omega) np.le
    dsimp [u] at um
    nlinarith only [um,mul_le_mul_of_nonneg_left up bp.le,
      mul_le_mul_of_nonneg_right left yp.le,mul_le_mul_of_nonneg_left bB hp,area]
  have ln : 0≤l := by
    by_contra! bad
    have lm := mul_le_mul_of_nonneg_left (show l≤ -1 by omega) np.le
    dsimp [l] at lm
    nlinarith only [lm,mul_le_mul_of_nonneg_left down dp.le,
      mul_le_mul_of_nonneg_right right yp.le,mul_le_mul_of_nonneg_left dB hp,area]
  by_cases lz : l=0
  · rw [lz,mul_zero,zero_add] at yl ml
    have ps := primitive_scale (v:=r*d-c*N) (z:=d) prim un
      (by rw [yl,ml]; ring) (by rw [yl]; ring)
    right
    simpa only [ps,mul_one] using And.intro ml yl
  by_cases uz : u=0
  · rw [uz,mul_zero,add_zero] at yl ml
    have ps := primitive_scale (v:=r*b-a*N) (z:=b) prim ln
      (by rw [yl,ml]; ring) (by rw [yl]; ring)
    left
    simpa only [ps,mul_one] using And.intro ml yl
  have pos1 := mul_le_mul_of_nonneg_left (show 1≤l by omega) bp.le
  have pos2 := mul_le_mul_of_nonneg_left (show 1≤u by omega) dp.le
  omega

/-- Natural rectangle data and the signed residual representation used
by the rectangle proof. Normalizing the root modulo N is optional. -/
theorem point {N r H B a b c d y : ℕ} {m x : ℤ} (np : 0<N)
    (bp : 0<b) (dp : 0<d) (bB : b≤B) (dB : d≤B) (sum : B<b+d)
    (det : b*c=a*d+1) (left : a*N≤b*r) (right : d*r≤c*N)
    (area : H*B<N) (yp : 0<y) (yB : y≤B)
    (eqn : x=(r:ℤ)*y-m*N) (near : x.natAbs≤H) (prim : x.natAbs.Coprime y) :
    (x=(r:ℤ)*b-(a:ℤ)*N ∧ y=b) ∨ (x=(r:ℤ)*d-(c:ℤ)*N ∧ y=d) := by
  have det' : (b:ℤ)*c=(a:ℤ)*d+1 := by exact_mod_cast det
  have small : |x|≤(H:ℤ) := by
    have h : ((x.natAbs : ℕ) : ℤ) ≤ (H : ℤ) := by exact_mod_cast near
    simpa only [Int.natCast_natAbs] using h
  have pr : IsCoprime x (y:ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using prim)
  rw [eqn] at small pr
  obtain h|h := classify (N:=(N:ℤ)) (r:=(r:ℤ)) (H:=(H:ℤ)) (B:=(B:ℤ))
    (a:=(a:ℤ)) (b:=(b:ℤ)) (c:=(c:ℤ)) (d:=(d:ℤ)) (m:=m) (y:=(y:ℤ))
    (by exact_mod_cast np) (by positivity : 0≤(H:ℤ))
    (by exact_mod_cast bp) (by exact_mod_cast dp) (by exact_mod_cast bB)
    (by exact_mod_cast dB) (by exact_mod_cast sum) (by linarith only [det'])
    (by exact_mod_cast left) (by exact_mod_cast right) (by exact_mod_cast area)
    (by exact_mod_cast yp) (by exact_mod_cast yB) small pr
  · have ye : y=b := by exact_mod_cast h.2
    exact Or.inl ⟨by rw [eqn,h.1,ye],ye⟩
  · have ye : y=d := by exact_mod_cast h.2
    exact Or.inr ⟨by rw [eqn,h.1,ye],ye⟩

end PrimeFactors.RectangularFareyOracle
