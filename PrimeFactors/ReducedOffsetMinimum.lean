import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace PrimeFactors.ReducedOffsetMinimum

/-- The factor-coordinate quadratic form with determinant p*q-T². -/
def Q (p T q s v : ℤ) : ℤ := p*s^2-2*T*s*v+q*v^2

private def cross (p T q s v x y : ℤ) : ℤ := p*s*x-T*(s*y+v*x)+q*v*y

theorem positive {p T q h s v : ℤ} (hp : 0<p) (hh : 0<h)
    (det : p*q-T^2=h) (nonzero : s≠0 ∨ v≠0) : 0<Q p T q s v := by
  by_cases z : v=0
  · simpa [Q,z] using mul_pos hp (sq_pos_of_ne_zero (nonzero.resolve_right (not_not.mpr z)))
  have ident : p*Q p T q s v=(p*s-T*v)^2+h*v^2 := by rw [←det]; unfold Q; ring
  have rhs := add_pos_of_nonneg_of_pos (sq_nonneg (p*s-T*v)) (mul_pos hh (sq_pos_of_ne_zero z))
  exact (mul_pos_iff_of_pos_left hp).mp (ident ▸ rhs)

private theorem nearest (b j : ℤ) (hj : 0<j) : ∃ k : ℤ, |2*(b+k*j)|≤j := by
  have lower := Int.emod_nonneg b hj.ne'
  have upper := Int.emod_lt_of_pos b hj
  have div := Int.emod_add_ediv b j
  by_cases half : 2*(b%j)≤j
  · refine ⟨-(b/j),?_⟩
    rw [show b+-(b/j)*j=b%j by linarith only [div],abs_le]
    omega
  · refine ⟨-(b/j)-1,?_⟩
    rw [show b+(-(b/j)-1)*j=b%j-j by linarith only [div],abs_le]
    omega

/-- Public arithmetic needed after a representation has supplied the shortest vector. -/
theorem minimum_bound {p T q h s v : ℤ} (hp : 0<p) (hh : 0<h) (det : p*q-T^2=h)
    (primitive : IsCoprime s v) (pos : 0<Q p T q s v)
    (shortest : ∀ x y : ℤ, 0<Q p T q x y → Q p T q s v ≤ Q p T q x y) :
    3*(Q p T q s v)^2≤4*h := by
  obtain ⟨a,b,bez⟩ := primitive
  let j := Q p T q s v
  obtain ⟨k,near⟩ := nearest (cross p T q s v (-b) a) j pos
  let x := -b+k*s
  let y := a+k*v
  have basis : s*y-v*x=1 := by dsimp [x,y]; linear_combination bez
  have nz : x≠0 ∨ y≠0 := by by_contra! both; simp [both.1,both.2] at basis
  have length := shortest x y (positive hp hh det nz)
  change j ≤ Q p T q x y at length
  have translate : cross p T q s v x y=cross p T q s v (-b) a+k*j := by
    dsimp [cross,x,y,j,Q]; ring
  rw [←translate] at near
  have small : (2*cross p T q s v x y)^2≤j^2 := by
    rw [←sq_abs (2*cross p T q s v x y)]
    exact pow_le_pow_left₀ (abs_nonneg _) near 2
  have identity : j*Q p T q x y-(cross p T q s v x y)^2 = h := by
    calc _ = (p*q-T^2)*(s*y-v*x)^2 := by dsimp [j,Q,cross]; ring
         _ = _ := by rw [det,basis];ring
  change 3*j^2≤4*h
  nlinarith only [small,identity,mul_le_mul_of_nonneg_left length pos.le]

private theorem shortest_primitive {p T q s v : ℤ} (pos : 0<Q p T q s v)
    (shortest : ∀ x y : ℤ, 0<Q p T q x y → Q p T q s v ≤ Q p T q x y) : IsCoprime s v := by
  let g : ℤ := Int.gcd s v
  obtain ⟨x,sx⟩ := (Int.gcd_dvd_left (a:=s) (b:=v))
  obtain ⟨y,vy⟩ := (Int.gcd_dvd_right (a:=s) (b:=v))
  change s=g*x at sx
  change v=g*y at vy
  have same : Q p T q s v=g^2*Q p T q x y := by
    rw [sx,vy]; unfold Q; ring
  have gn : g≠0 := by intro zero; rw [same,zero] at pos; simp at pos
  have qpos := (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero gn)).mp (same ▸ pos)
  have small := shortest x y qpos
  rw [same] at small
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  by_contra bad
  have gg : 2≤g := by dsimp [g] at *;omega
  have square : 4≤g^2 := by nlinarith [sq_nonneg (g-2)]
  nlinarith only [mul_le_mul_of_nonneg_right square qpos.le,small,qpos]

/-- A globally least positive represented value exists. It has a primitive
representative and satisfies the sharp two-dimensional determinant bound. -/
theorem exists_minimum {p T q h : ℤ} (hp : 0<p) (hh : 0<h) (det : p*q-T^2=h) :
    ∃ s v : ℤ, 0<Q p T q s v ∧ (∀ x y : ℤ, 0<Q p T q x y → Q p T q s v ≤ Q p T q x y) ∧
      IsCoprime s v ∧ 3*(Q p T q s v)^2≤4*h := by
  classical
  let represented (n : ℕ) := 0<n ∧ ∃ s v : ℤ, Q p T q s v=(n:ℤ)
  have start : ∃ n, represented n := by
    refine ⟨p.toNat,by omega,1,0,?_⟩
    simp [Q,Int.toNat_of_nonneg hp.le]
  obtain ⟨jp,s,v,sv⟩ := Nat.find_spec start
  have pos : 0<Q p T q s v := by rw [sv]; exact_mod_cast jp
  have shortest (x y : ℤ) (good : 0<Q p T q x y) : Q p T q s v ≤ Q p T q x y := by
    have repr : represented (Q p T q x y).toNat :=
      ⟨by omega,(x:ℤ),y,(Int.toNat_of_nonneg good.le).symm⟩
    have le := Nat.find_min' start repr
    rw [sv]
    exact (show (Nat.find start:ℤ)≤((Q p T q x y).toNat:ℤ) by exact_mod_cast le).trans_eq
      (Int.toNat_of_nonneg good.le)
  have primitive := shortest_primitive pos shortest
  exact ⟨s,v,pos,shortest,primitive,minimum_bound hp hh det primitive pos shortest⟩

theorem exists_small {p T q h : ℤ} (hp : 0<p) (hh : 0<h) (det : p*q-T^2=h) :
    ∃ s v : ℤ, 0<Q p T q s v ∧ 3*(Q p T q s v)^2≤4*h ∧ IsCoprime s v := by
  obtain ⟨s,v,pos,_,cop,bound⟩ := exists_minimum hp hh det
  exact ⟨s,v,pos,bound,cop⟩

/-- Equality occurs for the form 2s²−2sv+2v². Every positive value is an
even integer, and (1,0) represents two. -/
theorem sharp_example :
    Q 2 1 2 1 0=2 ∧ 3*(Q 2 1 2 1 0)^2=4*((2:ℤ)*2-1^2) ∧
    ∀ s v : ℤ, 0<Q 2 1 2 s v → 2≤Q 2 1 2 s v := by
  refine ⟨by decide,by decide,?_⟩
  intro s v pos
  have eq : Q 2 1 2 s v=2*(s^2-s*v+v^2) := by unfold Q;ring
  omega

end PrimeFactors.ReducedOffsetMinimum
