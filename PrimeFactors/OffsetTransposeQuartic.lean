import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! A product of offset transposed words has a quartic equation once the
block product C is supplied. On the positive digit interval the associated
rational function has strictly increasing slopes, giving at most two hits. -/

namespace PrimeFactors.OffsetTransposeQuartic

open Polynomial Finset

def height (B N C : ℤ) : ℤ := (N-(B^2+1)*C)/B

noncomputable def quartic (B t H C : ℤ) : ℤ[X] :=
  X^4+(Polynomial.C (-(B*t))*X^3+Polynomial.C (-H)*X^2+
    Polynomial.C (-(t*C))*X+Polynomial.C (C^2))

theorem eval_quartic (B t H C x : ℤ) :
    (quartic B t H C).eval x=x^4-B*t*x^3-H*x^2-t*C*x+C^2 := by
  simp [quartic]
  ring

theorem monic (B t H C : ℤ) : (quartic B t H C).Monic := by
  apply monic_X_pow_add
  apply lt_of_le_of_lt (b:=(3:WithBot ℕ)) _ (by decide)
  compute_degree

theorem degree (B t H C : ℤ) : (quartic B t H C).natDegree=4 := by
  unfold quartic
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · rw [natDegree_X_pow]
    apply lt_of_le_of_lt (b:=3) _ (by decide)
    compute_degree

theorem raw_root_count (B t H C : ℤ) (S : Finset ℤ)
    (roots : ∀ x∈S,(quartic B t H C).eval x=0) : S.card≤4 := by
  rw [←degree B t H C]
  exact card_le_degree_of_subset_roots (fun x hx => (mem_roots (monic B t H C).ne_zero).mpr (roots x hx))

def words (B t C x : ℤ) : ℤ×ℤ :=
  (B*(C/x-t)+x,B*x+C/x)

theorem identity (B t b z : ℤ) :
    (B*(z-t)+b)*(B*b+z)=(B^2+1)*(b*z)+B*(z^2+b^2-t*(B*b+z)) := by ring

/-- An exact division guard is needed for arbitrary trial values of C. -/
def Checked (B N t C x : ℤ) : Prop :=
  0<x ∧ x<B ∧ x∣C ∧ 0<C/x ∧ 0≤C/x-t ∧ C/x-t≤x ∧
  B∣N-(B^2+1)*C ∧ (quartic B t (height B N C) C).eval x=0

theorem check_iff {B N t C x : ℤ} (bp : 0<B) :
    Checked B N t C x ↔ ∃ a z : ℤ, 0<x ∧ x<B ∧ 0≤a ∧ a≤x ∧
      0<z ∧ z=a+t ∧ x*z=C ∧ (B*a+x)*(B*x+z)=N := by
  constructor
  · rintro ⟨xp,xb,div,zp,ap,order,exactDiv,rt⟩
    let z := C/x
    have xz : x*z=C := Int.mul_ediv_cancel' div
    have ratio : B*height B N C=N-(B^2+1)*C := Int.mul_ediv_cancel' exactDiv
    rw [eval_quartic] at rt
    have balance : x^2*(z^2+x^2-t*(B*x+z)-height B N C)=0 := by
      calc
        _ = x^4-B*t*x^3-height B N C*x^2-t*(x*z)*x+(x*z)^2 := by ring
        _ = 0 := by rw [xz]; exact rt
    have level := (mul_eq_zero.mp balance).resolve_left (pow_ne_zero _ xp.ne')
    refine ⟨z-t,z,xp,xb,ap,order,zp,by ring,xz,?_⟩
    rw [identity,xz,show z^2+x^2-t*(B*x+z)=height B N C by linarith,ratio]
    ring
  · rintro ⟨a,z,xp,xb,ap,order,zp,zt,rfl,rfl⟩
    have az : a=z-t := by omega
    have exactEq : (B*a+x)*(B*x+z)-(B^2+1)*(x*z)=B*(z^2+x^2-t*(B*x+z)) := by
      rw [az,identity]; ring
    have div : x*z/x=z := Int.mul_ediv_cancel_left _ xp.ne'
    have he : height B ((B*a+x)*(B*x+z)) (x*z)=z^2+x^2-t*(B*x+z) := by
      rw [height,exactEq,Int.mul_ediv_cancel_left _ bp.ne']
    refine ⟨xp,xb,dvd_mul_right ..,by rwa [div],?_,?_,⟨_,exactEq⟩,?_⟩
    · rwa [div,←az]
    · rwa [div,←az]
    · rw [eval_quartic,he]; ring

/-- For each checked positive block, its complementary block, offset block,
and thus both complete words are unique by exact division. -/
theorem recovered_words {B t C a b z : ℤ} (bp : 0<b) (prod : b*z=C) (shift : z=a+t) :
    words B t C b=(B*a+b,B*b+z) := by
  rw [words,←prod,Int.mul_ediv_cancel_left _ bp.ne',show z-t=a by omega]

def level (B t C x : ℚ) := x*x-B*t*x+(C/x)*(C/x)-t*(C/x)

/-- Denominator-cleared identity for the difference of two secant slopes. -/
theorem curvature (B t C : ℚ) {x y z : ℚ} (hx : x≠0) (hy : y≠0) (hz : z≠0) :
    (level B t C z-level B t C y)*(y-x) - (level B t C y-level B t C x)*(z-y) =
      (z-y)*(y-x)*(z-x)*(1+C/(x*y*z)*(C/x+C/y+C/z-t)) := by
  unfold level
  field_simp
  ring

private theorem positive_curve {t C x y z : ℚ} (cp : 0≤C) (xp : 0<x) (yp : 0<y) (zp : 0<z)
    (rangeX : t*x≤C) : 0 < 1+C/(x*y*z)*(C/x+C/y+C/z-t) := by
  have low := (le_div_iff₀ xp).mpr rangeX
  have h₁ : 0≤C/y := by positivity
  have h₂ : 0≤C/z := by positivity
  exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (by positivity) (by linarith))

/-- Even the first differences on the entire integer interval strictly increase.
This sign test uses rational arithmetic and applies between divisors of C. -/
theorem step_increases (B : ℚ) {t C x : ℚ} (cp : 0≤C) (xp : 0<x) (rangeX : t*x≤C) :
    level B t C (x+1)-level B t C x < level B t C (x+2)-level B t C (x+1) := by
  have yp : 0<x+1 := by linarith
  have zp : 0<x+2 := by linarith
  have key := curvature B t C xp.ne' yp.ne' zp.ne'
  rw [show x+2-(x+1)=1 by ring,show x+1-x=1 by ring,show x+2-x=2 by ring] at key
  simp only [mul_one,one_mul] at key
  have positive := positive_curve cp xp yp zp rangeX
  linarith only [positive,key]

theorem root_level {B t H C x : ℤ} (xp : 0<x) :
    (quartic B t H C).eval x=0 ↔ level B t C x=(H:ℚ) := by
  have xn : (x:ℚ)≠0 := by exact_mod_cast xp.ne'
  have bridge : (x:ℚ)^2*(level B t C x-H)=(((quartic B t H C).eval x : ℤ) : ℚ) := by
    rw [eval_quartic]
    push_cast
    unfold level
    field_simp
    ring
  constructor
  · intro rt
    rw [rt,Int.cast_zero] at bridge
    exact sub_eq_zero.mp ((mul_eq_zero.mp bridge).resolve_left (pow_ne_zero _ xn))
  · intro v
    rw [v,sub_self,mul_zero] at bridge
    exact_mod_cast bridge.symm

/-- The quartic has at most two positive roots in the entire admissible digit
interval. This result does not require any divisibility tests or prime factors. -/
theorem interval_root_count (B t H C : ℤ) (cp : 0≤C) (S : Finset ℤ)
    (roots : ∀ x∈S,0<x ∧ t*x≤C ∧ (quartic B t H C).eval x=0) : S.card≤2 := by
  by_contra! large
  obtain ⟨x,y,z,hx,hy,hz,xy,xz,yz⟩ := two_lt_card_iff.mp large
  obtain ⟨xp,rangeX,xr⟩ := roots x hx
  obtain ⟨yp,_,yr⟩ := roots y hy
  obtain ⟨zp,_,zr⟩ := roots z hz
  have xq : 0<(x:ℚ) := by exact_mod_cast xp
  have yq : 0<(y:ℚ) := by exact_mod_cast yp
  have zq : 0<(z:ℚ) := by exact_mod_cast zp
  have key := curvature B t C xq.ne' yq.ne' zq.ne'
  rw [(root_level xp).mp xr,(root_level yp).mp yr,(root_level zp).mp zr] at key
  simp only [sub_self,zero_mul] at key
  have pos := positive_curve (t:=(t:ℚ)) (C:=(C:ℚ)) (by exact_mod_cast cp) xq yq zq (by exact_mod_cast rangeX)
  have neq {a b : ℤ} (ab : a≠b) : (b:ℚ)-(a:ℚ)≠0 :=
    sub_ne_zero.mpr (by exact_mod_cast ab.symm)
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (neq yz) (neq xy)) (neq xz)) pos.ne') key.symm

theorem checked_product {B N t C x : ℤ} (bp : 0<B) (check : Checked B N t C x) :
    (words B t C x).1*(words B t C x).2=N := by
  obtain ⟨a,z,xp,_,_,_,_,shift,xz,prod⟩ := (check_iff bp).mp check
  simpa only [recovered_words xp xz shift] using prod

theorem checked_count (B N t C : ℤ) (S : Finset ℤ) (checks : ∀ x∈S,Checked B N t C x) :
    S.card≤2 := by
  rcases S.eq_empty_or_nonempty with empty|⟨x,hx⟩
  · simp [empty]
  obtain ⟨xp,_,dvd,zp,_⟩ := checks x hx
  have cp : 0<C := by
    rw [←Int.mul_ediv_cancel' dvd]
    exact mul_pos xp zp
  apply interval_root_count B t (height B N C) C cp.le S
  intro y hy
  obtain ⟨yp,_,div,_,ap,_,_,rt⟩ := checks y hy
  refine ⟨yp,?_,rt⟩
  calc
    t*y ≤ (C/y)*y := mul_le_mul_of_nonneg_right (by linarith) yp.le
    _ = C := Int.ediv_mul_cancel div

/-- Both admissible roots can occur even at offset one. -/
theorem two_hits : Checked 8 700 1 12 4 ∧ Checked 8 700 1 12 6 ∧
    words 8 1 12 4=(20,35) ∧ words 8 1 12 6=(14,50) := by
  refine ⟨(check_iff (by decide)).mpr ⟨2,3,?_⟩,
    (check_iff (by decide)).mpr ⟨1,2,?_⟩,by decide,by decide⟩ <;> decide

theorem toy_primes : Checked 8 1357 1 21 7 ∧ words 8 1 21 7=(23,59) ∧
    Nat.Prime 23 ∧ Nat.Prime 59 := by
  exact ⟨(check_iff (by decide)).mpr ⟨2,3,by decide⟩,by decide,by norm_num,by norm_num⟩

end PrimeFactors.OffsetTransposeQuartic
