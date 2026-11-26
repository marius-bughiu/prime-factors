import Mathlib.Data.Real.Sqrt
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Separation for two integer points of signed norm d in the same residue
class of square roots of 2. The class modulo |d| is equivalently given by
divisibility by d. The result applies as soon as a common class is supplied. -/
namespace PrimeFactors.WeightedPairPell

/-- Real size of an algebraic integer in the positive embedding. -/
noncomputable def height (v u : ℤ) : ℝ := v + u * Real.sqrt 2

private theorem multiplicative (v u a b : ℤ) :
    height (v*a+2*u*b) (v*b+u*a) = height v u * height a b := by
  unfold height
  push_cast
  linear_combination -(u:ℝ)*b*Real.sq_sqrt (by norm_num : (0:ℝ)≤2)

/-- A primitive integer solution specifies one square root of 2 modulo |d|.
The last clause gives uniqueness of the class, including when |d|=1. -/
theorem primitive_class {v u d : ℤ} (norm : v^2-2*u^2=d) (cop : IsCoprime u v) :
    ∃ r : ℤ, d ∣ r^2-2 ∧ d ∣ v-r*u ∧
      ∀ s : ℤ, d ∣ v-s*u → d ∣ r-s := by
  obtain ⟨x,y,bezout⟩ := cop
  let k := x^2*u + 2*x*y*v + 2*y^2*u
  have inv : k*u+d*y^2=1 := by
    dsimp [k]
    linear_combination (x*u+y*v+1)*bezout-y^2*norm
  refine ⟨v*k, ⟨k^2-2*y^2*(k*u+1),?_⟩, ⟨v*y^2,?_⟩,?_⟩
  · linear_combination k^2*norm+2*(k*u+1)*inv
  · linear_combination -v*inv
  · rintro s ⟨z,hz⟩
    refine ⟨k*z-s*y^2,?_⟩
    linear_combination k*hz+s*inv

/-- If two solutions select the root r modulo |d|, their quotient is an
integer pair of norm one. Its coordinates are specified by exact division,
and multiplying by the first solution recovers the second. -/
theorem quotient {v u w t d r : ℤ} (hd : d≠0)
    (first : v^2-2*u^2=d) (second : w^2-2*t^2=d)
    (root : d ∣ r^2-2) (left : d ∣ v-r*u) (right : d ∣ w-r*t) :
    ∃ a b : ℤ, d*a=v*w-2*u*t ∧ d*b=v*t-w*u ∧ a^2-2*b^2=1 ∧
      v*a+2*u*b=w ∧ v*b+u*a=t := by
  obtain ⟨e, he⟩ := root
  obtain ⟨s, hs⟩ := left
  obtain ⟨z, hz⟩ := right
  let a := s*w + r*u*z + e*u*t
  let b := s*t - z*u
  have ha : d*a=v*w-2*u*t := by
    dsimp [a]
    linear_combination -w*hs-r*u*hz-u*t*he
  have hb : d*b=v*t-w*u := by
    dsimp [b]
    linear_combination -t*hs+u*hz
  refine ⟨a,b,ha,hb,?_,?_,?_⟩
  · apply mul_left_cancel₀ (pow_ne_zero 2 hd)
    calc
      d^2*(a^2-2*b^2) = (d*a)^2-2*(d*b)^2 := by ring
      _ = (v^2-2*u^2)*(w^2-2*t^2) := by rw [ha,hb]; ring
      _ = d^2*1 := by rw [first,second]; ring
  · apply mul_left_cancel₀ hd
    calc
      d*(v*a+2*u*b) = v*(d*a)+2*u*(d*b) := by ring
      _ = d*w := by rw [ha,hb]; linear_combination w*first
  · apply mul_left_cancel₀ hd
    calc
      d*(v*b+u*a) = v*(d*b)+u*(d*a) := by ring
      _ = d*t := by rw [ha,hb]; linear_combination t*first

/-- The least expanding integral unit of norm one in the positive embedding
is at least 3+2√2. Equality occurs at the integer coordinates (3,2). -/
theorem unit_lower {a b : ℤ} (norm : a^2-2*b^2=1) (large : 1<height a b) :
    3+2*Real.sqrt 2 ≤ height a b := by
  have normR : (a:ℝ)^2-2*(b:ℝ)^2=1 := by exact_mod_cast norm
  have conjugates : height a b * ((a:ℝ)-b*Real.sqrt 2)=1 := by
    unfold height
    linear_combination normR-(b:ℝ)^2*Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have pos : 0<height a b := lt_trans (by norm_num) large
  have cp : 0<(a:ℝ)-b*Real.sqrt 2 := by
    apply (mul_pos_iff_of_pos_left pos).mp
    rw [conjugates]
    norm_num
  have cs : (a:ℝ)-b*Real.sqrt 2<1 := by
    apply (mul_lt_mul_iff_of_pos_left pos).mp
    rw [conjugates,mul_one]
    exact large
  unfold height at large ⊢
  have ap : 0<a := by exact_mod_cast (show (0:ℝ)<a by linarith only [large,cp])
  have bp : 0<b := by
    exact_mod_cast (pos_of_mul_pos_left
      (show (0:ℝ)<b*Real.sqrt 2 by linarith only [large,cs]) (Real.sqrt_nonneg _))
  have bne : b≠1 := by
    rintro rfl
    by_cases same : a=1
    · subst a
      norm_num at norm
    · have a2 : 2≤a := by omega
      nlinarith [mul_nonneg (by omega : 0≤a-2) (by omega : 0≤a+2)]
  have b2 : 2≤b := by omega
  have a3 : 3≤a := by
    by_cases big : 3≤a
    · exact big
    · have bb := mul_nonneg (by omega : 0≤b-2) (by omega : 0≤b+2)
      have aa := mul_nonneg (by omega : 0≤2-a) (by omega : 0≤2+a)
      nlinarith
  have a3r : (3:ℝ)≤a := by exact_mod_cast a3
  have b2r : (2:ℝ)≤b := by exact_mod_cast b2
  exact add_le_add a3r (mul_le_mul_of_nonneg_right b2r (Real.sqrt_nonneg _))

/-- Within one root class the real sizes of positive, strictly ordered
solutions grow by at least 3+2√2, for either sign of d. -/
theorem separation {v u w t d r : ℤ} (hd : d≠0)
    (first : v^2-2*u^2=d) (second : w^2-2*t^2=d)
    (root : d ∣ r^2-2) (left : d ∣ v-r*u) (right : d ∣ w-r*t)
    (positive : 0<height v u) (order : height v u<height w t) :
    height v u*(3+2*Real.sqrt 2) ≤ height w t := by
  obtain ⟨a,b,_,_,norm,hv,hu⟩ := quotient hd first second root left right
  have product : height v u * height a b = height w t :=
    (multiplicative v u a b).symm.trans (by rw [hv,hu])
  have expanding : 1<height a b := by
    apply (mul_lt_mul_iff_of_pos_left positive).mp
    simpa only [mul_one,product] using order
  rw [←product]
  exact mul_le_mul_of_nonneg_left (unit_lower norm expanding) positive.le

private theorem conjugate {v u d : ℤ} (norm : v^2-2*u^2=d) :
    height v u*((v:ℝ)-u*Real.sqrt 2)=d := by
  have n : (v:ℝ)^2-2*(u:ℝ)^2=d := by exact_mod_cast norm
  unfold height
  linear_combination n-(u:ℝ)^2*Real.sq_sqrt (by norm_num : (0:ℝ)≤2)

private theorem coords_of_height {v u w t d : ℤ}
    (first : v^2-2*u^2=d) (second : w^2-2*t^2=d)
    (positive : 0<height v u) (eq : height v u=height w t) : (v,u)=(w,t) := by
  have bar : (v:ℝ)-u*Real.sqrt 2=(w:ℝ)-t*Real.sqrt 2 := by
    apply mul_left_cancel₀ positive.ne'
    rw [conjugate first, eq, conjugate second]
  unfold height at eq
  apply Prod.ext
  · exact_mod_cast (show (v:ℝ)=w by linarith only [bar,eq])
  · have ur : (u:ℝ)*Real.sqrt 2=(t:ℝ)*Real.sqrt 2 := by linarith only [bar,eq]
    exact_mod_cast mul_right_cancel₀ (by positivity : Real.sqrt 2≠0) ur

private theorem band {h : ℝ} (bottom : 1≤h) (K : ℕ) (top : h<4^K) :
    ∃ j < K, 4^j≤h ∧ h<4^(j+1) := by
  induction K with
  | zero => simp at top; linarith
  | succ K ih =>
    by_cases inside : h<4^K
    · obtain ⟨j,hj,lo,hi⟩ := ih inside
      exact ⟨j,by omega,lo,hi⟩
    · exact ⟨K,by omega,le_of_not_gt inside,top⟩

/-- A fixed slope class contains at most K distinct solution pairs with
positive embedding in [1,4^K). This counts the pairs themselves. -/
theorem class_card {d r : ℤ} (hd : d≠0) (root : d ∣ r^2-2)
    (S : Finset (ℤ×ℤ)) (K : ℕ)
    (points : ∀ x∈S, x.1^2-2*x.2^2=d ∧ d ∣ x.1-r*x.2 ∧
      1≤height x.1 x.2 ∧ height x.1 x.2<4^K) : S.card≤K := by
  classical
  let h (x : ℤ×ℤ) := height x.1 x.2
  have room (x : S) : ∃ j<K, 4^j≤h x.val ∧ h x.val<4^(j+1) :=
    band (points x x.property).2.2.1 K (points x x.property).2.2.2
  choose j hj bot top using room
  let bin (x : S) : Fin K := ⟨j x,hj x⟩
  have strict (x y : S) (order : h x.val<h y.val) : j x≠j y := by
    intro same
    obtain ⟨fx,rx,px,_⟩ := points x x.property
    obtain ⟨fy,ry,_,_⟩ := points y y.property
    have grow := separation hd fx fy root rx ry (lt_of_lt_of_le zero_lt_one px) order
    have four : (4:ℝ)≤3+2*Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    have low : (4:ℝ)^(j y+1) ≤ h y.val := by
      rw [←same,pow_succ]
      exact (mul_le_mul (bot x) four (by norm_num) (zero_le_one.trans px)).trans grow
    exact (not_lt_of_ge low) (top y)
  have inj : Function.Injective bin := by
    intro x y same
    have jeq : j x=j y := congrArg Fin.val same
    rcases lt_trichotomy (h x.val) (h y.val) with xy|eq|yx
    · exact (strict x y xy jeq).elim
    · apply Subtype.ext
      exact coords_of_height (points x x.property).1 (points y y.property).1
        (lt_of_lt_of_le zero_lt_one (points x x.property).2.2.1) eq
    · exact (strict y x yx jeq.symm).elim
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective bin inj

end PrimeFactors.WeightedPairPell
