import PrimeFactors.CubicTraceSquare
import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Finset.Nat

/-! Finite trace menus for two forced cubic rows and public integer-root
recognition for one sparse family of products. We use signed integers for the
trace equations and natural numbers for the product-only decoder. -/
namespace PrimeFactors.CubicForcedParameters

/-- For `γ = α+w`, the translated cubic equation is
`γ(γ+r−w)(γ+t−w)=H`. Thus `Hγ` has trace `H(2w−r−t)`, second elementary
symmetric coefficient `H²(w−r)(w−t)`, and norm `H⁴`. -/
theorem scaled_cubic {R : Type*} [CommRing R] {r t w H γ : R}
    (root : γ*(γ+r-w)*(γ+t-w)=H) :
    CubicTraceSquare.cubic (H*(2*w-r-t)) (H^2*(w-r)*(w-t)) (H^4) (H*γ) = 0 := by
  unfold CubicTraceSquare.cubic
  linear_combination H^3*root

/-- Multiplication by the square of the nonzero third row changes `β` into
`Hγ`. In a field this preserves and reflects the existence of a square root. -/
theorem complement_square {K : Type*} [Field K] {β γ H : K} (prod : β*γ=H) (hg : γ≠0) :
    IsSquare β ↔ IsSquare (H*γ) := by
  rw [←prod, isSquare_iff_exists_sq, isSquare_iff_exists_sq]
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨u*γ, by ring⟩
  · rintro ⟨u, hu⟩
    refine ⟨u/γ, ?_⟩
    rw [div_pow, eq_div_iff (pow_ne_zero 2 hg), pow_two γ, ←mul_assoc]
    exact hu

def equation (r t H w u : ℤ) := u^4-2*H*(2*w-r-t)*u^2-8*H^2*u+H^2*(r-t)^2

theorem quartic (r t H w u : ℤ) :
    CubicTraceSquare.quartic (H*(2*w-r-t)) (H^2*(w-r)*(w-t)) (H^2) u = equation r t H w u := by
  unfold CubicTraceSquare.quartic equation
  ring

/-- All nonconstant coefficients carry a factor `u`; the divisor list uses
only `H,r,t`, even when the third row depends on a very large product. -/
theorem divisor {r t H w u : ℤ} (root : equation r t H w u=0) : u ∣ (H*(r-t))^2 := by
  refine ⟨-u^3+2*H*(2*w-r-t)*u+8*H^2, ?_⟩
  unfold equation at root
  linear_combination root

theorem inverse_label {r t H w u : ℤ} (root : equation r t H w u=0) :
    4*H*u^2*w=u^4+2*H*(r+t)*u^2-8*H^2*u+H^2*(r-t)^2 := by
  unfold equation at root
  linear_combination -root

/-- Each signed trace determines at most one third row. -/
theorem unique_w {r t H w₁ w₂ u : ℤ} (hn : H≠0) (hu : u≠0)
    (a : equation r t H w₁ u=0) (b : equation r t H w₂ u=0) : w₁=w₂ := by
  exact mul_left_cancel₀ (by positivity : 4*H*u^2 ≠ 0) ((inverse_label a).trans (inverse_label b).symm)

/-- A constant-cost exclusion before factoring the parameter `H(r−t)`. The
right-hand side is independent of both the input product and the third row. -/
theorem height_bound {r t H w u : ℤ} (order : r<t) (rs : 0≤r+t) (hn : H≠0) (positive : 0<w)
    (root : equation r t H w u=0) :
    4* |H| *w ≤ ((H*(r-t))^2)^2+2* |H| *(r+t)+8*H^2+(H*(r-t))^2 := by
  let k := (H*(r-t))^2
  have kp : 0<k := sq_pos_of_ne_zero (mul_ne_zero hn (sub_ne_zero.mpr order.ne))
  have dv : |u| ∣ k := (abs_dvd ..).mpr (divisor root)
  have nz : u≠0 := by rintro rfl; simp at dv; omega
  have one : 1≤|u| := by have := abs_pos.mpr nz; omega
  have bound := Int.le_of_dvd kp dv
  have qpos : 0<u^2 := sq_pos_of_ne_zero nz
  have qbound : u^2≤k^2 := by rw [←sq_abs u]; exact pow_le_pow_left₀ (abs_nonneg u) bound 2
  have ab : |u|≤u^2 := by rw [←sq_abs u, sq]; exact le_mul_of_one_le_right (abs_nonneg u) one
  have eq := congrArg abs (inverse_label root)
  have a₁ := abs_add_le (u^4) (2*H*(r+t)*u^2)
  have a₂ := abs_sub (u^4+2*H*(r+t)*u^2) (8*H^2*u)
  have a₃ := abs_add_le (u^4+2*H*(r+t)*u^2-8*H^2*u) k
  have right : |4*H*u^2*w| ≤ u^4+2* |H| *(r+t)*u^2+8*H^2* |u|+k := by
    rw [eq, show H^2*(r-t)^2=k by dsimp [k]; ring]
    simp only [abs_mul, abs_of_nonneg (pow_nonneg (sq_nonneg u) 2), abs_of_nonneg (sq_nonneg u),
      abs_of_nonneg (sq_nonneg H), abs_of_nonneg rs, abs_of_pos kp, abs_of_nonneg (by decide : (0:ℤ)≤2),
      abs_of_nonneg (by decide : (0:ℤ)≤8), abs_of_nonneg (show 0≤u^4 by positivity)] at a₁ a₂ a₃
    linarith only [a₁,a₂,a₃]
  have lead := mul_le_mul_of_nonneg_right qbound (sq_nonneg u)
  have lin := mul_le_mul_of_nonneg_left ab (show 0≤8*H^2 by positivity)
  have tail : k ≤ k*u^2 := le_mul_of_one_le_right kp.le (by omega)
  simp only [abs_mul, abs_of_nonneg (by decide : (0:ℤ)≤4), abs_of_nonneg (sq_nonneg u), abs_of_pos positive] at right
  change 4 * |H| * w ≤ k^2 + 2 * |H| * (r+t) + 8*H^2 + k
  apply le_of_mul_le_mul_right (a:=u^2) _ qpos
  nlinarith only [right,lead,lin,tail]

/-- Both signed values are computed without a cubic field operation. Their
product is the input times the explicit cofactor `4Hu²`. -/
theorem signed_product {r t H w u z : ℤ} (root : equation r t H w u=0) (rat : z^2=r*t) :
    (z*(u^2+H*(r+t))-2*H*(u+r*t))*(z*(u^2+H*(r+t))+2*H*(u+r*t)) =
      4*H*u^2*(r*t*w-H) := by
  unfold equation at root
  linear_combination (u^2+H*(r+t))^2*rat + r*t*root

def low (s : ℕ) := (s-1)*(4*s^2+2)+1
def high (s : ℕ) := 4*s^3+4*s^2+2*s+1
def target (s : ℕ) := low s*high s

/-- The first complementary trace, `u=1`, with the square pair `(1,4s²)`. -/
theorem diagonal_quartic (s : ℤ) : equation 1 (4*s^2) 1 (4*s^4-1) 1=0 := by
  unfold equation
  ring

theorem target_identity {s : ℕ} (hs : 0<s) : target s+4*s^2+1=16*s^6 := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  simp [target, low, high, Nat.succ_eq_add_one]
  ring

/-- Ordinary Fermat search reaches the midpoint `4s³+2s`, with half gap `4s²+1`. -/
theorem fermat {s : ℕ} (hs : 0<s) : target s+(4*s^2+1)^2=(4*s^3+2*s)^2 := by
  nlinarith only [target_identity hs]

/-- This is the exact starting midpoint of ordinary Fermat search. It is
`2s` positions below the midpoint representing the displayed factors. -/
theorem fermat_bracket {s : ℕ} (hs : 0<s) :
    (4*s^3-1)^2 < target s ∧ target s ≤ (4*s^3)^2 := by
  have target_eq := target_identity hs
  have positive : 1≤4*s^3 := Nat.succ_le_of_lt (by positivity)
  zify [positive] at *
  have sp : (1:ℤ)≤s := by omega
  have sq : (1:ℤ)≤(s:ℤ)^2 := by nlinarith [sq_nonneg ((s:ℤ)-1)]
  constructor
  · nlinarith only [target_eq, sq, mul_nonneg (show 0≤(s:ℤ)-1 by omega) (show 0≤(s:ℤ)^2 by positivity)]
  · nlinarith only [target_eq, sq]

theorem proper {s : ℕ} (hs : 2≤s) : 1<low s ∧ low s<high s := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hs
  simp [low, high]
  nlinarith only [Nat.zero_le v, Nat.zero_le (v^2), Nat.zero_le (v^3)]

/-- Public specification of the ordinary ceiling cube root. An implementation
can return any integer certified by its consecutive cube bounds. -/
noncomputable def ceilCube (a : ℕ) : ℕ := Nat.find (show ∃ t : ℕ, a≤t^3 from
  ⟨a+1, by nlinarith only [Nat.zero_le (a^2), Nat.zero_le (a^3)]⟩)

theorem ceilCube_eq {a t : ℕ} (lo : (t-1)^3<a) (hi : a≤t^3) : ceilCube a=t := by
  apply le_antisymm
  · exact Nat.find_min' (p:=fun v : ℕ => a≤v^3) _ hi
  by_contra! lt
  have prev : ceilCube a≤t-1 := by omega
  have reached : a≤(ceilCube a)^3 := Nat.find_spec (p:=fun v : ℕ => a≤v^3) _
  exact (not_lt_of_ge (reached.trans (Nat.pow_le_pow_left prev _))) lo

/-- Binary or Newton cube root followed by a square root recovers the parameter
on the entire diagonal family. -/
theorem cube_bracket {s : ℕ} (hs : 0<s) :
    (4*s^2-1)^3 < 4*target s ∧ 4*target s ≤ (4*s^2)^3 := by
  have target_eq := target_identity hs
  have sq : 1≤4*s^2 := Nat.succ_le_of_lt (by positivity)
  zify [sq] at *
  have span : 4*(s:ℤ)^2≥4 := by nlinarith [sq_nonneg ((s:ℤ)-1)]
  constructor
  · nlinarith only [target_eq, span, mul_nonneg (show 0≤4*(s:ℤ)^2-4 by omega)
        (show 0≤12*(s:ℤ)^2+5 by positivity)]
  · nlinarith only [target_eq, span]

noncomputable def decode (n : ℕ) : Option (ℕ × ℕ) :=
  let s := (ceilCube (4*n)).sqrt / 2
  if 2≤s ∧ target s=n then some (low s, high s) else none

theorem decode_target {s : ℕ} (hs : 2≤s) : decode (target s)=some (low s, high s) := by
  obtain ⟨lo,hi⟩ := cube_bracket (s:=s) (by omega)
  rw [decode, ceilCube_eq lo hi, show 4*s^2=(2*s)^2 by ring, Nat.sqrt_eq', Nat.mul_div_cancel_left _ (by decide : 0<2)]
  simp [hs]

set_option exponentiation.threshold 4096 in
/-- The target bit width bounds the parameter even without a primality assumption. -/
theorem parameter_bits {s : ℕ} (hs : 0<s) (size : target s<2^2048) : s<2^341 := by
  by_contra! large
  have monotone := Nat.pow_le_pow_left large 6
  have sq_le : s^2≤s^6 := Nat.pow_le_pow_right hs (by decide)
  have positive := Nat.one_le_pow 6 s hs
  have low_bound : 8*s^6≤target s := by
    nlinarith only [target_identity hs, sq_le, positive]
  exact (not_lt_of_ge ((show (2:ℕ)^2048≤8*(2^341)^6 by decide +kernel).trans
    ((Nat.mul_le_mul_left 8 monotone).trans low_bound))) size

/-- Fewer than 2^341 distinct products, allowing all composites in this family. -/
theorem population (pairs : Finset ℕ) (cover : ∀ n∈pairs, n<2^2048 ∧ ∃ s≥2, target s=n) :
    pairs.card < 2^341 := by
  have inc : pairs⊆(Finset.Ico 2 (2^341)).image target := by
    intro n hn
    obtain ⟨small,s,hs,rfl⟩ := cover n hn
    exact Finset.mem_image.mpr ⟨s,Finset.mem_Ico.mpr ⟨hs,parameter_bits (by omega) small⟩,rfl⟩
  have bound := (Finset.card_le_card inc).trans Finset.card_image_le
  rw [Nat.card_Ico] at bound
  omega

set_option exponentiation.threshold 4096 in
/-- For an ambient population with at least `2^2021` members, the recognized
input products occupy less than one part in `2^1680`. -/
theorem fraction (pairs : Finset ℕ) (T : ℕ) (room : 2^2021≤T)
    (cover : ∀ n∈pairs, n<2^2048 ∧ ∃ s≥2, target s=n) : 2^1680*pairs.card<T := by
  calc
    2^1680*pairs.card < 2^1680*2^341 := Nat.mul_lt_mul_of_pos_left (population pairs cover) (by positivity)
    _ = 2^2021 := (pow_add (2:ℕ) 1680 341).symm
    _ ≤ T := room

end PrimeFactors.CubicForcedParameters
