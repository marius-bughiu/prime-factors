import Mathlib.RingTheory.Polynomial.Dickson
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactors.DifferenceLane

namespace PrimeFactors.GapPolynomialScale

open Polynomial Finset

/-- The signed gap is unchanged in absolute value under joint negation. -/
theorem balanced_gap {x y : ℤ} (hxy : x ≤ 2*y) (hyx : y ≤ 2*x) :
    2*(x-y)^2 ≤ x*y := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hyx)]

theorem even_gap_radius {x y g : ℤ} {N : ℕ} (pair : x*y = N)
    (hxy : x ≤ 2*y) (hyx : y ≤ 2*x) (gap : x-y = 2*g) :
    g.natAbs ≤ Nat.sqrt (N/8) := by
  have hg := balanced_gap hxy hyx
  rw [gap, pair] at hg
  have hs : 8*g^2 ≤ (N:ℤ) := by nlinarith
  apply Nat.le_sqrt'.mpr
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).mpr
  have hex : ((g.natAbs : ℕ) : ℤ)^2 = g^2 := by
    rw [Int.natCast_natAbs, sq_abs]
  exact_mod_cast (show ((g.natAbs : ℕ) : ℤ)^2 * 8 ≤ N from by rw [hex]; linarith)

/-- The companion Lucas sequence for z and parameter c. -/
noncomputable def companion (c z : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n+2 => z * companion c z (n+1) - c * companion c z n

private theorem companion_norm (c z : ℤ) (n : ℕ) :
    (companion c z (n+1))^2 - z*companion c z (n+1)*companion c z n +
      c*(companion c z n)^2 = c^n := by
  induction n with
  | zero => simp [companion]
  | succ n ih =>
    change (companion c z (n+2))^2 - _ + _ = _
    rw [show companion c z (n+2) = z*companion c z (n+1)-c*companion c z n from rfl,
      pow_succ c n, ← ih]
    ring

theorem dickson_companion (c z : ℤ) (n : ℕ) :
    (dickson 1 c n).eval z = 2*companion c z (n+1) - z*companion c z n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [companion]
  | one => simp [companion]; ring
  | more n h₀ h₁ =>
    rw [dickson_add_two, eval_sub, eval_mul, eval_mul, eval_X, eval_C, h₀, h₁]
    change _ = 2 * (z * companion c z (n+2) - c * companion c z (n+1)) - _
    rw [show companion c z (n+2) = z*companion c z (n+1)-c*companion c z n from rfl]
    ring

/-- The integer identity works at either endpoint and at c=0. -/
theorem dickson_identity (c z : ℤ) (n : ℕ) :
    ((dickson 1 c n).eval z)^2 + (4*c-z^2)*(companion c z n)^2 = 4*c^n := by
  rw [dickson_companion, ← companion_norm c z n]
  ring

theorem dickson_bound {c z : ℤ} (interval : z^2 ≤ 4*c) (n : ℕ) :
    ((dickson 1 c n).eval z)^2 ≤ 4*c^n := by
  have hn := mul_nonneg (sub_nonneg.mpr interval) (sq_nonneg (companion c z n))
  linarith [dickson_identity c z n]

/-- With the even-gap radius s the interval weight is an integer. -/
theorem dickson_abs_bound {s z : ℤ} (hs : 0 ≤ s) (interval : z^2 ≤ 4*s^2) (n : ℕ) :
    |(dickson 1 (s^2) n).eval z| ≤ 2*s^n := by
  have h := dickson_bound interval n
  rw [← pow_mul, Nat.mul_comm, pow_mul] at h
  have hright : 0 ≤ 2*s^n := mul_nonneg (by decide) (pow_nonneg hs _)
  nlinarith [sq_abs ((dickson 1 (s^2) n).eval z), abs_nonneg ((dickson 1 (s^2) n).eval z)]

/-- All positive-degree Dickson polynomials give monic integer coordinates of the
indicated degree. The constant used for the basis itself is one. -/
theorem dickson_monic_degree (c : ℤ) (n : ℕ) :
    (dickson 1 c n).natDegree ≤ n ∧
      (0 < n → (dickson 1 c n).Monic ∧ (dickson 1 c n).natDegree = n) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [show (3-1:ℤ[X]) = C 2 by norm_num]
  | one => simp
  | more n h₀ h₁ =>
    obtain ⟨mon, deg⟩ := h₁.2 (by omega)
    have high : (X * dickson 1 c (n+1)).natDegree = n+2 := by
      rw [natDegree_X_mul mon.ne_zero, deg]
    have low : (C c * dickson 1 c n).natDegree < (X * dickson 1 c (n+1)).natDegree := by
      have he := natDegree_mul_le (p := C c) (q := dickson 1 c n)
      simp only [natDegree_C, zero_add] at he
      rw [high]
      omega
    rw [dickson_add_two, natDegree_sub_eq_left_of_natDegree_lt low, high]
    exact ⟨le_rfl, fun _ => ⟨(monic_X.mul mon).sub_of_left (degree_lt_degree low), rfl⟩⟩

def weight (s : ℕ) : ℕ → ℕ
  | 0 => 1
  | j+1 => 2*s^(j+1)

/-- Product of the integer column weights for the paired rows E_j, x E_(j−1). -/
theorem weight_product (s B n : ℕ) :
    (∏ i ∈ range (n+1), weight s (i+1) * (B*weight s i)) =
      2^(2*n+1) * B^(n+1) * s^((n+1)^2) := by
  induction n with
  | zero => simp [weight]; ring
  | succ n ih =>
    rw [prod_range_succ, ih]
    simp only [weight]
    rw [show 2*(n+1)+1 = (2*n+1)+2 by omega,
      show (n+1+1)^2 = (n+1)^2+(n+1+1)+(n+1) by ring]
    simp only [pow_add, pow_succ B]
    ring

theorem squared_weight_product (s B n : ℕ) :
    (∏ i ∈ range (n+1), weight s (i+1) * (B*weight s i))^2 =
      2^(4*n+2) * (B^2)^(n+1) * (s^2)^((n+1)^2) := by
  simp only [weight_product, mul_pow, ← pow_mul]
  congr 2 <;> ring

theorem uniform_weight_bound {s B : ℕ} (n : ℕ) (hB : B^2 ≤ 2^2049) (hs : s^2 ≤ 2^2045) :
    (∏ i ∈ range (n+1), weight s (i+1) * (B*weight s i))^2 ≤
      2^((4*n+2) + 2049*(n+1) + 2045*(n+1)^2) := by
  rw [squared_weight_product]
  calc _ ≤ 2^(4*n+2) * (2^2049)^(n+1) * (2^2045)^((n+1)^2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB _)) (Nat.pow_le_pow_left hs _)
       _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]

/-- On the top pair of coordinates, a monic E_j gives (1,(-1)^j), and
x E_(j−1) gives (1,0). Here is the integral inverse of that block. -/
theorem recover_leading_pair (j : ℕ) (a b : ℤ) :
    let u := (-1:ℤ)^j * b
    let v := a-u
    u+v = a ∧ (-1:ℤ)^j*u = b := by
  dsimp
  constructor
  · ring
  · rw [← mul_assoc, ← pow_two, ← pow_mul, Nat.mul_comm, pow_mul]
    norm_num

/-- The difference of the two uniform squared determinant exponents is
positive and strictly less than one bit of radix in the cleared comparison. -/
theorem radix_gain_limit {t : ℕ} (ht : 0 < t) :
    let old := 2049*t*(t+1)
    let gap := (4*t-2)+2049*t+2045*t^2
    gap < old ∧ old < gap+2*t*(2*t+1) := by
  dsimp
  have h := Nat.sub_add_cancel (show 2 ≤ 4*t by omega)
  have hprod := Nat.mul_le_mul_right t (show 1 ≤ t by omega)
  constructor <;> nlinarith

/-- The squared column product at a uniform 2048-bit scale contributes
4t−2 plus 2049t plus 2045t² bits to the cleared LLL inequality. -/
def scale (t e : ℕ) : Prop :=
  let m := 2*t+1
  m^m * 2^(t*m + (4*t-2) + 2049*t + 2045*t^2) <
    2^(2*e*t*m) * (∏ j ∈ range m, j.factorial)^2

noncomputable instance (t e : ℕ) : Decidable (scale t e) := by
  unfold scale
  infer_instance

theorem small_scales : ∀ entry ∈ ([(1,684), (2,615), (3,585), (4,568),
    (8,541)] : List (ℕ × ℕ)), scale entry.1 entry.2 ∧ ¬scale entry.1 (entry.2-1) := by
  decide +kernel

end PrimeFactors.GapPolynomialScale
