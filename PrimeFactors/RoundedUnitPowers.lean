import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! Repeated squaring of a number in the unit interval with downward
fixed-point rounding. The second output counts rounded multiplications. -/

namespace PrimeFactors.RoundedUnitPowers

def mul (D a b : ℕ) := a*b/D

/-- Stop at exponent zero or one. For larger exponents square the half
power and multiply by the input once more when the exponent is odd. -/
def run (D a : ℕ) : ℕ→ℕ→ℕ×ℕ
  | 0, n => if n=0 then (D,0) else (a,0)
  | k+1,n => if n=0 then (D,0) else if n=1 then (a,0) else
      let h := run D a k (n/2)
      let s := mul D h.1 h.1
      if n%2=0 then (s,h.2+1) else (mul D s a,h.2+2)

def eval (D a n : ℕ) := run D a (if n=0 then 0 else n.log2+1) n

theorem eval_eq (D a n : ℕ) : eval D a n=run D a n.size n := by
  by_cases zero : n=0
  · simp [eval,zero]
  have size : n.log2+1=n.size := le_antisymm (Nat.lt_size.mpr (Nat.log2_self_le zero))
    (Nat.size_le.mpr ((Nat.log2_lt zero).mp (Nat.lt_succ_self _)))
  simp only [eval,if_neg zero,size]

noncomputable def value (D a n : ℕ) : ℚ := ((eval D a n).1:ℚ)/D

/-- The unreduced product of two stored words fits below the squared scale,
and the rounded result fits back into one word of the original scale. -/
theorem mul_bounds {D a b : ℕ} (pos : 0<D) (aD : a≤D) (bD : b≤D) :
    a*b≤D^2 ∧ mul D a b≤D := by
  have cap : a*b≤D*D := Nat.mul_le_mul aD bD
  refine ⟨by simpa only [pow_two] using cap,?_⟩
  unfold mul
  exact (Nat.div_le_div_right cap).trans_eq (Nat.mul_div_cancel D pos)

theorem run_bounds {D a : ℕ} (pos : 0<D) (aD : a≤D) (k n : ℕ) :
    (run D a k n).1≤D ∧ (run D a k n).2≤2*k := by
  induction k generalizing n with
  | zero =>
    simp only [run]
    split <;> simp_all
  | succ k ih =>
    obtain ⟨cap,cost⟩ := ih (n/2)
    have sq := (mul_bounds pos cap cap).2
    have extra := (mul_bounds pos sq aD).2
    simp only [run]
    split
    · exact ⟨le_rfl,Nat.zero_le _⟩
    split
    · exact ⟨aD,Nat.zero_le _⟩
    split
    · exact ⟨sq,by omega⟩
    · exact ⟨extra,by omega⟩

theorem bounds {D a : ℕ} (pos : 0<D) (aD : a≤D) (n : ℕ) :
    (eval D a n).1≤D ∧ (eval D a n).2≤2*n.size := by
  rw [eval_eq]
  exact run_bounds pos aD ..

/-- Error in scaled integer units. -/
private def Acc (D word : ℕ) (x err : ℚ) : Prop :=
  (word:ℚ)≤D*x ∧ (D:ℚ)*x≤word+err

private theorem mul_acc {D a b : ℕ} {x y ex ey : ℚ} (pos : 0<D)
    (aD : a≤D) (yn : 0≤y) (yl : y≤1) (xa : Acc D a x ex) (yb : Acc D b y ey) :
    Acc D (mul D a b) (x*y) (ex+ey+1) := by
  obtain ⟨ax,ax'⟩ := xa
  obtain ⟨ay,ay'⟩ := yb
  have hp : (0:ℚ)<D := by exact_mod_cast pos
  have small : (a:ℚ)/D≤1 := (div_le_iff₀ hp).mpr (by simpa using (show (a:ℚ)≤D by exact_mod_cast aD))
  have an : 0≤(a:ℚ)/D := by positivity
  have g1 : 0≤((D:ℚ)*x-a)*y := mul_nonneg (by linarith) yn
  have g2 : 0≤((a:ℚ)/D)*(D*y-b) := mul_nonneg an (by linarith)
  have h1 : ((D:ℚ)*x-a)*y≤D*x-a := mul_le_of_le_one_right (by linarith) yl
  have h2 : ((a:ℚ)/D)*(D*y-b)≤D*y-b := mul_le_of_le_one_left (by linarith) small
  have rlo : ((mul D a b):ℚ)≤(a:ℚ)*b/D := (le_div_iff₀ hp).mpr (by
    exact_mod_cast Nat.div_mul_le_self (a*b) D)
  have rhi : (a:ℚ)*b/D < (mul D a b:ℚ)+1 := (div_lt_iff₀ hp).mpr (by
    have h : a*b<(mul D a b+1)*D := by simpa only [mul,Nat.mul_comm D _] using Nat.lt_mul_div_succ (a*b) pos
    exact_mod_cast h)
  have eq : (D:ℚ)*(x*y)-(mul D a b:ℚ) =
      (D*x-a)*y+(a/D)*(D*y-b)+(a*b/D-(mul D a b:ℚ)) := by
    field_simp
    ring
  constructor <;> linarith

private theorem accurate {D a : ℕ} {x : ℚ} (pos : 0<D) (aD : a≤D)
    (xn : 0≤x) (xl : x≤1) (base : Acc D a x 1) (k n : ℕ) (size : n<2^k) :
    Acc D (run D a k n).1 (x^n) (if n=0 then 0 else 2*(n:ℚ)-1) := by
  induction k generalizing n with
  | zero =>
    have zero : n=0 := by simpa using size
    subst n
    simp [run,Acc]
  | succ k ih =>
    by_cases zero : n=0
    · subst n
      simp [run,Acc]
    by_cases one : n=1
    · subst n
      norm_num [run]
      exact base
    let h := n/2
    have hp : 0<h := by dsimp [h]; omega
    have hw : h<2^k := by dsimp [h]; rw [pow_succ] at size; omega
    have approx := ih h hw
    rw [if_neg hp.ne'] at approx
    have cap := (run_bounds pos aD k h).1
    have hn := pow_nonneg xn h
    have hl := pow_le_one₀ xn xl (n:=h)
    have square := mul_acc pos cap hn hl approx approx
    by_cases even : n%2=0
    · have eq : n=h+h := by dsimp [h]; omega
      have power : x^n=x^h*x^h := by conv_lhs => rw [eq,pow_add]
      have err : 2*(n:ℚ)-1=(2*(h:ℚ)-1)+(2*(h:ℚ)-1)+1 := by
        have e : (n:ℚ)=h+h := by exact_mod_cast eq
        linarith
      simp only [run,if_neg zero,if_neg one,if_pos even, power, err]
      exact square
    · have eq : n=h+h+1 := by dsimp [h]; omega
      have power : x^n=(x^h*x^h)*x := by conv_lhs => rw [eq,pow_succ,pow_add]
      have err : 2*(n:ℚ)-1=((2*(h:ℚ)-1)+(2*(h:ℚ)-1)+1)+1+1 := by
        have e : (n:ℚ)=h+h+1 := by exact_mod_cast eq
        linarith
      simp only [run,if_neg zero,if_neg one,if_neg even, power,err]
      exact mul_acc pos (mul_bounds pos cap cap).2 xn xl square base

/-- The input word a may already have been rounded down by one scaled unit. -/
theorem approximation {D a n : ℕ} {x : ℚ} (pos : 0<D) (xn : 0≤x) (xl : x≤1)
    (lower : (a:ℚ)≤D*x) (upper : (D:ℚ)*x≤a+1) :
    0≤x^n-value D a n ∧ x^n-value D a n≤2*n/D := by
  have dp : 0<(D:ℚ) := by exact_mod_cast pos
  have small : a≤D := by
    exact_mod_cast lower.trans (mul_le_of_le_one_right dp.le xl)
  obtain ⟨lo,hi⟩ := accurate pos small xn xl ⟨lower,upper⟩ n.size n (Nat.lt_size_self n)
  rw [←eval_eq D a n] at lo hi
  change ((eval D a n).1:ℚ)≤D*x^n at lo
  change (D:ℚ)*x^n≤(eval D a n).1+(if n=0 then 0 else 2*(n:ℚ)-1) at hi
  have cap : (D:ℚ)*x^n≤(eval D a n).1+2*(n:ℚ) := by split at hi <;> linarith
  unfold value
  constructor
  · apply sub_nonneg.mpr
    exact (div_le_iff₀ dp).mpr (by linarith)
  · apply (le_div_iff₀ dp).mpr
    rw [sub_mul,div_mul_cancel₀ _ dp.ne']
    linarith

/-- A concrete scaled approximation guarantee, in absolute units of the
represented power, for all exponents up to 4B. -/
theorem precision {B D a n : ℕ} {x : ℚ} (bp : 0<B) (fit : 4096*B^2≤D)
    (exp : n≤4*B) (xn : 0≤x) (xl : x≤1)
    (lower : (a:ℚ)≤D*x) (upper : (D:ℚ)*x≤a+1) :
    0≤x^n-value D a n ∧ x^n-value D a n<1/(128*B) := by
  have pos : 0<D := lt_of_lt_of_le (by positivity) fit
  obtain ⟨al,au⟩ := approximation (n:=n) pos xn xl lower upper
  refine ⟨al,au.trans_lt ((div_lt_div_iff₀ (by exact_mod_cast pos) (by positivity)).mpr ?_)⟩
  have bound : 2*n*(128*B)<1*D := calc
    _ ≤ 2*(4*B)*(128*B) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ exp)
    _ = 1024*B^2 := by ring
    _ < 4096*B^2 := Nat.mul_lt_mul_of_pos_right (by decide) (by positivity)
    _ ≤ 1*D := by simpa using fit
  exact_mod_cast bound

def scale (B : ℕ) := 4096*B^2
def input (B : ℕ) := scale B-512*B
noncomputable def unitBase (B : ℕ) : ℚ := 1-1/(8*B)

/-- This base is exactly representable at the chosen scale. -/
theorem exact_input {B : ℕ} (bp : 0<B) : (input B:ℚ)=(scale B:ℚ)*unitBase B := by
  have sq : B≤B*B := by simpa using Nat.mul_le_mul_left B (show 1≤B by omega)
  have fit : 512*B≤4096*B^2 := by nlinarith only [sq,Nat.zero_le B]
  unfold input scale unitBase
  rw [Nat.cast_sub fit]
  push_cast
  have nz : (B:ℚ)≠0 := by exact_mod_cast bp.ne'
  field_simp
  ring

theorem fixed_grid {B n : ℕ} (bp : 0<B) (exp : n≤4*B) :
    0≤unitBase B^n-value (scale B) (input B) n ∧
    unitBase B^n-value (scale B) (input B) n<1/(128*B) := by
  have low : (1:ℚ)≤B := by exact_mod_cast bp
  have bn : 0≤unitBase B := by
    unfold unitBase
    exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr (by linarith))
  have top : unitBase B≤1 := by unfold unitBase; exact sub_le_self _ (by positivity)
  apply precision (D:=scale B) (a:=input B) bp le_rfl exp bn top (exact_input bp).le
  rw [exact_input bp]
  linarith

set_option exponentiation.threshold 8192 in
/-- For B=2^1023, each stored word is at most 2^2058. Every multiplication
has two such operands and yields an unreduced product at most 2^4116. -/
theorem full_width_work {n : ℕ} (cap : n≤4*(2^1023)) :
    (eval (scale (2^1023)) (input (2^1023)) n).1≤2^2058 ∧
    (eval (scale (2^1023)) (input (2^1023)) n).2≤2052 ∧
    ∀ a b : ℕ, a≤scale (2^1023) → b≤scale (2^1023) → a*b≤2^4116 := by
  have D : scale (2^1023)=2^2058 := by decide +kernel
  have pos : 0<scale (2^1023) := by rw [D]; positivity
  have res := bounds pos (Nat.sub_le (scale (2^1023)) (512*(2^1023))) n
  have bits : n.size≤1026 := Nat.size_le.mpr (cap.trans_lt (by decide +kernel))
  exact ⟨res.1.trans_eq D,res.2.trans (Nat.mul_le_mul_left 2 bits),fun a b ha hb =>
    (mul_bounds pos ha hb).1.trans_eq (by rw [D,←pow_mul])⟩

end PrimeFactors.RoundedUnitPowers
