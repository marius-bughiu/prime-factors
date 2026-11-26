import PrimeFactors.PersistentLocalSurvivors
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.FieldSimp

/-! Sharp lengths of translated Fermat-midpoint intervals surviving the dyadic
square sieve, and their implications for intervals of possible divisors. -/

namespace PrimeFactors.ShiftedDyadicMidpoints

open PersistentLocalSurvivors

/-- The same midpoint passes the square congruence at every finite binary precision. -/
def Survives (n h : ℤ) : Prop := ∀ e : ℕ, IsSquare ((h^2-n : ℤ) : ZMod (2^e))

/-- Sharp universal number of consecutive midpoints required in each odd residue class. -/
def length (n : ℤ) : ℤ := if n%8=1 then 62 else if n%8=5 then 14 else 4

/-- The two opposite odd remainders cannot both lie in the last two slots of
one period divisible by four: their offsets have the same parity and differ. -/
private theorem mirror {m r : ℤ} (pos : 0<m) (m4 : 4∣m) (odd : Odd r) (a : ℤ) :
    ∃ i : ℤ, 0 ≤ i ∧ i<m-2 ∧ (m∣a+i-r ∨ m∣a+i+r) := by
  obtain ⟨v,hv⟩ := m4
  obtain ⟨s,hs⟩ := odd
  let i := (r-a)%m
  let j := (-r-a)%m
  have parts (z : ℤ) : z=z%m+4*(v*(z/m)) := by
    rw [←mul_assoc,←hv]; exact (Int.emod_add_ediv z m).symm
  have hi : 0 ≤ i := Int.emod_nonneg _ pos.ne'
  have hj : 0≤j := Int.emod_nonneg _ pos.ne'
  have ui : i<m := Int.emod_lt_of_pos _ pos
  have uj : j<m := Int.emod_lt_of_pos _ pos
  have pi : r-a=i+4*(v*((r-a)/m)) := parts _
  have pj : -r-a=j+4*(v*((-r-a)/m)) := parts _
  have short : i<m-2 ∨ j<m-2 := by omega
  rcases short with h|h
  · exact ⟨i,hi,h,Or.inl ⟨-((r-a)/m),by have := Int.emod_add_ediv (r-a) m; dsimp [i]; linear_combination this⟩⟩
  · exact ⟨j,hj,h,Or.inr ⟨-((-r-a)/m),by have := Int.emod_add_ediv (-r-a) m; dsimp [j]; linear_combination this⟩⟩

/-- Translating or reflecting a root modulo an even period preserves its
square modulo twice that period. -/
private theorem square_period {m h r : ℤ} (even : Even m) (step : m∣h-r ∨ m∣h+r) :
    2*m∣h^2-r^2 := by
  obtain ⟨v,hv⟩ := even
  rcases step with ⟨z,hz⟩|⟨z,hz⟩
  · refine ⟨r*z+v*z^2,?_⟩
    rw [show h=r+m*z by omega,hv]; ring
  · refine ⟨-r*z+v*z^2,?_⟩
    rw [show h= -r+m*z by omega,hv]; ring

/-- An odd root in the stated class supplies two opposite regular classes. -/
private theorem odd_class {m n c r : ℤ} (pos : 0<m) (m4 : 4∣m) (even : Even m)
    (odd : Odd r) (base : 2*m∣n+c-r^2) (a : ℤ) :
    ∃ i : ℤ, 0 ≤ i ∧ i<m-2 ∧ 2*m∣(a+i)^2-n-c := by
  obtain ⟨i,lo,hi,h⟩ := mirror pos m4 odd a
  obtain ⟨x,hx⟩ := square_period even h
  obtain ⟨y,hy⟩ := base
  exact ⟨i,lo,hi,x-y,by linear_combination hx-hy⟩

/-- Every translated interval of the indicated length contains a permanent
survivor, regardless of how the start was calculated from the whole product. -/
theorem shifted {n : ℤ} (odd : n%2=1) (a : ℤ) :
    ∃ i : ℤ, 0 ≤ i ∧ i<length n ∧ Survives n (a+i) := by
  by_cases h1 : n%8=1
  · obtain ⟨r,hr,root⟩ := LocalMidpointLanes.lift_eight (D:=n+16) (by omega) 4
    obtain ⟨i,lo,hi,k,hk⟩ := odd_class (m:=64) (by decide) (by decide) (by decide) hr root a
    refine ⟨i,lo,by simpa only [length,if_pos h1] using hi,?_⟩
    apply dyadic_lifts; simp only [dyadicGood,Bool.or_eq_true,beq_iff_eq]
    right
    have : (a+i)^2-n=128*k+16 := by linarith only [hk]
    omega
  by_cases h5 : n%8=5
  · obtain ⟨r,hr,root⟩ := LocalMidpointLanes.lift_eight (D:=n+4) (by omega) 2
    obtain ⟨i,lo,hi,k,hk⟩ := odd_class (m:=16) (by decide) (by decide) (by decide) hr root a
    refine ⟨i,lo,by simpa only [length,if_neg h1,if_pos h5] using hi,?_⟩
    apply dyadic_lifts; simp only [dyadicGood,Bool.or_eq_true,beq_iff_eq]
    left; right
    have : (a+i)^2-n=32*k+4 := by linarith only [hk]
    omega
  have small : n%8=3 ∨ n%8=7 := by omega
  let r : ℤ := if n%8=3 then 2 else 0
  let i := (r-a)%4
  have hi : i<4 := Int.emod_lt_of_pos (r-a) (by decide : (0:ℤ)<4)
  refine ⟨i,Int.emod_nonneg _ (by decide),by simpa only [length,if_neg h1,if_neg h5] using hi,?_⟩
  have step : (4:ℤ)∣(a+i)-r := ⟨-((r-a)/4),by dsimp [i]; have := Int.emod_add_ediv (r-a) 4; omega⟩
  obtain ⟨k,hk⟩ := square_period (m:=4) (by decide) (Or.inl step)
  apply dyadic_lifts; simp only [dyadicGood,Bool.or_eq_true,beq_iff_eq]; left; left
  rcases small with h|h <;> simp [r,h] at hk <;> omega

/-- The public image of the final divisor interval under x ↦ (x+N/x)/2. -/
noncomputable def midpoint (n x : ℝ) : ℝ := (x+n/x)/2

theorem span {n l u : ℝ} (lp : 0<l) (le : l≤u) :
    midpoint n l-midpoint n u=(u-l)*(n-l*u)/(2*l*u) := by
  unfold midpoint; field_simp [lp.ne', (lp.trans_le le).ne']; ring

/-- For a smaller-factor interval, this width condition forces a local
survivor between the exact rational endpoint midpoints. -/
theorem divisor_interval {n : ℤ} {l u : ℝ} (odd : n%2=1) (lp : 0<l) (le : l≤u)
    (wide : (length n:ℝ)*(2*l*u)≤(u-l)*((n:ℝ)-l*u)) :
    ∃ h : ℤ, midpoint n u≤h ∧ (h:ℝ)≤midpoint n l ∧ Survives n h := by
  have up := lp.trans_le le
  have w : (length n:ℝ) ≤ midpoint n l-midpoint n u := by
    rw [span lp le]; exact (le_div_iff₀ (by positivity)).mpr wide
  obtain ⟨i,lo,hi,surv⟩ := shifted odd ⌈midpoint n u⌉
  refine ⟨⌈midpoint n u⌉+i,?_,?_,surv⟩
  · push_cast; linarith only [Int.le_ceil (midpoint n u),show (0:ℝ) ≤ i by exact_mod_cast lo]
  · push_cast; have bound : (i:ℝ)+1≤(length n:ℝ) := by exact_mod_cast (show i+1≤length n by omega)
    linarith only [bound,w,Int.ceil_lt_add_one (midpoint n u)]

/-- Proximity to the stationary point costs a quadratic width. Away from
it `divisor_interval` uses the exact endpoint span and needs less. -/
theorem stationary_bound {n : ℤ} {l u : ℝ} (odd : n%2=1) (lp : 0<l) (le : l≤u)
    (smaller : u^2≤(n:ℝ)) (wide : 124*l≤(u-l)^2) :
    ∃ h : ℤ, midpoint n u≤h ∧ (h:ℝ)≤midpoint n l ∧ Survives n h := by
  apply divisor_interval odd lp le
  have bound : (length n:ℝ)≤62 := by
    exact_mod_cast (show length n≤62 by unfold length; split_ifs <;> decide)
  have up := lp.trans_le le
  have top : u*(u-l) ≤ (n:ℝ)-l*u := by nlinarith only [smaller]
  have h := mul_le_mul_of_nonneg_left top (sub_nonneg.mpr le)
  calc
    _ ≤ 62*(2*l*u) := mul_le_mul_of_nonneg_right bound (by positivity)
    _ = u*(124*l) := by ring
    _ ≤ u*(u-l)^2 := mul_le_mul_of_nonneg_left wide up.le
    _ ≤ _ := by nlinarith only [h]

theorem full_width {n : ℤ} {l u : ℝ} (odd : n%2=1) (lp : 0<l) (le : l≤u)
    (smaller : u^2≤(n:ℝ)) (factor_cap : l≤2^1024) (width : 2^516≤u-l) :
    ∃ h : ℤ, midpoint n u≤h ∧ (h:ℝ)≤midpoint n l ∧ Survives n h := by
  apply stationary_bound odd lp le smaller
  calc
    _ ≤ 124*2^1024 := mul_le_mul_of_nonneg_left factor_cap (by norm_num)
    _ ≤ (2^516:ℝ)^2 := by norm_num [←pow_mul]
    _ ≤ (u-l)^2 := by gcongr

/-- With an even weighted product, every odd trace passes the dyadic tests:
its discriminant is 1 modulo 8, at all precisions simultaneously. -/
theorem even_weight (t s : ℤ) (even : Even t) (odd : Odd s) : Survives (4*t) s := by
  obtain ⟨k,hk⟩ := even
  obtain ⟨v,hv⟩ := odd
  have dvd : (8:ℤ)∣s^2-4*t-1 := by
    rcases Int.even_or_odd v with ⟨z,hz⟩|⟨z,hz⟩
    · refine ⟨z*(2*z+1)-k,?_⟩; rw [hk,hv,hz]; ring
    · refine ⟨(z+1)*(2*z+1)-k,?_⟩; rw [hk,hv,hz]; ring
  obtain ⟨v,h⟩ := dvd
  apply dyadic_lifts; simp only [dyadicGood,Bool.or_eq_true,beq_iff_eq]; left; left
  omega

/-- For odd weighted product, putting x=a*p and t=a*b*N yields a Fermat
midpoint (a*p+b*N/p)/2. The endpoint test works for any supplied placement. -/
theorem weighted_interval {n a b : ℤ} {l u : ℝ} (ap : 0<a) (odd : (a*b*n)%2=1)
    (lp : 0<l) (le : l≤u)
    (width : (length (a*b*n):ℝ)*(2*l*u)≤(u-l)*((b:ℝ)*n-(a:ℝ)*l*u)) :
    ∃ h : ℤ, ((a:ℝ)*u+(b:ℝ)*n/u)/2≤h ∧ (h:ℝ)≤((a:ℝ)*l+(b:ℝ)*n/l)/2 ∧ Survives (a*b*n) h := by
  have pos : (0:ℝ)<a := by exact_mod_cast ap
  have up := lp.trans_le le
  have cap : (length (a*b*n):ℝ)*(2*((a:ℝ)*l)*((a:ℝ)*u)) ≤
      ((a:ℝ)*u-(a:ℝ)*l)*(((a*b*n:ℤ):ℝ)-(a:ℝ)*l*((a:ℝ)*u)) := by
    push_cast; nlinarith only [mul_le_mul_of_nonneg_left width (sq_nonneg (a:ℝ))]
  obtain ⟨h,lo,hi,pass⟩ := divisor_interval odd (mul_pos pos lp) (mul_le_mul_of_nonneg_left le pos.le) cap
  have eq (x : ℝ) (xp : 0<x) : midpoint (a*b*n:ℤ) ((a:ℝ)*x)=((a:ℝ)*x+(b:ℝ)*n/x)/2 := by
    unfold midpoint; push_cast; field_simp [pos.ne',xp.ne']; ring
  exact ⟨h,eq u up ▸ lo,eq l lp ▸ hi,pass⟩

/-- Each finite check ranges only over offsets and 256 possible roots. -/
def Misses (n a count : ℕ) : Prop := ∀ i : Fin count, ∀ r : ZMod 256,
    (((a:ℤ)+(i.val:ℤ))^2-(n:ℤ) : ZMod 256) ≠ r*r

/-- Sharpness in all four odd residue classes. The first example is an actual
balanced semiprime with the rejected block inside the balanced midpoint range. -/
theorem sharp_examples : Misses 2022961 1442 61 ∧ Misses 3 3 3 ∧ Misses 13 10 13 ∧ Misses 7 1 3 := by
  unfold Misses; decide +kernel

/-- On the sharp 61-midpoint example the single modulus excludes 192
consecutive smaller-factor candidates, with no primality assumption on them. -/
theorem excluded_example {d : ℕ} (lower : 1018≤d) (upper : d≤1209) : ¬d∣2022961 := by
  rintro ⟨q,prod⟩
  have prodZ : (2022961:ℤ)=(d:ℤ)*q := by exact_mod_cast prod
  have dlo : (1018:ℤ)≤d := by exact_mod_cast lower
  have dhi : (d:ℤ)≤1209 := by exact_mod_cast upper
  have dp : (0:ℤ)<d := by omega
  have oddProd : Odd ((d:ℤ)*q) := by rw [←prodZ]; decide
  obtain ⟨⟨v,hv⟩,⟨w,hw⟩⟩ := Int.odd_mul.mp oddProd
  let h := v+w+1
  have trace : 2*h*d=(d:ℤ)^2+2022961 := by dsimp [h]; rw [prodZ,hv,hw]; ring
  have left : 2*1441*(d:ℤ)<2*h*d := by
    rw [trace]; nlinarith only [mul_nonneg (sub_nonneg.mpr dhi) (show (0:ℤ)≤2882-1209-d by omega)]
  have right : 2*h*(d:ℤ)<2*1503*d := by
    rw [trace]; nlinarith only [mul_nonneg (sub_nonneg.mpr dlo) (show (0:ℤ)≤3006-1018-d by omega)]
  have lo := (mul_lt_mul_right dp).mp left
  have hi := (mul_lt_mul_right dp).mp right
  let i : Fin 61 := ⟨(h-1442).toNat,by omega⟩
  have offset : (1442:ℤ)+i.val=h := by dsimp [i]; omega
  have sq : (1442+(i.val:ℤ))^2-2022961=(v-w)*(v-w) := by rw [offset,prodZ,hv,hw]; dsimp [h]; ring
  apply sharp_examples.1 i ((v-w:ℤ):ZMod 256)
  simpa using congrArg (fun z : ℤ => (z:ZMod 256)) sq

theorem example_factorization : Nat.Prime 1013 ∧ Nat.Prime 1997 ∧ 1013*1997=2022961 := by decide +kernel

end PrimeFactors.ShiftedDyadicMidpoints
