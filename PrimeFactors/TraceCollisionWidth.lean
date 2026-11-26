import PrimeFactors.TraceProgression
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Interval.Finset.Nat

/-! Width of a band for the excess of a weighted sum over its geometric
minimum. Fix the first factor and vary the second; hence the modulus pq
also varies. The band center can, for example, be an integral multiple of
an order that depends on the first factor. -/

namespace PrimeFactors.TraceCollisionWidth

/-- Excess of the weighted sum over twice the geometric mean. -/
noncomputable def excess (a b p q : ℝ) : ℝ := (√(a*p)-√(b*q))^2

theorem excess_nonneg (a b p q : ℝ) : 0≤excess a b p q :=
  sq_nonneg _

theorem excess_eq {a b p q : ℝ} (a0 : 0≤a) (b0 : 0≤b) (p0 : 0≤p) (q0 : 0≤q) :
    excess a b p q = a*p+b*q-2*√(a*p)*√(b*q) := by
  unfold excess
  nlinarith only [Real.sq_sqrt (mul_nonneg a0 p0), Real.sq_sqrt (mul_nonneg b0 q0)]

/-- After passing to square-root coordinates, the two sides of the
stationary point are handled at the endpoint nearest to it. -/
private theorem root_separation {x y t c R : ℝ} (x0 : 0≤x) (t0 : 0≤t)
    (c0 : 0≤c) (order : x≤y) (yc : y≤c) (tc : t≤2*c) (R0 : 0≤R)
    (side : R≤x^2-t^2 ∨ R≤t^2-y^2) : 2*R≤3*c*|x+y-2*t| := by
  rcases side with right | left
  · have tx := (sq_le_sq₀ t0 x0).mp (show t^2≤x^2 by linarith)
    rw [abs_of_nonneg (show 0≤x+y-2*t by linarith)]
    have endpt := mul_le_mul_of_nonneg_right (show x+t≤3*c by linarith) (sub_nonneg.mpr tx)
    nlinarith only [right,endpt,mul_nonneg c0 (sub_nonneg.mpr order)]
  · have yt := (sq_le_sq₀ (x0.trans order) t0).mp (show y^2≤t^2 by linarith)
    rw [abs_of_nonpos (show x+y-2*t≤0 by linarith)]
    have endpt := mul_le_mul_of_nonneg_right (show t+y≤3*c by linarith) (sub_nonneg.mpr yt)
    nlinarith only [left,endpt,mul_nonneg c0 (sub_nonneg.mpr order)]

/-- On either side at residual distance at least R, a separation y-x
forces a proportional separation of the two excesses. The weights can
be in either order. -/
theorem separation {a b p U R x y : ℝ} (bpos : 0<b) (a0 : 0≤a)
    (cap : a≤2*b) (p0 : 0≤p) (pU : p≤U) (r0 : 0≤R)
    (x0 : 0≤x) (xy : x≤y) (yU : y≤U)
    (side : R≤b*x-a*p ∨ R≤a*p-b*y) :
    (y-x)*R ≤ 3*U*|excess a b p y-excess a b p x| := by
  let X := √(b*x)
  let Y := √(b*y)
  let T := √(a*p)
  let C := √(b*U)
  have sx : X^2=b*x := Real.sq_sqrt (mul_nonneg bpos.le x0)
  have sy : Y^2=b*y := Real.sq_sqrt (mul_nonneg bpos.le (x0.trans xy))
  have st : T^2=a*p := Real.sq_sqrt (mul_nonneg a0 p0)
  have sc : C^2=b*U := Real.sq_sqrt (mul_nonneg bpos.le (p0.trans pU))
  have hC : 0≤C := Real.sqrt_nonneg _
  have hxy : X≤Y := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left xy bpos.le)
  have hyc : Y≤C := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left yU bpos.le)
  have htc : T≤2*C := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) hC)).mp
    have prod := mul_le_mul cap pU p0 (show 0≤2*b by linarith)
    nlinarith only [st,sc,prod,sq_nonneg C]
  have step := root_separation (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hC hxy hyc htc r0
    (by simpa only [sx,sy,st] using side : R≤X^2-T^2 ∨ R≤T^2-Y^2)
  have factor : |excess a b p y-excess a b p x|=(Y-X)*|X+Y-2*T| := by
    change |(T-Y)^2-(T-X)^2|=_
    rw [show (T-Y)^2-(T-X)^2=(Y-X)*(X+Y-2*T) by ring,abs_mul,abs_of_nonneg (sub_nonneg.mpr hxy)]
  have spend : (Y+X)*R ≤ 3*C^2*|X+Y-2*T| := calc
    _ ≤ (2*C)*R := mul_le_mul_of_nonneg_right (by linarith) r0
    _ = C*(2*R) := by ring
    _ ≤ C*(3*C*|X+Y-2*T|) := mul_le_mul_of_nonneg_left step hC
    _ = _ := by ring
  apply le_of_mul_le_mul_left (a:=b) _ bpos
  calc
    b*((y-x)*R) = (Y-X)*((Y+X)*R) := by
      have eq : b*(y-x)=(Y-X)*(Y+X) := by nlinarith only [sx,sy]
      rw [←mul_assoc,eq,mul_assoc]
    _ ≤ (Y-X)*(3*C^2*|X+Y-2*T|) := mul_le_mul_of_nonneg_left spend (sub_nonneg.mpr hxy)
    _ = b*(3*U*|excess a b p y-excess a b p x|) := by rw [sc,factor]; ring

/-- The center C of the common excess band is arbitrary. -/
theorem band_diameter {a b p U R L C x y : ℝ} (bpos : 0<b) (a0 : 0≤a)
    (cap : a≤2*b) (p0 : 0≤p) (pU : p≤U) (rpos : 0<R)
    (x0 : 0≤x) (xy : x≤y) (yU : y≤U)
    (side : R≤b*x-a*p ∨ R≤a*p-b*y)
    (bx : C≤excess a b p x ∧ excess a b p x≤C+L)
    (by' : C≤excess a b p y ∧ excess a b p y≤C+L) : y-x ≤ 3*U*L/R := by
  apply (le_div_iff₀ rpos).mpr
  apply (separation bpos a0 cap p0 pU rpos.le x0 xy yU side).trans
  have width : |excess a b p y-excess a b p x|≤L := abs_le.mpr ⟨by linarith,by linarith⟩
  exact mul_le_mul_of_nonneg_left width (mul_nonneg (by norm_num) (p0.trans pU))

/-- Number of integer partners on one side of the stationary point that
can occupy one band. No spacing assumption about primes is used. -/
theorem band_card {s : Finset ℕ} {a b p U R L C : ℝ}
    (bpos : 0<b) (a0 : 0≤a) (cap : a≤2*b) (p0 : 0≤p) (pU : p≤U) (rpos : 0<R)
    (qU : ∀ q∈s,(q:ℝ)≤U)
    (side : (∀ q∈s, R≤b*q-a*p) ∨ (∀ q∈s, R≤a*p-b*q))
    (band : ∀ q∈s, C≤excess a b p q ∧ excess a b p q≤C+L) :
    s.card ≤ ⌊3*U*L/R⌋₊+1 := by
  rcases s.eq_empty_or_nonempty with rfl | ne
  · simp
  let x := s.min' ne
  let y := s.max' ne
  have hx : x∈s := s.min'_mem ne
  have hy : y∈s := s.max'_mem ne
  have order : x≤y := s.le_max' x hx
  have gap : R≤b*x-a*p ∨ R≤a*p-b*y :=
    side.elim (fun h => Or.inl (h x hx)) (fun h => Or.inr (h y hy))
  have diam := band_diameter bpos a0 cap p0 pU rpos (Nat.cast_nonneg x)
    (show (x:ℝ)≤y by exact_mod_cast order) (qU y hy) gap (band x hx) (band y hy)
  have d : y-x≤⌊3*U*L/R⌋₊ := Nat.le_floor <| by simpa only [Nat.cast_sub order] using diam
  have count := Finset.card_le_card (show s⊆Finset.Icc x y from
    fun z hz => Finset.mem_Icc.mpr ⟨s.min'_le z hz,s.le_max' z hz⟩)
  rw [Nat.card_Icc] at count
  omega

/-- The excess minus the difference between the true trace and a candidate
label is the candidate's distance from the geometric minimum. Every tested
label is strictly less than one full tested prefix above that minimum. -/
theorem label_window {p q m g j : ℕ} {s : TraceCoverCertificate.Slope}
    (start : TraceCoverCertificate.validStart (p*q) s) (tested : j<m*g) :
    let delta : ℝ := ((s.a*p+s.b*q:ℕ):ℝ)-((s.start+s.step*j:ℕ):ℝ)
    0≤excess s.a s.b p q-delta ∧ excess s.a s.b p q-delta < ((s.step*(m*g):ℕ):ℝ) := by
  obtain ⟨_,_,_,first,previous⟩ := of_decide_eq_true start
  let v : ℝ := 2*√((s.a:ℝ)*p)*√((s.b:ℝ)*q)
  have positive : 0≤v := by dsimp [v]; positivity
  have square : v^2=((4*s.a*s.b*(p*q):ℕ):ℝ) := by
    dsimp [v]
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
    push_cast
    ring
  have base : v≤s.start := by
    apply (sq_le_sq₀ positive (Nat.cast_nonneg _)).mp
    rw [square]
    exact_mod_cast first
  have upper : (s.start:ℝ)<v+s.step := by
    rcases previous with small | prev
    · exact (show (s.start:ℝ)<s.step by exact_mod_cast small).trans_le (by linarith)
    · by_cases small : s.start<s.step
      · exact (show (s.start:ℝ)<s.step by exact_mod_cast small).trans_le (by linarith)
      have pred : ((s.start-s.step:ℕ):ℝ)<v := by
        apply (sq_lt_sq₀ (Nat.cast_nonneg _) positive).mp
        rw [square]
        exact_mod_cast prev
      rw [Nat.cast_sub (by omega)] at pred
      linarith
  have included : (s.step:ℝ)*j+s.step ≤ s.step*(m*g:ℕ) := by
    exact_mod_cast (show s.step*j+s.step ≤ s.step*(m*g) by
      simpa only [Nat.mul_add,Nat.mul_one] using Nat.mul_le_mul_left s.step (Nat.succ_le_of_lt tested))
  dsimp only
  rw [excess_eq (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  change 0≤(s.a*p+s.b*q-v)-_ ∧ (s.a*p+s.b*q-v)-_ < _
  push_cast at included ⊢
  constructor
  · linarith only [base,mul_nonneg (Nat.cast_nonneg s.step : 0≤(s.step:ℝ)) (Nat.cast_nonneg j)]
  · linarith only [upper,included]

end PrimeFactors.TraceCollisionWidth
