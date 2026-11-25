import PrimeFactors.UnitQuarticRecovery
import PrimeFactors.Fermat

namespace PrimeFactors.CenteredSumQuartic
open QuarticFactorLane

/-- Coefficients of 1, T, Z, T²−2s², ZT with T=x+y−h and Z=x−c. -/
noncomputable def coordinates (N h c s : ℤ) (v : Fin 5 → ℤ) : Weights where
  a := v 1 + v 2 - 2*h*v 3 - (h+c)*v 4
  b := v 1 - 2*h*v 3 - c*v 4
  c := v 3 + v 4
  d := v 3
  e := v 0 - h*v 1 - c*v 2 + (2*N+h^2-2*s^2)*v 3 + (N+c*h)*v 4

theorem trace_eq {x y N : ℤ} (pair : x*y=N) (h c s : ℤ) (v : Fin 5 → ℤ) :
    trace (coordinates N h c s v) x y =
      ∑ i, v i * UnitQuarticRecovery.terms (x-c) (h-c-y) s i := by
  rw [← pair]
  simp [trace, coordinates, UnitQuarticRecovery.terms, Fin.sum_univ_succ]
  ring

/-- A common upper bound on the factors also bounds their sum, with integer rounding. -/
theorem sum_upper {x y N U : ℕ} (pair : x*y=N) (pos : 0<U) (hx : x≤U) (hy : y≤U) :
    x+y ≤ U+N/U := by
  have cross : (x+y)*U ≤ N+U*U := by
    zify at pair hx hy ⊢
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have divided := (Nat.le_div_iff_mul_le pos).mpr cross
  rwa [Nat.add_mul_div_right _ _ pos, Nat.add_comm (N/U)] at divided

/-- Both centers and radii used by the input-dependent search, including odd widths. -/
theorem dynamic_widths {x y N L U : ℕ} (pair : x*y=N) (pos : 0<U)
    (lo : L≤x) (hx : x≤U) (hy : y≤U) :
    let A := ceilSqrt (4*N)
    let B := U+N/U
    |(x:ℤ)+y-(((A+B)/2 : ℕ):ℤ)| ≤ 2*(max 1 ((B-A+3)/4) : ℕ) ∧
      |(x:ℤ)-(((L+U)/2 : ℕ):ℤ)| ≤ (max 1 ((U-L+1)/2) : ℕ) := by
  have sumLo : ceilSqrt (4*N) ≤ x+y := ceilSqrt_le_iff.mpr
    (by nlinarith [sq_nonneg ((x:ℤ)-y)])
  have sumHi := sum_upper pair pos hx hy
  dsimp only
  constructor <;> apply abs_le.mpr <;> constructor <;> omega

private theorem nonzero {p q : Fin 5 → ℤ} (ne : p ≠ q) (N h c s : ℤ) :
    let w := coordinates N h c s (p-q)
    w.a ≠ 0 ∨ w.b ≠ 0 ∨ w.c ≠ 0 ∨ w.d ≠ 0 ∨ w.e ≠ 0 := by
  dsimp only
  by_contra! all
  obtain ⟨ha,hb,hc,hd,he⟩ := all
  simp [coordinates] at ha hb hc hd he
  have f3 : p 3=q 3 := by omega
  simp [f3] at hc
  have f4 : p 4=q 4 := by omega
  simp [f3,f4] at hb
  have f1 : p 1=q 1 := by omega
  simp [f1,f3,f4] at ha
  have f2 : p 2=q 2 := by omega
  apply ne
  funext i
  fin_cases i <;> simp_all
  omega

/-- The two centers and all bounds are public. Each accepted residue class has
a nonzero quartic with at most four integer roots covering its factor pairs. -/
theorem from_windows {N h c : ℤ} {R s H : ℕ} (hN : N≠0)
    (hr : 0<R) (hs : 0<s) (hH : 0<H) (unit : IsCoprime (360*(R:ℤ)^4) N)
    (localCop : IsCoprime (8*(R:ℤ)^4) 45)
    (scale : 5^5 * (∏ i, UnitQuarticBox.weight s H i) < R^10*12960) (u : ℤ) :
    ∃ v : Fin 5 → ℤ, v≠0 ∧
      (∑ i, |v i| * (UnitQuarticBox.weight s H i : ℤ)) < 360*(R:ℤ)^4 ∧
      let w := coordinates N h c s v
      (∀ z : ℤ, z ≡ u [ZMOD (R:ℤ)] → IsCoprime z 30 → 360*(R:ℤ)^4 ∣ value w N z) ∧
      (candidates w N).card≤4 ∧
      ∀ x y : ℤ, x*y=N → |x+y-h|≤2*(s:ℤ) → |x-c|≤(H:ℤ) →
        x ≡ u [ZMOD (R:ℤ)] → x ∈ candidates w N := by
  letI : NeZero R := ⟨hr.ne'⟩
  let label (v : Fin 5 → ℤ) := QuarticUnitLabels.label R u N (coordinates N h c s v)
  obtain ⟨p,q,ne,same,short⟩ := UnitQuarticBox.quartic_collision hr hs hH
    (QuarticUnitLabels.card_labels R).le scale label
  let w := coordinates N h c s (p-q)
  have valid (z : ℤ) (lane : z ≡ u [ZMOD (R:ℤ)]) (cz : IsCoprime z 30) :
      360*(R:ℤ)^4 ∣ value w N z := by
    have eqn : value w N z = value (coordinates N h c s p) N z -
        value (coordinates N h c s q) N z := by simp [w, value, coordinates]; ring
    rw [eqn]
    exact QuarticUnitLabels.divides_of_label_eq_at localCop same lane cz
  refine ⟨p-q, sub_ne_zero.mpr ne, short, valid, candidates_card .., ?_⟩
  intro x y pair sumRange xRange lane
  have cx := (show IsCoprime (360*(R:ℤ)^4) (x*y) by rwa [pair]).of_mul_right_left
  have div := valid x lane (cx.symm.of_isCoprime_of_dvd_right ⟨12*(R:ℤ)^4, by ring⟩)
  rw [pair_identity _ pair] at div
  have size : |trace w x y| < 360*(R:ℤ)^4 := by
    rw [show trace w x y = _ from trace_eq pair h c s (p-q)]
    apply (UnitQuarticRecovery.terms_bound (p-q) _ xRange).trans_lt short
    rwa [show x-c-(h-c-y)=x+y-h by ring]
  have zero := Int.eq_zero_of_abs_lt_dvd (cx.pow_right.dvd_of_dvd_mul_left div) size
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots (polynomial_nonzero hN (nonzero ne N h c s))).mpr
  rw [Polynomial.IsRoot, eval_polynomial, pair_identity _ pair, zero, mul_zero]

/-- The square root of 4N and the common bit width give a short interval for the sum. -/
theorem widths {x y N k : ℕ} (pair : x*y=N) (size : 2*(64*k)^2 ≤ N)
    (lx : 64*k≤x) (ux : x≤128*k) (ly : 64*k≤y) (uy : y≤128*k) :
    let K := ceilSqrt (4*N)
    |(x:ℤ)+y-((K:ℤ)+6*k)|≤2*(3*(k:ℤ)) ∧ |(x:ℤ)-96*k|≤32*(k:ℤ) := by
  let K := ceilSqrt (4*N)
  have ksq : 4*N ≤ K^2 := ceilSqrt_le_iff.mp le_rfl
  have ksum : K ≤ x+y := ceilSqrt_le_iff.mpr (by nlinarith [sq_nonneg ((x:ℤ)-y)])
  have kmin : 168*k ≤ K := (Nat.pow_le_pow_iff_left (by decide : (2:ℕ)≠0)).mp (by
    calc (168*k)^2 ≤ 4*(2*(64*k)^2) := by nlinarith [Nat.zero_le (k*k)]
         _ ≤ 4*N := Nat.mul_le_mul_left _ size
         _ ≤ K^2 := ksq)
  have gap : ((x:ℤ)-y)^2 ≤ (64*(k:ℤ))^2 := sq_le_sq' (by omega) (by omega)
  have upper : x+y ≤ K+12*k := by
    apply le_of_not_gt
    intro hyp
    have step := Nat.pow_lt_pow_left hyp (by decide : 2≠0)
    have kg := Nat.mul_le_mul_right k kmin
    zify at pair step kg ksq
    nlinarith [sq_nonneg (k:ℤ)]
  change |(x:ℤ)+y-((K:ℤ)+6*k)|≤_ ∧ _
  constructor <;> apply abs_le.mpr <;> constructor <;> omega

private theorem scaled_class {k e N : ℕ} (hk : 0<k) (pos : N≠0)
    (size : 2*(64*k)^2 ≤ N) (cop : N.Coprime 30)
    (scale : 5^5 * (∏ i, UnitQuarticBox.weight (3*k) (32*k) i) < ((2:ℕ)^e)^10*12960)
    (u : ℤ) :
    let h : ℤ := (ceilSqrt (4*N):ℤ)+6*k
    ∃ v : Fin 5 → ℤ, v≠0 ∧
      (∑ i, |v i| * (UnitQuarticBox.weight (3*k) (32*k) i : ℤ)) < 360*((2:ℤ)^e)^4 ∧
      let w := coordinates N h (96*(k:ℤ)) (3*(k:ℤ)) v
      (∀ z : ℤ, z ≡ u [ZMOD (2:ℤ)^e] → IsCoprime z 30 →
        360*((2:ℤ)^e)^4 ∣ value w N z) ∧
      (candidates w N).card≤4 ∧
      ∀ x y : ℕ, x*y=N → 64*k≤x → x<128*k → 64*k≤y → y<128*k →
        (x:ℤ) ≡ u [ZMOD (2:ℤ)^e] → (x:ℤ) ∈ candidates w N := by
  let h : ℤ := (ceilSqrt (4*N):ℤ)+6*k
  have unit : IsCoprime (360*(((2^e:ℕ):ℤ))^4) (N:ℤ) := by
    have dc := (cop.symm.pow_left 3).of_dvd_left (by decide : 360 ∣ 30^3)
    have dr := cop.symm.of_dvd_left (by decide : 2 ∣ 30)
    exact_mod_cast (Nat.coprime_mul_iff_left.mpr ⟨dc,(dr.pow_left e).pow_left 4⟩).isCoprime
  have two : IsCoprime (2:ℤ) 45 := Int.isCoprime_iff_gcd_eq_one.mpr (by decide)
  have eight : IsCoprime (8:ℤ) 45 := Int.isCoprime_iff_gcd_eq_one.mpr (by decide)
  have odd : IsCoprime (8*(((2^e:ℕ):ℤ))^4) 45 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    have pow : IsCoprime ((2:ℤ)^e) 45 := two.pow_left
    exact eight.mul_left pow.pow_left
  obtain ⟨v,ne,short,modular,card,covers⟩ := from_windows (h := h) (c := 96*(k:ℤ))
    (by exact_mod_cast pos) (by positivity : 0<(2:ℕ)^e) (by positivity) (by positivity) unit odd scale u
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at short modular card covers
  refine ⟨v,ne,short,modular,card,?_⟩
  intro x y pair lx ux ly uy lane
  have limits := widths pair size lx ux.le ly uy.le
  exact covers x y (by exact_mod_cast pair) limits.1 limits.2 lane

set_option exponentiation.threshold 16384 in
private theorem full_scale :
    5^5 * (∏ i, UnitQuarticBox.weight (3*2^1017) (32*2^1017) i) <
      ((2:ℕ)^612)^10*12960 := by
  rw [UnitQuarticBox.weight_product]
  decide +kernel

set_option exponentiation.threshold 16384 in
set_option maxRecDepth 8192 in
/-- For every 2048-bit product of two 1024-bit primes, a specified positive
factor remainder modulo 2^612 can be checked with one quartic. -/
theorem every_2048_class (N : ℕ) (size : 2^2047≤N) (cop : N.Coprime 30) (u : ℤ) :
    let k : ℕ := 2^1017
    let h : ℤ := (ceilSqrt (4*N):ℤ)+6*k
    ∃ v : Fin 5 → ℤ, v≠0 ∧
      (∑ i, |v i| * (UnitQuarticBox.weight (3*k) (32*k) i : ℤ)) < 360*((2:ℤ)^612)^4 ∧
      let w := coordinates N h (96*(k:ℤ)) (3*(k:ℤ)) v
      (∀ z : ℤ, z ≡ u [ZMOD (2:ℤ)^612] → IsCoprime z 30 →
        360*((2:ℤ)^612)^4 ∣ value w N z) ∧
      (candidates w N).card≤4 ∧
      ∀ x y : ℕ, x*y=N → 2^1023≤x → x<2^1024 → 2^1023≤y → y<2^1024 →
        (x:ℤ) ≡ u [ZMOD (2:ℤ)^612] → (x:ℤ) ∈ candidates w N := by
  have lower : 64*(2:ℕ)^1017=2^1023 := by decide +kernel
  have upper : 128*(2:ℕ)^1017=2^1024 := by decide +kernel
  have minimum : 2*(64*(2:ℕ)^1017)^2=2^2047 := by decide +kernel
  have pos : N≠0 := (lt_of_lt_of_le (pow_pos (by decide : 0<(2:ℕ)) 2047) size).ne'
  have result := scaled_class (k:=2^1017) (e:=612) (by positivity) pos (minimum.trans_le size) cop full_scale u
  simpa only [lower,upper] using result

end PrimeFactors.CenteredSumQuartic
