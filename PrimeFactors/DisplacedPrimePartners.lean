import PrimeFactors.PrimeGapMultiplier

/-! Apply a one-sided prime-gap estimate beyond the 3/2 ratio, where
two finite weight-six search schedules cease to cover the same traces. -/
namespace PrimeFactors.DisplacedPrimePartners
open Real Finset InteriorBatchPopulation PrimeGapMultiplier

set_option exponentiation.threshold 8192

private theorem root_upper {w y : ℝ} (yp : 0<y) (large : 10000000 ≤ sqrt y)
    (upper : w-y ≤ 3530*sqrt y) : sqrt w ≤ (1001/1000)*sqrt y := by
  apply sqrt_le_iff.mpr ⟨by positivity,?_⟩
  have h := mul_le_mul_of_nonneg_right large (sqrt_nonneg y)
  nlinarith only [upper,h,sq_sqrt yp.le]

/-- Starting at 2900 square roots above the center still leaves room for
the full one-sided prime gap before 3530 square roots. -/
theorem displaced (gap : PrimeInInterval) {y : ℝ}
    (low : (2:ℝ)^1023 ≤ y) (high : y ≤ (2:ℝ)^1024) :
    ∃ q : ℕ, q.Prime ∧ 2900*sqrt y ≤ (q:ℝ)-y ∧ (q:ℝ)-y ≤ 3530*sqrt y ∧
      4199202 < 2*(sqrt q-sqrt y)^2 ∧ 2*(sqrt q-sqrt y)^2 ≤ 6230450 := by
  let x := y+2900*sqrt y
  have yp : 0<y := lt_of_lt_of_le (by norm_num) low
  have sy := sq_sqrt yp.le
  have large : 10000000 ≤ sqrt y :=
    (le_sqrt (by norm_num) yp.le).mpr (le_trans (by norm_num) low)
  have xlow : 4≤x := by dsimp [x]; linarith only [low,sqrt_nonneg y]
  have roof : x≤(2:ℝ)^1025 := by
    have h := mul_le_mul_of_nonneg_right large (sqrt_nonneg y)
    have xy : x≤2*y := by dsimp [x]; nlinarith only [h,sy,sqrt_nonneg y]
    calc x ≤ 2*y := xy
         _ ≤ 2*(2:ℝ)^1024 := mul_le_mul_of_nonneg_left high (by norm_num)
         _ = (2:ℝ)^1025 := by norm_num
  have lx : log x ≤ 711 := by
    have bound := log_le_log (by linarith : 0<x) roof
    rw [log_pow] at bound
    norm_num only [Nat.cast_ofNat] at bound
    linarith only [bound,log_two_lt_d9]
  have rx := root_upper yp large (w:=x) (by dsimp [x]; linarith only [sqrt_nonneg y])
  obtain ⟨q,prime,lq,uq⟩ := gap x xlow
  have nearLow : 2900*sqrt y ≤ (q:ℝ)-y := by dsimp [x] at lq; linarith only [lq]
  have nearHigh : (q:ℝ)-y ≤ 3530*sqrt y := by
    have h := mul_le_mul rx lx (log_nonneg (by linarith : 1≤x)) (by positivity)
    dsimp only [x] at uq h
    linarith only [uq,h,sqrt_nonneg y]
  have rq := root_upper yp large nearHigh
  have order : sqrt y ≤ sqrt (q:ℝ) := sqrt_le_sqrt (by linarith only [nearLow,sqrt_nonneg y])
  have span : (sqrt (q:ℝ)-sqrt y)*(sqrt q+sqrt y)=(q:ℝ)-y := by
    nlinarith only [sy,sq_sqrt (Nat.cast_nonneg q)]
  have rad : 0 < sqrt (q:ℝ)+sqrt y := by positivity
  have left : 1449 < sqrt (q:ℝ)-sqrt y := by
    by_contra! fail
    have t := mul_le_mul_of_nonneg_right fail rad.le
    linarith only [t,span,rq,nearLow,large]
  have right : sqrt (q:ℝ)-sqrt y ≤ 1765 := by
    by_contra! fail
    have t := mul_lt_mul_of_pos_right fail rad
    linarith only [t,span,order,nearHigh]
  refine ⟨q,prime,nearLow,nearHigh,?_,?_⟩
  · have h := pow_lt_pow_left₀ left (by norm_num : (0:ℝ)≤1449) (by decide : 2≠0)
    linarith only [h]
  · have h := pow_le_pow_left₀ (sub_nonneg.mpr order) right 2
    linarith only [h]

/-- Every eligible smaller prime has a partner whose true weighted trace
falls strictly between the odd-prefix cap and the mod-six-prefix cap. -/
theorem partner (gap : PrimeInInterval) {p : ℕ} (hp : p∈interior) :
    let y := 3*(p:ℝ)/2
    ∃ q∈neighbors p, q.Prime ∧ 2900*sqrt y ≤ (q:ℝ)-y ∧ (q:ℝ)-y ≤ 3530*sqrt y ∧
      let e := ((3*p+2*q:ℕ):ℝ)-2*sqrt (6*((p*q:ℕ):ℝ))
      4199202 < e ∧ e ≤ 6230450 := by
  let y := 3*(p:ℝ)/2
  have bounds := hp
  rw [InteriorBatchPopulation.interior,firstPrimes] at bounds
  obtain ⟨⟨pl,pu⟩,_⟩ := (show (79*(U/128)≤p ∧ p≤82*(U/128)) ∧ p.Prime by simpa using bounds)
  have yl : (2:ℝ)^1023 ≤ y := by
    have h : 2*(2:ℝ)^1023 ≤ 3*p := by exact_mod_cast
      (le_trans (by decide +kernel) (Nat.mul_le_mul_left 3 pl) : 2*2^1023≤3*p)
    dsimp [y]; linarith only [h]
  have yu : y ≤ (2:ℝ)^1024 := by
    have h : 3*(p:ℝ)≤2*(2:ℝ)^1024 := by exact_mod_cast
      (le_trans (Nat.mul_le_mul_left 3 pu) (by decide +kernel) : 3*p≤2*2^1024)
    dsimp [y]; linarith only [h]
  obtain ⟨q,prime,lo,hi,left,right⟩ := displaced gap yl yu
  have ry : sqrt y ≤ (2:ℝ)^512 :=
    sqrt_le_iff.mpr ⟨by positivity,yu.trans_eq (by norm_num)⟩
  have within : 3530*sqrt y ≤ V := le_trans (mul_le_mul_of_nonneg_left ry (by norm_num))
    (by norm_num [V])
  have ql : 3*p≤2*q+2*V := by
    have h : 3*(p:ℝ)≤2*q+2*(V:ℝ) := by dsimp [y] at lo; linarith only [lo,sqrt_nonneg (3*(p:ℝ)/2),show (0:ℝ)≤V by positivity]
    exact_mod_cast h
  have qu : 2*q≤3*p+2*V := by
    have h := hi.trans within
    have twice (a b v : ℝ) (bound : b-3*a/2 ≤ v) : 2*b ≤ 3*a+2*v := by linarith
    have hh := twice (p:ℝ) (q:ℝ) (V:ℝ) h
    exact_mod_cast hh
  have hq : q∈neighbors p := by
    rw [neighbors]
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,prime⟩
  have yp : 0<y := lt_of_lt_of_le (by norm_num) yl
  have root : sqrt (6*((p*q:ℕ):ℝ)) = 2*sqrt y*sqrt (q:ℝ) := by
    apply (sq_eq_sq₀ (sqrt_nonneg _) (by positivity)).mp
    rw [sq_sqrt (by positivity),mul_pow,mul_pow,sq_sqrt (Nat.cast_nonneg q),sq_sqrt yp.le]
    dsimp [y]; push_cast; ring
  have id : ((3*p+2*q:ℕ):ℝ)-2*sqrt (6*((p*q:ℕ):ℝ))=2*(sqrt q-sqrt y)^2 := by
    rw [root]
    have sy := sq_sqrt yp.le
    dsimp [y] at sy ⊢
    push_cast
    nlinarith only [sy,sq_sqrt (Nat.cast_nonneg q)]
  exact ⟨q,hq,prime,lo,hi,id ▸ left,id ▸ right⟩

end PrimeFactors.DisplacedPrimePartners
