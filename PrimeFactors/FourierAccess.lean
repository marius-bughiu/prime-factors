import PrimeFactors.DivisorSignal

namespace PrimeFactors

open scoped BigOperators

private theorem punctured_character_sum {r : ℕ} [Fact r.Prime]
    (ψ : AddChar (ZMod r) ℂ) (inj : Function.Injective ψ) (k : ZMod r) :
    (∑ x : ZMod r, if x = 0 then 0 else ψ (-(x*k))) =
      (if k = 0 then (r : ℂ) else 0) - 1 := by
  classical
  have whole : (∑ x : ZMod r, ψ (-(x*k))) = if k = 0 then (r : ℂ) else 0 := by
    split_ifs with zero
    · simp [zero, AddChar.map_zero_eq_one]
    · have nontrivial : ψ.mulShift (-k) ≠ 1 := by
        intro h
        have eq := congrArg (fun χ : AddChar (ZMod r) ℂ => χ 1) h
        have atZero := ψ.map_zero_eq_one
        simp only [AddChar.mulShift_apply, mul_one, AddChar.one_apply] at eq
        exact zero (neg_eq_zero.mp (inj (eq.trans atZero.symm)))
      simpa only [AddChar.mulShift_apply, neg_mul, mul_comm k] using
        AddChar.sum_eq_zero_of_ne_one nontrivial
  rw [← whole]
  calc
    _ = ∑ x : ZMod r, (ψ (-(x*k)) - if x = 0 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : x = 0 <;> simp [h, AddChar.map_zero_eq_one]
    _ = _ := by rw [Finset.sum_sub_distrib]; simp

/-- Exact transform of the principal coefficients, with mathlib's sign and
normalization conventions. The two exceptional sets of nonzero frequencies
are the multiples of the unknown primes. -/
theorem principal_dft_at_nat {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (different : p ≠ q)
    [NeZero (p*q)] (k : ℕ) :
    ZMod.dft (fun j => (1 : DirichletCharacter ℂ (p*q)) j) (k : ZMod (p*q)) =
      ((if p ∣ k then (p:ℂ) else 0) - 1) * ((if q ∣ k then (q:ℂ) else 0) - 1) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  let e := ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr different)
  let ψ : AddChar (ZMod (p*q)) ℂ := ZMod.stdAddChar
  let ψp := ψ.compAddMonoidHom (e.symm.toAddMonoidHom.comp (AddMonoidHom.inl (ZMod p) (ZMod q)))
  let ψq := ψ.compAddMonoidHom (e.symm.toAddMonoidHom.comp (AddMonoidHom.inr (ZMod p) (ZMod q)))
  have pinj : Function.Injective ψp := by
    intro x y eq
    change ψ (e.symm (x,0)) = ψ (e.symm (y,0)) at eq
    exact congrArg Prod.fst (e.symm.injective (ZMod.injective_stdAddChar eq))
  have qinj : Function.Injective ψq := by
    intro x y eq
    change ψ (e.symm (0,x)) = ψ (e.symm (0,y)) at eq
    exact congrArg Prod.snd (e.symm.injective (ZMod.injective_stdAddChar eq))
  have splitChar (x : ZMod p) (y : ZMod q) :
      ψ (e.symm (x,y)) = ψp x * ψq y := by
    change _ = ψ (e.symm (x,0)) * ψ (e.symm (0,y))
    rw [← AddChar.map_add_eq_mul, ← map_add]
    show ψ (e.symm (x,y)) = ψ (e.symm ((x+0), (0+y)))
    simp
  let fp := fun x : ZMod p => if x = 0 then (0:ℂ) else ψp (-(x*k))
  let fq := fun y : ZMod q => if y = 0 then (0:ℂ) else ψq (-(y*k))
  have term (j : ZMod (p*q)) :
      ψ (-(j*k)) * (1 : DirichletCharacter ℂ (p*q)) j = fp (e j).1 * fq (e j).2 := by
    have units : IsUnit j ↔ (e j).1 ≠ 0 ∧ (e j).2 ≠ 0 := by
      rw [← isUnit_map_iff e, Prod.isUnit_iff, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
    have charEq : ψ (-(j*k)) = ψp (-((e j).1*k)) * ψq (-((e j).2*k)) := by
      rw [← splitChar]
      apply congrArg ψ
      apply e.injective
      simp
      ext <;> rfl
    by_cases xzero : (e j).1 = 0
    · have h : ¬IsUnit j := fun u => (units.mp u).1 xzero
      simp [fp, xzero, MulChar.map_nonunit _ h]
    by_cases yzero : (e j).2 = 0
    · have h : ¬IsUnit j := fun u => (units.mp u).2 yzero
      simp [fq, yzero, MulChar.map_nonunit _ h]
    simp [fp,fq,xzero,yzero,charEq,MulChar.one_apply (units.mpr ⟨xzero,yzero⟩)]
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  change (∑ j, ψ (-(j*k)) * (1 : DirichletCharacter ℂ (p*q)) j) = _
  rw [Fintype.sum_equiv e.toEquiv _ (fun j => fp j.1 * fq j.2) term, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  change (∑ j, if j = 0 then 0 else ψp (-(j*k))) *
    (∑ j, if j = 0 then 0 else ψq (-(j*k))) = _
  rw [punctured_character_sum ψp pinj, punctured_character_sum ψq qinj]
  simp only [ZMod.natCast_zmod_eq_zero_iff_dvd]

/-- A Fourier series with explicitly specified natural frequency indices. -/
noncomputable def maskSeries (n : ℕ) [NeZero n] (indices : Finset ℕ) (weight : ℕ → ℂ)
    (j : ZMod n) : ℂ :=
  ∑ k ∈ indices, weight k * ZMod.stdAddChar ((k : ZMod n) * j)

/-- If the series contains no frequency divisible by q alone, then even the
best choice of weights incurs uniform error at least (q−1)/(2q). -/
theorem maskSeries_missing_axis {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (different : p ≠ q)
    [NeZero (p*q)] (indices : Finset ℕ) (weight : ℕ → ℂ) {ε : ℝ}
    (missing : ∀ k ∈ indices, q ∣ k → p ∣ k)
    (error : ∀ j, ‖maskSeries (p*q) indices weight j -
      (1 : DirichletCharacter ℂ (p*q)) j‖ ≤ ε) :
    (q : ℝ) - 1 ≤ 2*q*ε := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  let e := ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr different)
  let ψ : AddChar (ZMod (p*q)) ℂ := ZMod.stdAddChar
  let F := maskSeries (p*q) indices weight
  let χ := (1 : DirichletCharacter ℂ (p*q))
  have fiber (x : ZMod p) (k : ℕ) (hk : k ∈ indices) :
      (∑ y : ZMod q, ψ ((k : ZMod (p*q))* e.symm (x,y))) =
      (∑ y : ZMod q, ψ ((k : ZMod (p*q))* e.symm (0,y))) := by
    by_cases qdiv : q ∣ k
    · have nk : (k : ZMod (p*q)) = 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr
        (((Nat.coprime_primes hp hq).mpr different).mul_dvd_of_dvd_of_dvd (missing k hk qdiv) qdiv)
      simp [nk]
    let ξ := (ψ.mulShift (k : ZMod (p*q))).compAddMonoidHom
      (e.symm.toAddMonoidHom.comp (AddMonoidHom.inr (ZMod p) (ZMod q)))
    have nontrivial : ξ ≠ 1 := by
      intro trivial
      have atOne := congrArg (fun φ : AddChar (ZMod q) ℂ => φ 1) trivial
      change ψ ((k : ZMod (p*q)) * e.symm (0,1)) = 1 at atOne
      have zero := ZMod.injective_stdAddChar (atOne.trans ψ.map_zero_eq_one.symm)
      have axis := congrArg (fun j => (e j).2) zero
      simp only [map_mul,map_natCast,e.apply_symm_apply,Prod.snd_mul, Prod.snd_natCast,
        mul_one,map_zero,Prod.snd_zero] at axis
      exact qdiv ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp axis)
    have vanish : (∑ y : ZMod q, ψ ((k : ZMod (p*q))*e.symm (0,y))) = 0 :=
      AddChar.sum_eq_zero_of_ne_one nontrivial
    have factored (y : ZMod q) : ψ ((k : ZMod (p*q))*e.symm (x,y)) =
        ψ ((k : ZMod (p*q))*e.symm (x,0)) * ψ ((k : ZMod (p*q))*e.symm (0,y)) := by
      rw [← AddChar.map_add_eq_mul, ← mul_add, ← map_add]
      simp
    rw [Finset.sum_congr rfl (fun y _ => factored y), ← Finset.mul_sum, vanish, mul_zero]
  have invariant (x : ZMod p) : (∑ y : ZMod q, F (e.symm (x,y))) =
      ∑ y : ZMod q, F (e.symm (0,y)) := by
    dsimp only [F,maskSeries]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := indices)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    exact congrArg (weight k * ·) (fiber x k hk)
  have units (x : ZMod p) (y : ZMod q) : IsUnit (e.symm (x,y)) ↔ x ≠ 0 ∧ y ≠ 0 := by
    rw [← isUnit_map_iff e, e.apply_symm_apply, Prod.isUnit_iff, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
  have zeroMask (y : ZMod q) : χ (e.symm (0,y)) = 0 :=
    MulChar.map_nonunit _ (fun h => ((units 0 y).mp h).1 rfl)
  have oneMask (y : ZMod q) : χ (e.symm (1,y)) = if y = 0 then 0 else 1 := by
    by_cases hy : y = 0
    · simp [hy, MulChar.map_nonunit χ (fun h => ((units 1 0).mp h).2 rfl)]
    · simp [hy, MulChar.one_apply ((units 1 y).mpr ⟨one_ne_zero, hy⟩), χ]
  have trueDiff : (∑ y : ZMod q, χ (e.symm (1,y))) -
      (∑ y : ZMod q, χ (e.symm (0,y))) = (q : ℂ) - 1 := by
    simp only [zeroMask, Finset.sum_const_zero, sub_zero, oneMask]
    calc
      _ = ∑ y : ZMod q, ((1:ℂ) - (if y = 0 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases h : y = 0 <;> simp [h]
      _ = _ := by simp [Finset.sum_sub_distrib]
  have approx (x : ZMod p) :
      ‖(∑ y : ZMod q, F (e.symm (x,y))) - (∑ y : ZMod q, χ (e.symm (x,y)))‖ ≤ q*ε := by
    rw [← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun y _ => error (e.symm (x,y)))).trans_eq
      (by simp))
  have first := approx 1
  have second := approx 0
  rw [invariant 1, norm_sub_rev] at first
  have total := dist_triangle (∑ y : ZMod q, χ (e.symm (1,y))) (∑ y : ZMod q, F (e.symm (0,y)))
    (∑ y : ZMod q, χ (e.symm (0,y)))
  simp only [dist_eq_norm] at total
  rw [trueDiff, ← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hq.one_lt.le) : 0 ≤ (q : ℝ)-1)] at total
  linarith

/-- An oscillatory weight with explicit frequencies coprime to the input has
a fully determined sum against the principal coefficients: each nonconstant
mode contributes its weight, and the constant mode is weighted by the totient.
This also covers every strictly positive band below the smaller prime. -/
theorem principal_weighted_modes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (different : p ≠ q)
    [NeZero (p*q)] (indices : Finset ℕ) (weight : ℕ → ℂ)
    (clean : ∀ k ∈ indices, k ≠ 0 → k.Coprime (p*q)) :
    (∑ j : ZMod (p*q), (1 : DirichletCharacter ℂ (p*q)) j *
      maskSeries (p*q) indices weight (-j)) =
    ∑ k ∈ indices, weight k * (if k = 0 then ((p:ℂ)-1)*((q:ℂ)-1) else 1) := by
  classical
  unfold maskSeries
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have h (j : ZMod (p*q)) : (1 : DirichletCharacter ℂ (p*q)) j *
      (weight k * ZMod.stdAddChar ((k : ZMod (p*q)) * -j)) =
      weight k * (ZMod.stdAddChar (-(j*(k : ZMod (p*q)))) * (1 : DirichletCharacter ℂ (p*q)) j) := by
    rw [mul_neg, mul_comm (k : ZMod (p*q)) j]
    ring
  simp_rw [h]
  rw [← Finset.mul_sum]
  congr 1
  change ZMod.dft (fun j => (1 : DirichletCharacter ℂ (p*q)) j) (k : ZMod (p*q)) = _
  rw [principal_dft_at_nat hp hq different]
  by_cases kz : k = 0
  · simp [kz]
  · obtain ⟨pco,qco⟩ := Nat.coprime_mul_iff_right.mp (clean k hk kz)
    simp [kz, hp.coprime_iff_not_dvd.mp pco.symm, hq.coprime_iff_not_dvd.mp qco.symm]

/-- Uniform error below one quarter forces an explicitly listed frequency
whose gcd with the modulus is a proper factor. -/
theorem maskSeries_factor_frequency {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (different : p ≠ q)
    [NeZero (p*q)] (indices : Finset ℕ) (weight : ℕ → ℂ) {ε : ℝ} (small : ε < 1/4)
    (error : ∀ j, ‖maskSeries (p*q) indices weight j -
      (1 : DirichletCharacter ℂ (p*q)) j‖ ≤ ε) :
    ∃ k ∈ indices, q ∣ k ∧ ¬ p ∣ k := by
  by_contra! none
  have obstruction := maskSeries_missing_axis hp hq different indices weight none error
  have two : (2:ℝ) ≤ q := by exact_mod_cast hq.two_le
  nlinarith [mul_lt_mul_of_pos_left small (show (0:ℝ)<q by linarith)]

end PrimeFactors
