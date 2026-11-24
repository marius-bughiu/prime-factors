import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace PrimeFactors

open scoped ComplexConjugate

/-- Squared modulus of a weighted finite additive-character sum. -/
noncomputable def bandMass (Q : ℕ) [NeZero Q] (modes : Finset ℕ) (weight : ℕ → ℂ)
    (x : ZMod Q) : ℝ :=
  Complex.normSq (∑ i ∈ modes, weight i * ZMod.stdAddChar ((i : ZMod Q)*x))

private theorem conjugate_mode {Q : ℕ} [NeZero Q] (x : ZMod Q) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv]

private theorem restricted_mode (m n : ℕ) [NeZero m] [NeZero n] (d : ℤ) :
    ZMod.stdAddChar ((m : ZMod (m*n)) * (d : ZMod (m*n))) = ZMod.stdAddChar (d : ZMod n) := by
  rw [← Int.cast_natCast m, ← Int.cast_mul, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp [show (m:ℂ) ≠ 0 by exact_mod_cast NeZero.ne m,
    show (n:ℂ) ≠ 0 by exact_mod_cast NeZero.ne n]
  ring

private theorem fiber_mode_sum {m n : ℕ} [NeZero m] [NeZero n] (a : ZMod (m*n)) (d : ℤ) :
    (∑ y : ZMod n, ZMod.stdAddChar ((d : ZMod (m*n))*(a+(m : ZMod (m*n))*(y.val : ZMod (m*n))))) =
      ZMod.stdAddChar ((d : ZMod (m*n))*a) * (if (d : ZMod n) = 0 then (n:ℂ) else 0) := by
  classical
  simp only [mul_add, AddChar.map_add_eq_mul, ← Finset.mul_sum]
  congr 1
  have term (y : ZMod n) :
      ZMod.stdAddChar ((d : ZMod (m*n))*((m : ZMod (m*n))*(y.val : ZMod (m*n)))) =
        ZMod.stdAddChar (y*(d : ZMod n)) := by
    have prod : (d : ZMod (m*n))*((m : ZMod (m*n))*(y.val : ZMod (m*n))) =
        (m : ZMod (m*n))*((((y.val : ℤ)*d : ℤ) : ZMod (m*n))) := by push_cast; ring
    rw [prod, restricted_mode]
    simp
  simp_rw [term]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n), ZMod.card]
  split_ifs <;> simp

/-- If the frequencies are distinct modulo the fiber size n, the marginal
squared mass is exactly uniform on all residue classes modulo m. The offset a
may be any representative in Z/(mn), including a translated center. -/
theorem bandMass_fiber {m n : ℕ} [NeZero m] [NeZero n]
    (modes : Finset ℕ) (weight : ℕ → ℂ) (a : ZMod (m*n))
    (separate : ∀ i ∈ modes, ∀ j ∈ modes, (i : ZMod n) = (j : ZMod n) → i = j) :
    (∑ y : ZMod n, bandMass (m*n) modes weight (a+(m : ZMod (m*n))*(y.val : ZMod (m*n)))) =
      n * ∑ i ∈ modes, Complex.normSq (weight i) := by
  classical
  let D := fun i j : ℕ => (i:ℤ) - j
  let wave := fun i j (x : ZMod (m*n)) => ZMod.stdAddChar ((D i j : ZMod (m*n))*x)
  have expand (x : ZMod (m*n)) :
      (bandMass (m*n) modes weight x : ℂ) =
        ∑ i ∈ modes, ∑ j ∈ modes, (weight i * conj (weight j)) * wave i j x := by
    unfold bandMass
    rw [← Complex.mul_conj, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul (starRingEnd ℂ), conjugate_mode]
    dsimp [wave,D]
    push_cast
    rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  have orth (i j : ℕ) (hi : i ∈ modes) (hj : j ∈ modes) :
      (∑ y : ZMod n, (weight i * conj (weight j)) * wave i j (a+(m : ZMod (m*n))*(y.val : ZMod (m*n)))) =
        if i=j then (n:ℂ)*Complex.normSq (weight i) else 0 := by
    rw [← Finset.mul_sum, show (∑ y : ZMod n, wave i j (a+(m : ZMod (m*n))*(y.val : ZMod (m*n)))) =
      _ from fiber_mode_sum a (D i j)]
    by_cases eq : i=j
    · subst j
      simp [D,Complex.mul_conj,AddChar.map_zero_eq_one,mul_comm]
    · have nonzero : ((D i j : ℤ) : ZMod n) ≠ 0 := by
        simp only [D,Int.cast_sub,Int.cast_natCast,sub_ne_zero]
        exact fun e => eq (separate i hi j hj e)
      simp [eq,nonzero]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum]
  simp_rw [expand]
  rw [Finset.sum_comm (s := Finset.univ) (t := modes)]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := modes)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_congr rfl (fun j hj => orth i j hi hj), Finset.sum_ite_eq, if_pos hi]

/-- The unnormalized Fejér mass has fiber total nH for all H ≤ n.
For positive H its normalization as a probability on Z/(mn) gives each
residue class modulo m mass 1/m. -/
theorem fejer_uniform_fiber {m n H : ℕ} [NeZero m] [NeZero n] (short : H ≤ n) (a : ZMod (m*n)) :
    (∑ y : ZMod n, bandMass (m*n) (Finset.range H) (fun _ => 1) (a+(m : ZMod (m*n))*(y.val : ZMod (m*n)))) =
      (n:ℝ)*H := by
  have separate (i : ℕ) (hi : i ∈ Finset.range H) (j : ℕ) (hj : j ∈ Finset.range H)
      (same : (i : ZMod n) = (j : ZMod n)) : i=j :=
    ((ZMod.natCast_eq_natCast_iff ..).mp same).eq_of_lt_of_lt
      ((Finset.mem_range.mp hi).trans_le short) ((Finset.mem_range.mp hj).trans_le short)
  simpa using bandMass_fiber (Finset.range H) (fun _ => 1) a separate

/-- A translated interval around the kernel center retains at least H²/4
unnormalized mass per point. The integer offset x may have either sign.
The condition is expressed without any division or rounding. -/
theorem fejer_near_center {Q H : ℕ} [NeZero Q] (x : ℤ)
    (near : 6*H*x.natAbs ≤ Q) :
    (H:ℝ)^2/4 ≤ bandMass Q (Finset.range H) (fun _ => 1) (x : ZMod Q) := by
  let wave := fun i : ℕ => ZMod.stdAddChar ((i : ZMod Q)*(x : ZMod Q))
  have Qpos : 0 < (Q:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have nearR : 6*(H:ℝ)*|(x:ℝ)| ≤ (Q:ℝ) := by
    have lifted : 6*(H:ℝ)*(x.natAbs:ℝ) ≤ (Q:ℝ) := by exact_mod_cast near
    simpa only [Nat.cast_ofNat, Int.cast_natAbs, Int.cast_abs] using lifted
  have half (i : ℕ) (hi : i ∈ Finset.range H) : 1/2 ≤ (wave i).re := by
    let phase := 2*Real.pi*(i:ℝ)*x/Q
    have value : wave i = Complex.exp ((phase : ℂ)*Complex.I) := by
      dsimp [wave,phase]
      rw [← Int.cast_natCast i, ← Int.cast_mul, ZMod.stdAddChar_coe]
      push_cast
      congr 1
      ring
    rw [value, Complex.exp_ofReal_mul_I_re, ← Real.cos_abs]
    have ile : (i:ℝ) ≤ H := by exact_mod_cast (Finset.mem_range.mp hi).le
    have phaseB : |phase| ≤ Real.pi/3 := by
      dsimp [phase]
      rw [abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi*(i:ℝ)), abs_of_pos Qpos,
        div_le_iff₀ Qpos]
      have product := mul_le_mul_of_nonneg_right ile (abs_nonneg (x:ℝ))
      have cap : 6*(i:ℝ)*|(x:ℝ)| ≤ Q := by linarith
      nlinarith only [mul_le_mul_of_nonneg_left cap Real.pi_pos.le]
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) phaseB
  have total := Finset.sum_le_sum half
  rw [← Complex.re_sum] at total
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at total
  change _ ≤ Complex.normSq (∑ i ∈ Finset.range H, 1*wave i)
  simp only [one_mul, Complex.normSq_apply]
  nlinarith only [mul_self_le_mul_self (by positivity : 0 ≤ (H:ℝ)*(1/2)) total,
    sq_nonneg (∑ i ∈ Finset.range H, wave i).im]

end PrimeFactors
