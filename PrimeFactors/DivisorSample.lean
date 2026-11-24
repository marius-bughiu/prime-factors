import PrimeFactors.FourierAccess

namespace PrimeFactors

/-- Fourier transformation of a weighted square-root fibre converts it into
a complete quadratic exponential sum. The scaling c can be any unit. -/
theorem divisorSample_fiber_transform {n : ℕ} [NeZero n]
    (ψ : AddChar (ZMod n) ℂ) (c : (ZMod n)ˣ) (y : ZMod n) :
    (∑ a : ZMod n, ψ (-a*y) * ∑ v : ZMod n,
      if v^2=(c:ZMod n)*a then ψ v else 0) =
    ∑ v : ZMod n, ψ (v - ((↑(c⁻¹) : ZMod n)*v^2)*y) := by
  classical
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  have fibre (a : ZMod n) : v^2=(c:ZMod n)*a ↔ a=(↑(c⁻¹) : ZMod n)*v^2 := by
    constructor
    · intro h
      rw [h, ← mul_assoc, Units.inv_mul, one_mul]
    · rintro rfl
      rw [← mul_assoc, Units.mul_inv, one_mul]
  simp_rw [fibre]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- A nontrivial square root of one with prescribed CRT signs. -/
noncomputable def divisorSampleMixed {p q : ℕ} (cp : p.Coprime q) : ZMod (p*q) :=
  (ZMod.chineseRemainder cp).symm (1,-1)

/-- The four roots of one on a two-prime product, with their exact weights. -/
theorem divisorSample_four_roots {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (cp : p.Coprime q)
    (pOdd : p≠2) (qOdd : q≠2) [NeZero (p*q)] {A : Type*} [AddCommMonoid A]
    (f : ZMod (p*q) → A) :
    (∑ w : ZMod (p*q), if w^2=1 then f w else 0) =
      f 1 + f (-1) + f (divisorSampleMixed cp) + f (-divisorSampleMixed cp) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  let e := ZMod.chineseRemainder cp
  have pSign : (-1 : ZMod p) ≠ 1 :=
    Ring.neg_one_ne_one_of_char_ne_two (by simpa only [ZMod.ringChar_zmod_n] using pOdd)
  have qSign : (-1 : ZMod q) ≠ 1 :=
    Ring.neg_one_ne_one_of_char_ne_two (by simpa only [ZMod.ringChar_zmod_n] using qOdd)
  let blocks (x : ZMod p × ZMod q) :=
    if (x.1=1 ∨ x.1= -1) ∧ (x.2=1 ∨ x.2= -1) then f (e.symm x) else 0
  have term (w : ZMod (p*q)) :
      (if w^2=1 then f w else 0) = blocks (e w) := by
    have iff : w^2=1 ↔ ((e w).1=1 ∨ (e w).1= -1) ∧ ((e w).2=1 ∨ (e w).2= -1) := by
      rw [← e.injective.eq_iff, map_pow, map_one, Prod.ext_iff]
      change ((e w).1^2=1 ∧ (e w).2^2=1) ↔ _
      simp only [sq_eq_one_iff]
    simp only [blocks, iff, e.symm_apply_apply]
  rw [Fintype.sum_equiv e.toEquiv _ blocks term, Fintype.sum_prod_type]
  have pairSum {F : Type} [Field F] [Fintype F] [DecidableEq F] (h : (-1:F)≠1) (g : F→A) :
      (∑ x : F, if x=1 ∨ x= -1 then g x else 0) = g 1+g (-1) := by
    have memb (x : F) : (x=1 ∨ x= -1) ↔ x∈({1,-1}:Finset F) := by simp
    simp_rw [memb]
    rw [← Finset.sum_filter]
    rw [show Finset.univ.filter (fun x : F => x ∈ ({1,-1}:Finset F)) = {1,-1} by ext; simp]
    simp [Ne.symm h]
  change (∑ x : ZMod p, ∑ y : ZMod q, if (x=1 ∨ x= -1) ∧ (y=1 ∨ y= -1)
    then f (e.symm (x,y)) else 0) = _
  have inner (x : ZMod p) : (∑ y : ZMod q, if (x=1 ∨ x= -1) ∧ (y=1 ∨ y= -1)
      then f (e.symm (x,y)) else 0) =
      if x=1 ∨ x= -1 then f (e.symm (x,1)) + f (e.symm (x,-1)) else 0 := by
    by_cases hx : x=1 ∨ x= -1
    · simp only [hx, true_and, if_true]
      exact pairSum (F:=ZMod q) qSign _
    · simp [hx]
  simp_rw [inner]
  rw [pairSum (F:=ZMod p) pSign]
  have a : e.symm (1,1) = (1 : ZMod (p*q)) := e.symm.map_one
  have b : e.symm (-1,-1) = (-1 : ZMod (p*q)) := by rw [← a, ← map_neg]; rfl
  have d : e.symm (-1,1) = -divisorSampleMixed cp := by
    change e.symm (-1,1) = -e.symm (1,-1)
    rw [← map_neg]
    simp
  rw [a,b,d]
  change (f 1 + f (divisorSampleMixed cp)) + (f (-divisorSampleMixed cp) + f (-1)) = _
  simp only [add_assoc]
  congr 1
  rw [← add_assoc, add_comm _ (f (-1))]

/-- The mixed CRT root selects a definite factor by ordinary gcd. -/
theorem divisorSample_mixed_gcd {p q : ℕ} (hp : p.Prime) (cp : p.Coprime q)
    (pOdd : p≠2) [NeZero (p*q)] :
    Nat.gcd (p*q) ((divisorSampleMixed cp).val+1) = q := by
  letI : Fact p.Prime := ⟨hp⟩
  let e := ZMod.chineseRemainder cp
  let h := divisorSampleMixed cp
  have v : e (h.val : ZMod (p*q)) = (1,-1) := by
    rw [ZMod.natCast_zmod_val]
    exact e.apply_symm_apply _
  have P : (h.val : ZMod p)=1 := by simpa only [map_natCast, Prod.fst_natCast] using congrArg Prod.fst v
  have Q : (h.val : ZMod q)= -1 := by simpa only [map_natCast, Prod.snd_natCast] using congrArg Prod.snd v
  apply Nat.gcd_mul_of_coprime_of_dvd
  · apply hp.coprime_iff_not_dvd.mpr
    intro divides
    have z := (ZMod.natCast_zmod_eq_zero_iff_dvd (h.val+1) p).mpr divides
    rw [Nat.cast_add, Nat.cast_one, P] at z
    have bad : (2:ZMod p)=0 := by simpa only [one_add_one_eq_two] using z
    have hd : p ∣ 2 := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).mp bad
    exact pOdd (le_antisymm (Nat.le_of_dvd (by decide) hd) hp.two_le)
  · apply (ZMod.natCast_zmod_eq_zero_iff_dvd (h.val+1) q).mp
    simp [Nat.cast_add, Q]

/-- A second cosine sample with a calibrated shift supplies the missing sine
component, up to the one global choice of sign for the hidden root. -/
theorem divisorSample_cross_phase (x y : ℝ) :
    Real.sin x * Real.sin y = Real.cos x * Real.cos y - Real.cos (x+y) := by
  rw [Real.cos_add]
  ring

/-- Consecutive binary digits differ exactly in the two middle quarters.
For a phase x/N, substitute x = 2^(j+1) h to decode a dyadic cosine sign. -/
theorem divisorSample_adjacent_digits (x N : ℕ) :
    ((x/N)%2 ≠ (2*x/N)%2) ↔ (2*x/N)%4=1 ∨ (2*x/N)%4=2 := by
  have half : (2*x/N)/2 = x/N := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm N 2, Nat.mul_div_mul_left _ _ (by decide)]
  rw [← half]
  omega

/-- Below a square-root cutoff, a distinct nonnegative lift of a square
must gain at least one whole modulus. This applies at the quarter boundaries. -/
theorem divisorSample_square_separation {r a N : ℕ} (small : a^2 < N)
    (different : r ≠ a) (congruence : r^2 ≡ a^2 [MOD N]) : N+a^2 ≤ r^2 := by
  have rem : r^2%N = a^2 := by
    change r^2%N = a^2%N at congruence
    rwa [Nat.mod_eq_of_lt small] at congruence
  have large : N ≤ r^2 := by
    apply Nat.le_of_not_gt
    intro lt
    rw [Nat.mod_eq_of_lt lt] at rem
    exact different ((Nat.pow_left_inj (by decide : 2 ≠ 0)).mp rem)
  have pos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) small
  have div : 1 ≤ r^2/N := (Nat.le_div_iff_mul_le pos).mpr (by simpa)
  have product := Nat.mul_le_mul_left N div
  rw [Nat.mul_one] at product
  have split := Nat.mod_add_div (r^2) N
  rw [rem] at split
  omega


private theorem divisorSample_real_center {ι : Type*} [Fintype ι] (f : ι→ℝ) (a b : ℝ) :
    (∑ i, (a*f i-b)^2) = a^2 * (∑ i, (f i)^2) - 2*a*b*(∑ i, f i) +
        Fintype.card ι * b^2 := by
  simp_rw [show ∀ x : ℝ, (a*x-b)^2 = a^2*x^2-2*a*b*x+b^2 by intro x; ring]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Exact one-sample squared error before division by the normalization.
This applies to the public Jacobi-weighted terms, whose squared norms are
the unit indicators. -/
theorem divisorSample_squared_error {ι : Type*} [Fintype ι] (f : ι→ℂ) :
    let n : ℝ := Fintype.card ι
    let S := ∑ i, f i
    (∑ i, Complex.normSq ((n:ℂ)*f i-S)) =
      n^2 * (∑ i, Complex.normSq (f i)) - n*Complex.normSq S := by
  dsimp only
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
    Complex.re_sum, Complex.im_sum, Finset.sum_add_distrib, ← sq]
  rw [divisorSample_real_center, divisorSample_real_center]
  ring

example : (137 : ZMod 391)^2 = 1 ∧ (137 : ZMod 391) ≠ 1 ∧ (137 : ZMod 391) ≠ -1 ∧
    Nat.gcd 391 (137+1) = 23 := by decide +kernel

/-- The root returned by the bounded, rounded Salié calculation. -/
theorem divisorSample_667 : (436 : ZMod 667)^2 = 1 ∧ Nat.gcd 435 667 = 29 ∧
    Nat.gcd 437 667 = 23 ∧ Nat.Prime 23 ∧ Nat.Prime 29 ∧ 23*29=667 := by decide +kernel

end PrimeFactors
