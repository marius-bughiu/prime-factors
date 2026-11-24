import PrimeFactors.ConditionalStride
import PrimeFactors.DyadicSeries
import PrimeFactors.ProductAdvice

namespace PrimeFactors

noncomputable def boundedSquareRoots (M a : ℕ) : Finset ℕ :=
  (Finset.range M).filter fun x => x^2 ≡ a [MOD M]

/-- Count the roots as integer representatives even though the group estimate
is naturally stated for units. -/
theorem boundedSquareRoots_odd (k a : ℕ) (odd : Odd a) :
    (boundedSquareRoots (2^k) a).card ≤ 4 := by
  classical
  let M := 2^k
  have isA : IsUnit (a : ZMod M) := (ZMod.isUnit_iff_coprime _ _).mpr
    ((Nat.coprime_two_left.mpr odd).symm.pow_right k)
  let f (x : ℕ) : (ZMod M)ˣ := if h : IsUnit (x : ZMod M) then h.unit else 1
  have val {x : ℕ} (hx : x ∈ boundedSquareRoots M a) :
      (f x : ZMod M)=(x : ZMod M) ∧ f x^2=isA.unit := by
    have square : (x : ZMod M)^2=(a : ZMod M) := by
      simpa only [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Finset.mem_filter.mp hx).2
    have ux : IsUnit (x : ZMod M) := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (square ▸ isA)
    have fx : (f x : ZMod M)=(x : ZMod M) := by simp [f,ux]
    exact ⟨fx, Units.ext (by simpa only [Units.val_pow_eq_pow_val, fx, IsUnit.unit_spec] using square)⟩
  apply le_trans _ (strideUnitRoots_two_pow_le_four k isA.unit)
  apply Finset.card_le_card_of_injOn f
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(val hx).2⟩
  · intro x hx y hy eq
    have eqval : (x : ZMod M)=(y : ZMod M) := (val hx).1.symm.trans ((congrArg Units.val eq).trans (val hy).1)
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp eqval).eq_of_lt_of_lt
      (Finset.mem_range.mp (Finset.mem_filter.mp hx).1) (Finset.mem_range.mp (Finset.mem_filter.mp hy).1)

/-- Dividing an even square by four has at most two choices of the lost high bit. -/
theorem boundedSquareRoots_four_mul {M : ℕ} (pos : 0 < M) (t : ℕ) :
    (boundedSquareRoots (4*M) (4*t)).card ≤ (boundedSquareRoots M t).card*2 := by
  let f (x : ℕ) := (x/2%M,x/2/M)
  rw [← show ((boundedSquareRoots M t) ×ˢ Finset.range 2).card = (boundedSquareRoots M t).card*2 by simp]
  have data {x : ℕ} (hx : x ∈ boundedSquareRoots (4*M) (4*t)) :
      2*(x/2)=x ∧ (x/2)^2 ≡ t [MOD M] ∧ x/2/M<2 := by
    obtain ⟨range,root⟩ := Finset.mem_filter.mp hx
    have bound := Finset.mem_range.mp range
    have parity := root.of_dvd (show 2 ∣ 4*M by exact ⟨2*M,by ring⟩)
    have evenSq : 2 ∣ x^2 := Nat.modEq_zero_iff_dvd.mp (parity.trans (show 2 ∣ 4*t from ⟨2*t,by ring⟩).modEq_zero_nat)
    have even := Nat.dvd_iff_mod_eq_zero.mp (Nat.prime_two.dvd_of_dvd_pow evenSq)
    have decomp : 2*(x/2)=x := by omega
    have cancel : 4*(x/2)^2 ≡ 4*t [MOD 4*M] := by
      rw [show 4*(x/2)^2=(2*(x/2))^2 by ring, decomp]; exact root
    exact ⟨decomp, cancel.mul_left_cancel' (by decide : 4 ≠ 0),
      (Nat.div_lt_iff_lt_mul pos).mpr (by omega)⟩
  apply Finset.card_le_card_of_injOn f
  · intro x hx
    obtain ⟨_,root,bound⟩ := data hx
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ pos),
      ((Nat.mod_modEq _ _).pow 2).trans root⟩,Finset.mem_range.mpr bound⟩
  · intro x hx y hy eq
    have low : x/2%M=y/2%M := congrArg Prod.fst eq
    have hi : x/2/M=y/2/M := congrArg Prod.snd eq
    have half : x/2=y/2 := by rw [← Nat.mod_add_div (x/2) M, low, hi, Nat.mod_add_div]
    exact (data hx).1.symm.trans ((congrArg (2*·) half).trans (data hy).1)

/-- Weighted powers of four dividing the target, through level K. -/
noncomputable def rootLevels (a K : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (K+1), if 4^j ∣ a then 2^j else 0

private theorem rootLevels_pos (a K : ℕ) : 1 ≤ rootLevels a K := by
  rw [rootLevels, Finset.sum_range_succ']; simp

private theorem rootLevels_four (a K : ℕ) : rootLevels (4*a) (K+1)=1+2*rootLevels a K := by
  rw [rootLevels, Finset.sum_range_succ', rootLevels, Finset.mul_sum]
  simp only [pow_zero, one_dvd, if_true, add_comm 1]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [pow_succ', Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)]
  split_ifs <;> simp

private theorem four_dvd_of_even_square_root {x a M : ℕ} (evenA : 2 ∣ a)
    (root : x^2 ≡ a [MOD 4*M]) : 4 ∣ a := by
  have mod2 := root.of_dvd (show 2 ∣ 4*M from ⟨2*M,by ring⟩)
  obtain ⟨y,rfl⟩ := Nat.prime_two.dvd_of_dvd_pow
    (Nat.modEq_zero_iff_dvd.mp (mod2.trans evenA.modEq_zero_nat))
  have divides : 4 ∣ (2*y)^2 := ⟨y^2,by ring⟩
  exact Nat.modEq_zero_iff_dvd.mp ((root.of_dvd (dvd_mul_right 4 M)).symm.trans divides.modEq_zero_nat)

/-- A target divisible by a large square can have many roots, but the loss is
controlled by the powers of four dividing the target. -/
theorem boundedSquareRoots_levels (k a : ℕ) :
    (boundedSquareRoots (2^k) a).card ≤ 4*rootLevels a (k/2) := by
  induction k using Nat.twoStepInduction generalizing a with
  | zero =>
    have h := Finset.card_le_card (Finset.filter_subset (fun x : ℕ => x^2 ≡ a [MOD 1]) (Finset.range 1))
    simp only [Finset.card_range] at h
    have := rootLevels_pos a 0
    change (boundedSquareRoots 1 a).card ≤ 4*rootLevels a 0
    change (boundedSquareRoots 1 a).card ≤ 1 at h
    omega
  | one =>
    have h := Finset.card_le_card (Finset.filter_subset (fun x : ℕ => x^2 ≡ a [MOD 2]) (Finset.range 2))
    simp only [Finset.card_range] at h
    have := rootLevels_pos a 0
    change (boundedSquareRoots 2 a).card ≤ 4*rootLevels a 0
    change (boundedSquareRoots 2 a).card ≤ 2 at h
    omega
  | more k ih _ =>
    have kp : 2^(k+2)=4*2^k := by rw [pow_add]; ring
    have half : (k+2)/2=k/2+1 := by omega
    rw [half]
    by_cases div : 4 ∣ a
    · obtain ⟨t,rfl⟩ := div
      rw [kp, rootLevels_four]
      have red := boundedSquareRoots_four_mul (M := 2^k) (by positivity) t
      have := ih t
      omega
    · by_cases odd : Odd a
      · have h := boundedSquareRoots_odd (k+2) a odd
        have := rootLevels_pos a (k/2+1)
        omega
      · have even := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp odd)
        have empty : boundedSquareRoots (2^(k+2)) a = ∅ := by
          apply Finset.eq_empty_iff_forall_not_mem.mpr
          intro x hx
          exact div (four_dvd_of_even_square_root even (kp ▸ (Finset.mem_filter.mp hx).2))
        simp [empty]

/-- An odd product suffix confines cofactors with a singular target at this
level to at most four residue classes, including when the stride is even. -/
theorem singular_cofactors_card (C a m j : ℕ) (odd : Odd a) :
    ((Finset.Icc 1 C).filter fun c => 4^(j+1) ∣ a+(m*c)^2).card ≤
      4*(C/4^(j+1)+1) := by
  let M := 4^(j+1)
  have mp : 0 < M := by dsimp [M]; positivity
  let s := (Finset.Icc 1 C).filter fun c => M ∣ a+(m*c)^2
  change s.card ≤ 4*(C/M+1)
  rcases s.eq_empty_or_nonempty with empty | ⟨x,hx⟩
  · simp [empty]
  have divides := (Finset.mem_filter.mp hx).2
  have modEven : 2 ∣ M := by
    dsimp [M]; rw [pow_succ]; exact dvd_mul_of_dvd_right (by decide : 2 ∣ 4) _
  have evenSum := even_iff_two_dvd.mpr (modEven.trans divides)
  have oddSq : Odd ((m*x)^2) := Nat.not_even_iff_odd.mp fun he =>
    (Nat.not_even_iff_odd.mpr (odd.add_even he)) evenSum
  have oddProd : Odd (m*x) := (Nat.odd_mul.mp (show Odd ((m*x)*(m*x)) by simpa [pow_two] using oddSq)).1
  have oddM : Odd m := (Nat.odd_mul.mp oddProd).1
  have rep : M=2^(2*(j+1)) := by simp [M,pow_mul]
  have cop : M.Coprime m := rep ▸ (Nat.coprime_two_left.mpr oddM).pow_left _
  let roots := boundedSquareRoots M ((m*x)^2)
  have rootSize : roots.card ≤ 4 := by
    dsimp [roots]; rw [rep]; exact boundedSquareRoots_odd _ _ oddSq
  let key (c : ℕ) := ((m*c)%M,c/M)
  apply le_trans _ (Nat.mul_le_mul_right (C/M+1) rootSize)
  rw [← show (roots ×ˢ Finset.range (C/M+1)).card=roots.card*(C/M+1) by simp]
  apply Finset.card_le_card_of_injOn key
  · intro c hc
    obtain ⟨interval,dvd'⟩ := Finset.mem_filter.mp hc
    have root := Nat.ModEq.add_left_cancel' a (dvd'.modEq_zero_nat.trans divides.modEq_zero_nat.symm)
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ mp),
      ((Nat.mod_modEq (m*c) M).pow 2).trans root⟩,
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_Icc.mp interval).2))⟩
  · intro c _ b _ eq
    have same : m*c ≡ m*b [MOD M] := congrArg Prod.fst eq
    have low := Nat.ModEq.cancel_left_of_coprime cop same
    have hi : c/M=b/M := congrArg Prod.snd eq
    rw [← Nat.mod_add_div c M, show c%M=b%M from low, hi, Nat.mod_add_div]

/-- Average over consecutive positive cofactors, with an explicit endpoint
allowance for the singular squares in the observed low bits. -/
theorem advice_root_mass (k a m C : ℕ) (odd : Odd a) :
    (∑ c ∈ Finset.Icc 1 C, (adviceRootClasses (2^k) a m c).card) ≤ 20*C+32*2^(k/2) := by
  let target (c : ℕ) := a+(m*c)^2
  have levels (j : ℕ) (pos : 1 ≤ j) (_ : j ≤ k/2) :
      ((Finset.Icc 1 C).filter fun c => 4^j ∣ target c).card ≤ 4*(C/4^j+1) := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact singular_cofactors_card C a m i odd
  have count : (Finset.Icc 1 C).card ≤ C := by simp
  have total := dyadic_level_sum_bound (Finset.Icc 1 C) target C (k/2) count levels
  have per (c : ℕ) (_ : c ∈ Finset.Icc 1 C) :
      (adviceRootClasses (2^k) a m c).card ≤ 4*rootLevels (target c) (k/2) :=
    boundedSquareRoots_levels k (target c)
  have bound := Finset.sum_le_sum per
  rw [← Finset.mul_sum] at bound
  change (∑ c ∈ Finset.Icc 1 C, rootLevels (target c) (k/2)) ≤ _ at total
  omega

/-- Explicit joint count in one observed product cell, for any dyadic suffix
represented by an odd integer and any stride. -/
theorem advice_dyadic_cell_card {s : Finset (ℕ × ℕ)} {X L k W m a C : ℕ}
    (hw : 0 < W) (odd : Odd a)
    (inside : ∀ t ∈ s, t.1 ∈ Finset.Icc 1 C ∧ X ≤ t.2 ∧
      L ≤ t.2*(t.2+2*(m*t.1)) ∧ t.2*(t.2+2*(m*t.1)) < L+2*X*(2^k*W) ∧
      t.2*(t.2+2*(m*t.1)) ≡ a [MOD 2^k]) :
    s.card ≤ (20*C+32*2^(k/2))*W := by
  have bound := advice_cell_card (by positivity : 0 < 2^k) hw inside
  rw [← Finset.sum_mul] at bound
  exact bound.trans (Nat.mul_le_mul_right W (advice_root_mass k a m C odd))

end PrimeFactors
