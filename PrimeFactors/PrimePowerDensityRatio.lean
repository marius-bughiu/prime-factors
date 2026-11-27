import PrimeFactors.PrimePowerEssentialDigits
import PrimeFactors.LocalSumMenu
import PrimeFactors.PrimePowerRatioProduct

/-! A uniform bound for the change in complete-period factor-sum density
between the second digit of an odd prime and any deeper precision. -/

namespace PrimeFactors.PrimePowerDensityRatio

open scoped Classical

/-- Fraction of the complete residue system allowed by the local predicate. -/
noncomputable def density (n m : ℕ) : ℚ := (LocalSumMenu.count n m : ℚ)/m

theorem density_nonneg (n m : ℕ) : 0 ≤ density n m :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The sum from the pair 1 and n supplies one admissible class. -/
theorem density_pos (n : ℕ) {m : ℕ} (hm : 0 < m) : 0 < density n m := by
  letI : NeZero m := ⟨hm.ne'⟩
  haveI : Nonempty {s : ZMod m // AdmissibleSum (n : ZMod m) s} :=
    ⟨⟨1+n,1,n,one_mul _,rfl⟩⟩
  exact div_pos (Nat.cast_pos.mpr Nat.card_pos) (Nat.cast_pos.mpr hm)

/-- Ratio of the square-unit density at the second digit to its lower bound
at arbitrary depth. The subtraction in the denominator is rational. -/
noncomputable abbrev ratio := PrimePowerRatioProduct.ratio

variable {p n : ℕ} [Fact p.Prime]

private theorem positive_polynomial (odd : p ≠ 2) : (0 : ℚ) < (p : ℚ)^2-2*p-1 := by
  have prime := (Fact.out : p.Prime)
  have large : (3 : ℚ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := prime.two_le; omega)
  nlinarith only [sq_nonneg ((p : ℚ)-3),large]

theorem one_le_ratio (odd : p ≠ 2) : 1 ≤ ratio p := by
  exact PrimePowerRatioProduct.ratio_ge_one p (by have := (Fact.out : p.Prime).two_le; omega)

private theorem count_at (odd : p ≠ 2) (unitN : ¬p ∣ n) (k : ℕ) :
    LocalSumMenu.count n (p^(k+1)) =
      primePowerSumCount p (decide (IsSquare (n : ZMod p))) (k+1) := by
  classical
  have nz : firstPrimeDigit p k (n : ZMod (p^(k+1))) ≠ 0 := by
    rw [map_natCast]
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd n p).mp.mt unitN
  simpa only [LocalSumMenu.count,map_natCast] using card_primePower_admissibleSum odd k _ nz

private theorem nonsquare_at (odd : p ≠ 2) (unitN : ¬p ∣ n) (ns : ¬IsSquare (n : ZMod p))
    (k : ℕ) : density n (p^(k+1)) = (((p-1)/2 : ℕ) : ℚ)/p := by
  have pp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [density,count_at odd unitN,decide_eq_false ns]
  simp only [primePowerSumCount,Bool.false_eq_true,if_false,Nat.cast_mul,Nat.cast_pow,pow_succ]
  field_simp
  ring

/-- At a nonsquare unit product all positive precisions have equal density. -/
theorem nonsquare_density (odd : p ≠ 2) (unitN : ¬p ∣ n) (ns : ¬IsSquare (n : ZMod p))
    {e : ℕ} (depth : 1 ≤ e) : density n (p^2) = density n (p^e) := by
  obtain ⟨k,rfl⟩ : ∃ k, e = k+1 := ⟨e-1,by omega⟩
  exact (nonsquare_at odd unitN ns 1).trans (nonsquare_at odd unitN ns k).symm

private noncomputable def floorDensity (p : ℕ) : ℚ :=
  let P : ℚ := p
  (P^2-2*P-1)/(2*P*(P+1))

private theorem square_floor (odd : p ≠ 2) (unitN : ¬p ∣ n) (sq : IsSquare (n : ZMod p))
    (k : ℕ) : floorDensity p ≤ density n (p^(k+1)) := by
  have pp : (0 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have closed := primePowerSumCount_closed_square (p := p) odd k
  have lower : p^2*p^k ≤ 2*(p+1)*primePowerSumCount p true (k+1)+(2*p+1)*p^k := by
    rw [closed]
    omega
  have rat : (p : ℚ)^2*(p : ℚ)^k ≤
      2*(p+1)*(primePowerSumCount p true (k+1) : ℚ)+(2*p+1)*(p : ℚ)^k := by
    exact_mod_cast lower
  have bound : ((p : ℚ)^2-2*p-1)*(p : ℚ)^k ≤ 2*(p+1)*(primePowerSumCount p true (k+1) : ℚ) := by
    linarith only [rat]
  rw [density,count_at odd unitN,decide_eq_true sq,Nat.cast_pow]
  dsimp only [floorDensity]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [pow_succ (p : ℚ) k]
  nlinarith only [mul_le_mul_of_nonneg_right bound pp.le]

private theorem square_second (odd : p ≠ 2) (unitN : ¬p ∣ n) (sq : IsSquare (n : ZMod p)) :
    density n (p^2) = ratio p * floorDensity p := by
  have pp : (0 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have poly := positive_polynomial odd
  have closed := primePowerSumCount_closed_square (p := p) odd 1
  simp only [pow_one,Nat.not_even_one,if_false] at closed
  have rat : 2*((p : ℚ)+1)*(primePowerSumCount p true 2 : ℚ)+(2*p+1)*p =
      (p : ℚ)^2*p+2*(p+2) := by exact_mod_cast closed
  have val : (primePowerSumCount p true 2 : ℚ) =
      (((p : ℚ)^2-2*p-1)*p+(2*p+4))/(2*(p+1)) := by
    apply (eq_div_iff (by positivity)).mpr
    nlinarith only [rat]
  rw [density,count_at odd unitN 1,decide_eq_true sq,val,Nat.cast_pow]
  dsimp [ratio,PrimePowerRatioProduct.ratio,floorDensity]
  field_simp [poly.ne',pp.ne']
  ring

/-- The density reduction available from any precision beyond p² is
bounded solely in terms of p, for every unit product. -/
theorem local_bound (odd : p ≠ 2) (unitN : ¬p ∣ n) {e : ℕ} (depth : 2 ≤ e) :
    density n (p^2) ≤ ratio p * density n (p^e) := by
  by_cases sq : IsSquare (n : ZMod p)
  · obtain ⟨k,rfl⟩ : ∃ k, e = k+1 := ⟨e-1,by omega⟩
    rw [square_second odd unitN sq]
    exact mul_le_mul_of_nonneg_left (square_floor odd unitN sq k) ((one_le_ratio odd).trans' (by decide))
  · rw [nonsquare_density odd unitN sq (by omega : 1 ≤ e)]
    exact le_mul_of_one_le_left (density_nonneg _ _) (one_le_ratio odd)

end PrimeFactors.PrimePowerDensityRatio
