import PrimeFactors.Fermat
import Mathlib.Data.Nat.Dist
import Mathlib.NumberTheory.DiophantineApproximation.Basic

namespace PrimeFactors

/-- Dirichlet approximation to the hidden ratio gives an integer band at a
slope in the complete, factor-independent list `b ≤ a ≤ 2*b`, `1 ≤ b ≤ K`. -/
theorem exists_balanced_multiplier_band {p q K : ℕ} (hp : 0 < p)
    (ordered : p ≤ q) (balanced : q ≤ 2 * p) (hK : 0 < K) :
    ∃ a b : ℕ, 0 < b ∧ b ≤ K ∧ b ≤ a ∧ a ≤ 2 * b ∧
      (K + 1) * Nat.dist (a * p) (b * q) ≤ p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨b, hb, hbK, approx⟩ :=
    Real.exists_nat_abs_mul_sub_round_le ((q : ℝ) / p) hK
  let j := round ((b : ℝ) * ((q : ℝ) / p))
  change |(b : ℝ) * ((q : ℝ) / p) - (j : ℝ)| ≤ 1 / (K + 1) at approx
  have tiny : |(b : ℝ) * ((q : ℝ) / p) - (j : ℝ)| < 1 :=
    approx.trans_lt ((div_lt_one (by positivity)).mpr (by linarith))
  have ratioLo : (1 : ℝ) ≤ q / (p : ℝ) := (one_le_div hpR).mpr (by exact_mod_cast ordered)
  have ratioHi : (q : ℝ) / p ≤ 2 := (div_le_iff₀ hpR).mpr (by exact_mod_cast balanced)
  have lo : (b : ℝ) ≤ (b : ℝ) * ((q : ℝ) / p) := by
    simpa using mul_le_mul_of_nonneg_left ratioLo (Nat.cast_nonneg (α := ℝ) b)
  have hi : (b : ℝ) * ((q : ℝ) / p) ≤ 2 * (b : ℝ) := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left ratioHi (Nat.cast_nonneg (α := ℝ) b)
  have bj : (b : ℤ) ≤ j := by
    by_contra bad
    have badZ : j + 1 ≤ (b : ℤ) := Int.add_one_le_iff.mpr (lt_of_not_ge bad)
    have badR : (j : ℝ) + 1 ≤ b := by exact_mod_cast badZ
    linarith [(abs_lt.mp tiny).2]
  have jb : j ≤ 2 * (b : ℤ) := by
    by_contra bad
    have badZ : 2 * (b : ℤ) + 1 ≤ j := Int.add_one_le_iff.mpr (lt_of_not_ge bad)
    have badR : 2 * (b : ℝ) + 1 ≤ j := by exact_mod_cast badZ
    linarith [(abs_lt.mp tiny).1]
  lift j to ℕ using (show 0 ≤ j by omega) with a ha
  refine ⟨a, b, hb, hbK, by exact_mod_cast bj, by exact_mod_cast jb, ?_⟩
  have scaled := (le_div_iff₀ (by positivity : (0 : ℝ) < K + 1)).mp approx
  have gap : |(b : ℝ) * q - a * p| * (K + 1) ≤ p := by
    have id : (b : ℝ) * q - a * p = ((b : ℝ) * (q / (p : ℝ)) - a) * p := by
      field_simp
      ring
    rw [id, abs_mul, abs_of_pos hpR, mul_right_comm]
    simpa using mul_le_mul_of_nonneg_right scaled hpR.le
  rcases le_total (a * p) (b * q) with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    have hR : (a : ℝ) * p ≤ b * q := by exact_mod_cast h
    rw [abs_of_nonneg (sub_nonneg.mpr hR)] at gap
    exact_mod_cast (show ((K + 1) * ↑(b * q - a * p) : ℝ) ≤ p by
      rw [Nat.cast_sub h]; push_cast; simpa [mul_comm] using gap)
  · rw [Nat.dist_eq_sub_of_le_right h]
    have hR : (b : ℝ) * q ≤ a * p := by exact_mod_cast h
    rw [abs_of_nonpos (sub_nonpos.mpr hR), neg_sub] at gap
    exact_mod_cast (show ((K + 1) * ↑(a * p - b * q) : ℝ) ≤ p by
      rw [Nat.cast_sub h]; push_cast; simpa [mul_comm] using gap)

/-- Every scaled sum satisfies the difference-of-squares identity, independently
of which of the two scaled factors is larger. -/
theorem multiplier_sum_square (p q a b : ℕ) :
    (a * p + b * q) ^ 2 = 4 * a * b * (p * q) + (Nat.dist (a * p) (b * q)) ^ 2 := by
  rcases le_total (a * p) (b * q) with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    have hdiff := Nat.sub_add_cancel h
    nlinarith only [congrArg (fun v : ℕ => v ^ 2) hdiff,
      congrArg (fun v : ℕ => (a * p) * v) hdiff]
  · rw [Nat.dist_eq_sub_of_le_right h]
    have hdiff := Nat.sub_add_cancel h
    nlinarith only [congrArg (fun v : ℕ => v ^ 2) hdiff,
      congrArg (fun v : ℕ => (b * q) * v) hdiff]

/-- At least one window contains the true scaled sum. Its endpoints use only
the product and the indices of the window, so all windows can be generated
without knowing the pair that supplied the approximation. -/
theorem exists_balanced_multiplier_window {p q K : ℕ} (hp : 0 < p)
    (ordered : p ≤ q) (balanced : q ≤ 2 * p) (hK : 0 < K) :
    ∃ a b : ℕ, 0 < b ∧ b ≤ K ∧ b ≤ a ∧ a ≤ 2 * b ∧
      let r := ceilSqrt (4 * a * b * (p * q))
      let t := a * p + b * q
      r ≤ t ∧ t ≤ r + (p * q).sqrt / (2 * b * (K + 1) ^ 2) := by
  obtain ⟨a, b, hb, hbK, hba, hab, band⟩ :=
    exists_balanced_multiplier_band hp ordered balanced hK
  refine ⟨a, b, hb, hbK, hba, hab, ?_⟩
  let r := ceilSqrt (4 * a * b * (p * q))
  let t := a * p + b * q
  let d := Nat.dist (a * p) (b * q)
  change r ≤ t ∧ t ≤ r + (p * q).sqrt / (2 * b * (K + 1) ^ 2)
  have identity : t ^ 2 = 4 * a * b * (p * q) + d ^ 2 := multiplier_sum_square _ _ _ _
  have hr : 4 * a * b * (p * q) ≤ r ^ 2 := ceilSqrt_le_iff.mp (le_refl r)
  have hrt : r ≤ t := ceilSqrt_le_iff.mpr (by omega)
  have den : 2 * b * p ≤ t := by
    dsimp [t]
    nlinarith only [Nat.mul_le_mul_right p hba, Nat.mul_le_mul_left b ordered]
  have factor : (t - r) * (2 * b * p) ≤ d ^ 2 := calc
    _ ≤ (t - r) * (t + r) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ d ^ 2 := by
      have eq := Nat.sub_add_cancel hrt
      nlinarith only [identity, hr, congrArg (fun v : ℕ => v ^ 2) eq,
        congrArg (fun v : ℕ => (t - r) * v) eq]
  have gapSq : ((K + 1) * d) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left band 2
  have scaled : ((t - r) * (2 * b * (K + 1) ^ 2)) * p ≤ p * p := by
    nlinarith only [Nat.mul_le_mul_right ((K + 1) ^ 2) factor, gapSq]
  have pBound := (Nat.le_of_mul_le_mul_right scaled hp)
  have rootBound : p ≤ (p * q).sqrt := Nat.le_sqrt.mpr (Nat.mul_le_mul_left p ordered)
  have offset := (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * b * (K + 1) ^ 2)).mpr
    (pBound.trans rootBound)
  exact ⟨hrt, by omega⟩

/-- Size of the full list of square tests, including overlaps. At denominator
`b = i+1` there are `b+1` numerators, each with the indicated window length. -/
noncomputable def multiplierCandidateCount (n K : ℕ) : ℕ :=
  ∑ i ∈ Finset.range K, (i + 2) * (1 + n.sqrt / (2 * (i + 1) * (K + 1) ^ 2))

/-- Choosing the scale by the product alone gives at most a quadratic number
of square tests in `K` whenever `sqrt n ≤ (K+1)³`. -/
theorem multiplierCandidateCount_le {n K : ℕ} (scale : n.sqrt ≤ (K + 1) ^ 3) :
    multiplierCandidateCount n K ≤ 2 * K * (K + 1) := by
  unfold multiplierCandidateCount
  calc
    _ ≤ ∑ _i ∈ Finset.range K, 2 * (K + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiK := Finset.mem_range.mp hi
      let w := n.sqrt / (2 * (i + 1) * (K + 1) ^ 2)
      have hw : w * (2 * (i + 1) * (K + 1) ^ 2) ≤ (K + 1) ^ 3 :=
        (Nat.div_mul_le_self _ _).trans scale
      have copies : i + 2 ≤ 2 * (i + 1) := by omega
      have granularity : (i + 2) * w * (K + 1) ^ 2 ≤ (K + 1) * (K + 1) ^ 2 := by
        calc
          _ ≤ (2 * (i + 1)) * w * (K + 1) ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ copies)
          _ = w * (2 * (i + 1) * (K + 1) ^ 2) := by ring
          _ ≤ (K + 1) ^ 3 := hw
          _ = _ := by ring
      have total := Nat.le_of_mul_le_mul_right granularity (by positivity)
      change (i + 2) * (1 + w) ≤ 2 * (K + 1)
      rw [Nat.mul_add, Nat.mul_one]
      omega
    _ = _ := by simp; ring

/-- At the true weighted sum, trying both signs recovers the first factor by
exact division by twice its multiplier. The square test gives its root `d`. -/
theorem multiplier_recovers_factor {p q a b t d : ℕ} (ha : 0 < a)
    (sum : t = a * p + b * q) (hit : t ^ 2 = 4 * a * b * (p * q) + d ^ 2) :
    (t - d) / (2 * a) = p ∨ (t + d) / (2 * a) = p := by
  subst t
  have hd : d = Nat.dist (a * p) (b * q) := by
    apply (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp
    nlinarith only [hit, multiplier_sum_square p q a b]
  subst d
  have denom : 0 < 2 * a := by positivity
  rcases le_total (a * p) (b * q) with h | h
  · left
    rw [Nat.dist_eq_sub_of_le h,
      show a * p + b * q - (b * q - a * p) = p * (2 * a) by
        have heq := Nat.sub_add_cancel h
        rw [show p * (2 * a) = a * p + a * p by ring]
        omega, Nat.mul_div_cancel _ denom]
  · right
    rw [Nat.dist_eq_sub_of_le_right h,
      show a * p + b * q + (a * p - b * q) = p * (2 * a) by
        have heq := Nat.sub_add_cancel h
        rw [show p * (2 * a) = a * p + a * p by ring]
        omega, Nat.mul_div_cancel _ denom]

/-- Total number of square tests in an explicit balanced example. -/
theorem multiplier_example_count : multiplierCandidateCount 1900014700027 111 = 8978 := by
  have root : Nat.sqrt 1900014700027 = 1378410 := by norm_num
  simp only [multiplierCandidateCount, root]
  decide +kernel

/-- At (19,10), the first sum for this product already yields the factors. -/
theorem multiplier_example_hit : ceilSqrt (4 * 19 * 10 * 1900014700027) = 38000147 ∧
    38000147 ^ 2 = 4 * 19 * 10 * 1900014700027 + 33 ^ 2 ∧
    (38000147 - 33) / (2 * 19) = 1000003 ∧ 1000003 * 1900009 = 1900014700027 := by
  have lo : ¬ ceilSqrt (4 * 19 * 10 * 1900014700027) ≤ 38000146 := by
    rw [ceilSqrt_le_iff]
    norm_num
  have hi : ceilSqrt (4 * 19 * 10 * 1900014700027) ≤ 38000147 := by
    rw [ceilSqrt_le_iff]
    norm_num
  exact ⟨by omega, by norm_num, by norm_num, by norm_num⟩

end PrimeFactors
