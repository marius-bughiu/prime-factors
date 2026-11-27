import PrimeFactors.BoundedSmoothCount
import PrimeFactors.LargeBaseOrderPairs

/-! Summing over the possible smooth parts of large multiplicative orders.
The estimate keeps the reciprocal of the larger of the order cutoff and the smooth divisor. -/
namespace PrimeFactors.SmoothOrderTail
open Finset BoundedSmoothCount
set_option exponentiation.threshold 2050

private noncomputable def weight (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ)^(-s)
  map_one' := by simp
  map_mul' m n := by simp [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

/-- The finite smooth sum is bounded by its Euler product, before any multiplication by U^s. -/
theorem finite_mass (U B : ℕ) {s : ℝ} (hs : 0<s) :
    ∑ d ∈ Nat.smoothNumbersUpTo U B, (d : ℝ)^(-s) ≤
      ∏ p ∈ B.primesBelow, (1-(p:ℝ)^(-s))⁻¹ := by
  classical
  let f := weight s
  have nn (n : ℕ) : 0≤f n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have ltone {p : ℕ} (hp : p.Prime) : f p<1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_lt_zero.mpr hs)
  have series := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f:=f) (map_one _) (fun _ => map_mul _ _ _)
    (fun {p} hp => by
      simp only [map_pow,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (nn p) _)]
      exact summable_geometric_of_lt_one (nn p) (ltone hp)) B).2
  have smooth (d : ℕ) (hd : d ∈ Nat.smoothNumbersUpTo U B) := (Nat.mem_smoothNumbersUpTo.mp hd).2
  change ∑ d ∈ Nat.smoothNumbersUpTo U B, f d ≤ _
  rw [←sum_subtype_of_mem f smooth]
  apply (sum_le_hasSum _ (fun d _ => nn _) series).trans_eq (prod_congr rfl ?_)
  intro p hp
  simp only [map_pow]
  exact tsum_geometric_of_lt_one (nn p) (ltone (Nat.prime_of_mem_primesBelow hp))

private theorem split_weight {T d : ℕ} (tp : 0<T) (dp : 0<d) :
    1/((max T d : ℕ):ℝ) ≤ (T:ℝ)^(-(27/32:ℝ))*(d:ℝ)^(-(5/32:ℝ)) := by
  let K : ℝ := (max T d : ℕ)
  have tpos : 0<(T:ℝ) := by exact_mod_cast tp
  have dpos : 0<(d:ℝ) := by exact_mod_cast dp
  have tl : (T:ℝ)≤K := by dsimp [K]; exact_mod_cast le_max_left T d
  have dl : (d:ℝ)≤K := by dsimp [K]; exact_mod_cast le_max_right T d
  calc
    1/K = K^(-(27/32:ℝ))*K^(-(5/32:ℝ)) := by
      rw [←Real.rpow_add (tpos.trans_le tl)]
      norm_num [Real.rpow_neg_one]
    _ ≤ _ := mul_le_mul (Real.rpow_le_rpow_of_nonpos tpos tl (by norm_num))
      (Real.rpow_le_rpow_of_nonpos dpos dl (by norm_num))
      (Real.rpow_nonneg (tpos.trans_le tl).le _) (Real.rpow_nonneg tpos.le _)

/-- The large-order rectangle sum is dominated by the already certified Euler cap for 1000-smooth numbers. -/
theorem tilted (U T : ℕ) (tp : 0<T) :
    ∑ d ∈ Nat.smoothNumbersUpTo U 1001, 1/((max T d : ℕ):ℝ) ≤
      (T:ℝ)^(-(27/32:ℝ)) * eulerCap := by
  calc
    _ ≤ ∑ d ∈ Nat.smoothNumbersUpTo U 1001, (T:ℝ)^(-(27/32:ℝ))*(d:ℝ)^(-(5/32:ℝ)) :=
      sum_le_sum fun d hd => split_weight tp (Nat.pos_of_ne_zero (Nat.mem_smoothNumbersUpTo.mp hd).2.1)
    _ = _ := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left ((finite_mass U 1001 (s:=5/32) (by norm_num)).trans euler_1000)
      (Real.rpow_nonneg (Nat.cast_nonneg T) _)

/-- The large-order count pays for the possible smooth divisor with its reciprocal weight. -/
theorem count_tilt (U T : ℕ) (tp : 0<T) :
    ((LargeBaseOrderPairs.admissible U 1001 T).card:ℝ) ≤
      2*(U:ℝ)^2*((T:ℝ)^(-(27/32:ℝ))*eulerCap) :=
  (LargeBaseOrderPairs.count_max U 1001 T tp).trans
    (mul_le_mul_of_nonneg_left (tilted U T tp) (by positivity))

attribute [local irreducible] Nat.smoothNumbersUpTo

/-- At T = 2^403 the weighted smooth sum is strictly less than 2^-203 for every U. -/
theorem at_403 (U : ℕ) :
    ∑ d ∈ Nat.smoothNumbersUpTo U 1001, 1/((max (2^403) d : ℕ):ℝ) < 1/(2:ℝ)^203 := by
  have scale : (((2^403:ℕ):ℝ))^(-(27/32:ℝ)) ≤ ((2:ℝ)^340)⁻¹ := by
    rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),
      ←Real.rpow_natCast 2 (340:ℕ),←Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have cap : (eulerCap:ℝ) < (2:ℝ)^137 := by exact_mod_cast (show eulerCap<(2:ℕ)^137 by decide +kernel)
  apply (tilted U (2^403) (by positivity)).trans_lt
  calc
    _ ≤ ((2:ℝ)^340)⁻¹ * eulerCap := mul_le_mul_of_nonneg_right scale (Nat.cast_nonneg _)
    _ < ((2:ℝ)^340)⁻¹ * 2^137 := mul_lt_mul_of_pos_left cap (by positivity)
    _ = _ := by norm_num

/-- Apply directly after `LargeBaseOrderPairs.count_max`. -/
theorem scaled_403 :
    2*((2^1024:ℕ):ℝ)^2 * (∑ d ∈ Nat.smoothNumbersUpTo (2^1024) 1001,
      1/((max (2^403) d : ℕ):ℝ)) < (2:ℝ)^1846 := by
  apply (mul_lt_mul_of_pos_left (at_403 (2^1024)) (by positivity : 0<2*((2^1024:ℕ):ℝ)^2)).trans_eq
  norm_num

/-- The count over both shifted coordinates, before choosing a tested side of the product. -/
theorem large_403 : (LargeBaseOrderPairs.admissible (2^1024) 1001 (2^403)).card < 2^1846 := by
  exact_mod_cast (LargeBaseOrderPairs.count_max (2^1024) 1001 (2^403) (by positivity)).trans_lt scaled_403

end PrimeFactors.SmoothOrderTail
