import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.EulerProduct.Basic

namespace PrimeFactors.SmoothFractionHyperbola

open Finset

/-- Ordered pairs of positive integers supported on the given primes, with
a single product bound. Either coordinate can take the full budget. -/
noncomputable def pairs (X : ℕ) (base : Finset ℕ) : Finset (ℕ × ℕ) :=
  let s := (range (X+1)).filter (fun n => n ∈ Nat.factoredNumbers base)
  (s ×ˢ s).filter (fun ab => ab.1*ab.2 ≤ X)

theorem mem_pairs {X a b : ℕ} {base : Finset ℕ} :
    (a,b) ∈ pairs X base ↔
    a ∈ Nat.factoredNumbers base ∧ b ∈ Nat.factoredNumbers base ∧ a*b ≤ X := by
  simp only [pairs, mem_filter, mem_product, mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨⟨_,ha⟩,_,hb⟩,h⟩
    exact ⟨ha,hb,h⟩
  · rintro ⟨ha,hb,h⟩
    exact ⟨⟨⟨(Nat.le_mul_of_pos_right a (Nat.pos_of_ne_zero hb.1)).trans h, ha⟩,
      (Nat.le_mul_of_pos_left b (Nat.pos_of_ne_zero ha.1)).trans h, hb⟩,h⟩

private noncomputable def weight (σ : ℝ) : ℕ →* ℝ where
  toFun := fun n => (n : ℝ)^(-σ)
  map_one' := by simp
  map_mul' := fun a b => by simp [Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

private theorem rankin_weighted (X : ℕ) (σ : ℝ) (hσ : 0 < σ) (s : Finset ℕ)
    (rows : Finset (ℕ × ℕ)) (incl : rows ⊆ s ×ˢ s)
    (bounds : ∀ ab ∈ rows, 0 < ab.1 ∧ 0 < ab.2 ∧ ab.1*ab.2 ≤ X) :
    (rows.card : ℝ) ≤ (X : ℝ)^σ * (∑ n ∈ s, weight σ n)^2 := by
  let w := weight σ
  have nonneg (n : ℕ) : 0 ≤ w n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have majorant (ab : ℕ × ℕ) (hab : ab ∈ rows) :
      1 ≤ (X : ℝ)^σ * (w ab.1 * w ab.2) := by
    obtain ⟨apos,bpos,h⟩ := bounds ab hab
    have pos : 0 < ((ab.1 * ab.2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos apos bpos
    rw [← map_mul, show w (ab.1*ab.2) = (((ab.1*ab.2 : ℕ) : ℝ)^σ)⁻¹ from Real.rpow_neg pos.le _,
      ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos pos _), one_mul]
    exact Real.rpow_le_rpow pos.le (by exact_mod_cast h) hσ.le
  have weighted : (∑ ab ∈ rows, w ab.1 * w ab.2) ≤ (∑ n ∈ s, w n)^2 := by
    calc
      _ ≤ ∑ ab ∈ s ×ˢ s, w ab.1 * w ab.2 :=
        sum_le_sum_of_subset_of_nonneg incl (fun ab _ _ => mul_nonneg (nonneg _) (nonneg _))
      _ = _ := by rw [sum_product, sq, sum_mul_sum]
  calc
    (rows.card : ℝ) = ∑ _ ∈ rows, (1 : ℝ) := by simp
    _ ≤ ∑ ab ∈ rows, (X : ℝ)^σ * (w ab.1 * w ab.2) := sum_le_sum majorant
    _ = (X : ℝ)^σ * ∑ ab ∈ rows, w ab.1 * w ab.2 := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left weighted (Real.rpow_nonneg (Nat.cast_nonneg X) _)

/-- Rankin's bound for all ordered pairs with smooth positive coordinates
and product at most X, for an arbitrary finite prime base and every σ > 0. -/
theorem rankin_pairs (X : ℕ) (base : Finset ℕ) (primes : ∀ p ∈ base, Nat.Prime p)
    (σ : ℝ) (hσ : 0 < σ) :
    ((pairs X base).card : ℝ) ≤
      (X : ℝ)^σ * (∏ p ∈ base, (1 - (p : ℝ)^(-σ))⁻¹)^2 := by
  classical
  let w := weight σ
  have nonneg (n : ℕ) : 0 ≤ w n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have geom {p : ℕ} (hp : p.Prime) : ‖w p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (nonneg p)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_lt_zero.mpr hσ)
  have euler := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := w) geom base).2
  rw [filter_true_of_mem primes] at euler
  let s := (range (X+1)).filter (fun n => n ∈ Nat.factoredNumbers base)
  have smooth (n : ℕ) (hn : n ∈ s) : n ∈ Nat.factoredNumbers base := (mem_filter.mp hn).2
  have sumBound : ∑ n ∈ s, w n ≤ ∏ p ∈ base, (1 - w p)⁻¹ := by
    rw [← sum_subtype_of_mem w smooth]
    exact sum_le_hasSum _ (fun n _ => nonneg _) euler
  have bounds (ab : ℕ × ℕ) (h : ab ∈ pairs X base) := mem_pairs.mp h
  exact (rankin_weighted X σ hσ s (pairs X base) (filter_subset _ _) (fun ab h =>
    ⟨Nat.pos_of_ne_zero (bounds ab h).1.1, Nat.pos_of_ne_zero (bounds ab h).2.1.1,
      (bounds ab h).2.2⟩)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (sum_nonneg fun n _ => nonneg n) sumBound 2)
    (Real.rpow_nonneg (Nat.cast_nonneg X) _))

/-- In the usual cutoff convention, the base contains every prime at most B. -/
theorem rankin_cutoff (X B : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    ((pairs X (B+1).primesBelow).card : ℝ) ≤
      (X : ℝ)^σ * (∏ p ∈ (B+1).primesBelow, (1 - (p : ℝ)^(-σ))⁻¹)^2 :=
  rankin_pairs X _ (fun _ hp => Nat.prime_of_mem_primesBelow hp) σ hσ

/-- Odd valuations specify the primes in the squarefree part. The remaining
square root is bounded by the represented positive integer. -/
theorem square_part_witness {n : ℕ} {base : Finset ℕ} (hn : 0 < n)
    (supported : ∀ p, Odd (n.factorization p) → p ∈ base) :
    ∃ k ≤ n, ∃ t ∈ base.powerset, k^2*(∏ p ∈ t, p) = n := by
  obtain ⟨c,k,hc,hk,hprod,free⟩ := Nat.sq_mul_squarefree_of_pos hn
  refine ⟨k, Nat.le_of_dvd hn ⟨k*c, by simpa [sq, mul_assoc] using hprod.symm⟩,
    c.primeFactors, mem_powerset.mpr ?_, ?_⟩
  · intro p hp
    apply supported p
    have hone := Nat.factorization_eq_one_of_squarefree free
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
    rw [← hprod, Nat.factorization_mul (pow_pos hk _).ne' hc.ne', Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.smul_apply, hone]
    exact ⟨k.factorization p, by simp⟩
  · rwa [Nat.prod_primeFactors_of_squarefree free]

/-- Arbitrary square factors can use primes outside the base. This bound
applies to any set of eligible ordered pairs, including reduced fractions.
Its infinite sum is the real Dirichlet series for ζ(2σ). -/
theorem rankin_square_parts (rows : Finset (ℕ × ℕ)) (X : ℕ) (base : Finset ℕ) (σ : ℝ)
    (hσ : 1 < 2*σ) (bounds : ∀ ab ∈ rows, 0 < ab.1 ∧ 0 < ab.2 ∧ ab.1*ab.2 ≤ X)
    (supported : ∀ ab ∈ rows, ∀ p, Odd (ab.1.factorization p) ∨ Odd (ab.2.factorization p) →
      p ∈ base) :
    (rows.card : ℝ) ≤ (X : ℝ)^σ *
      ((∑' k : ℕ, (k : ℝ)^(-(2*σ))) * ∏ p ∈ base, (1 + (p : ℝ)^(-σ)))^2 := by
  classical
  let w := weight σ
  let value (u : ℕ × Finset ℕ) := u.1^2*(∏ p ∈ u.2, p)
  let reprs := range (X+1) ×ˢ base.powerset
  let s := reprs.image value
  have incl : rows ⊆ s ×ˢ s := by
    intro ab hab
    obtain ⟨apos,bpos,h⟩ := bounds ab hab
    have represent {n : ℕ} (hpos : 0 < n) (hX : n ≤ X)
        (hs : ∀ p, Odd (n.factorization p) → p ∈ base) : n ∈ s := by
      obtain ⟨k,hk,t,ht,he⟩ := square_part_witness hpos hs
      exact mem_image.mpr ⟨(k,t), mem_product.mpr ⟨mem_range.mpr
        (Nat.lt_succ_iff.mpr (hk.trans hX)), ht⟩, he⟩
    exact mem_product.mpr ⟨represent apos ((Nat.le_mul_of_pos_right _ bpos).trans h)
      (fun p hp => supported ab hab p (Or.inl hp)),
      represent bpos ((Nat.le_mul_of_pos_left _ apos).trans h)
      (fun p hp => supported ab hab p (Or.inr hp))⟩
  have nonneg (n : ℕ) : 0 ≤ w n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have squareWeight (k : ℕ) : (w k)^2 = (k : ℝ)^(-(2*σ)) := by
    change ((k : ℝ)^(-σ))^2 = _
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg k)]
    congr 1
    push_cast
    ring
  have finiteWeight : ∑ n ∈ s, w n ≤
      (∑ k ∈ range (X+1), (k : ℝ)^(-(2*σ))) * ∏ p ∈ base, (1+w p) := by
    calc
      _ ≤ ∑ u ∈ reprs, w (value u) := sum_image_le_of_nonneg fun n _ => nonneg n
      _ = _ := by
        dsimp only [reprs]
        rw [sum_product, prod_one_add, sum_mul_sum]
        simp only [value, map_mul, map_pow, map_prod, squareWeight]
  have zetaBound : (∑ k ∈ range (X+1), (k : ℝ)^(-(2*σ))) ≤
      ∑' k : ℕ, (k : ℝ)^(-(2*σ)) :=
    sum_le_hasSum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (Real.summable_nat_rpow.mpr (by linarith : -(2*σ) < -1)).hasSum
  apply (rankin_weighted X σ (by linarith) s rows incl bounds).trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg X) _)
  apply pow_le_pow_left₀ (sum_nonneg fun n _ => nonneg n) _ 2
  exact finiteWeight.trans (mul_le_mul_of_nonneg_right zetaBound
    (prod_nonneg fun p _ => add_nonneg zero_le_one (nonneg p)))

end PrimeFactors.SmoothFractionHyperbola
