import PrimeFactors.FactorSumProductCell
import PrimeFactors.MonotoneSumBlocks

/-! Bounds on how many sorted pairs have a sum close to a single
nondecreasing predictor of their product. The predictor is unrestricted
apart from monotonicity. -/
namespace PrimeFactors.MonotoneSumCoverage

open Finset MonotoneSumBlocks

/-- The interval swept by the predictor and the curvature of the
constant-sum product sequence control two different factors in this bound. -/
theorem card_bound (A : Finset (ℕ×ℕ)) (g : ℕ→ℕ) (mono : Monotone g) (B W E : ℕ)
    (width : 0<W) (sorted : ∀ z∈A, z.1≤z.2) (within : ∀ z∈A, z.1*z.2<B*W)
    (fit : ∀ z∈A, g (z.1*z.2)≤z.1+z.2+E ∧ z.1+z.2≤g (z.1*z.2)+E) :
    A.card ≤ (g (B*W)-g 0+(2*E+1)*B)*(W.sqrt+1) := by
  let tag (z : ℕ×ℕ) := (z.1*z.2/W,z.1+z.2)
  have interval (n : ℕ) : (n/W)*W≤n ∧ n<(n/W+1)*W :=
    ⟨Nat.div_mul_le_self ..,by simpa only [Nat.mul_comm W] using Nat.lt_mul_div_succ n width⟩
  have into (z : ℕ×ℕ) (hz : z∈A) : tag z∈cells g B W E := by
    obtain ⟨lower,upper⟩ := fit z hz
    exact mem_quotient mono width (within z hz) (Nat.sub_le_of_le_add lower) upper
  have fiber (v : ℕ×ℕ) (_hv : v∈cells g B W E) :
      (A.filter (fun z => tag z=v)).card≤W.sqrt+1 := by
    apply FactorSumProductCell.card_bound _ v.2 v.1 W
    · intro z hz
      exact sorted z (mem_filter.mp hz).1
    · intro z hz
      exact congrArg Prod.snd (mem_filter.mp hz).2
    · intro z hz
      have eq : z.1*z.2/W=v.1 := congrArg Prod.fst (mem_filter.mp hz).2
      simpa only [←eq] using interval (z.1*z.2)
  calc
    A.card ≤ (W.sqrt+1)*(cells g B W E).card := card_le_mul_card_image_of_maps_to into _ fiber
    _ = (cells g B W E).card*(W.sqrt+1) := Nat.mul_comm ..
    _ ≤ _ := Nat.mul_le_mul_right _ (MonotoneSumBlocks.card_le g mono B W E)

end PrimeFactors.MonotoneSumCoverage
