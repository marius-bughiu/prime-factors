import PrimeFactors.DyadicSumMenuBudget

/-! An attained modular menu optimum gives two-sided control of the best
guess-menu success rate on actual prime pairs with that product remainder. -/
namespace PrimeFactors.DyadicMenuPopulationOptimum

open Finset DyadicSumMenuBudget
open scoped Classical
set_option exponentiation.threshold 4096

private noncomputable def menus (α : Type*) [Fintype α] (B : ℕ) : Finset (Finset α) :=
  univ.filter (fun A => A.card≤B)

private theorem menus_nonempty (α : Type*) [Fintype α] (B : ℕ) : (menus α B).Nonempty :=
  ⟨∅,mem_filter.mpr ⟨mem_univ _,by simp⟩⟩

private noncomputable def best {α β : Type*} [Fintype α] [LinearOrder β]
    (B : ℕ) (f : Finset α→β) : β :=
  ((menus α B).image f).max' ((menus_nonempty α B).image f)

private theorem best_spec {α β : Type*} [Fintype α] [LinearOrder β]
    (B : ℕ) (f : Finset α→β) : IsGreatest {y : β | ∃ A : Finset α, A.card≤B ∧ y=f A} (best B f) := by
  constructor
  · obtain ⟨A,ok,eq⟩ := mem_image.mp (max'_mem _ ((menus_nonempty α B).image f))
    exact ⟨A,(mem_filter.mp ok).2,eq.symm⟩
  · rintro _ ⟨A,size,rfl⟩
    exact le_max' _ _ (mem_image.mpr ⟨A,mem_filter.mpr ⟨mem_univ _,size⟩,rfl⟩)

/-- Best conditional prime-pair probability when a menu contains at most B
different guesses. This finite maximum also exists for a zero budget. -/
noncomputable def bestActual {e : ℕ} (r : U e) (B : ℕ) : ℝ := best B (actualShare r)

theorem bestActual_spec {e : ℕ} (r : U e) (B : ℕ) :
    IsGreatest {p : ℝ | ∃ A : Finset (ZMod (2^e)), A.card≤B ∧ p=actualShare r A} (bestActual r B) :=
  best_spec B (actualShare r)

/-- Transfer the optimum itself. Its lower bound uses a modular maximizer,
while the upper bound applies to the maximizing prime-population menu. -/
theorem optimum {e : ℕ} (cap : e≤161) (r : U e) (B W : ℕ)
    (top : IsGreatest {n : ℕ | ∃ A : Finset (ZMod (2^e)), A.card≤B ∧ n=mass r A} W)
    {li : ℕ→ℝ} (h : 2≤e → ExtendedModulusPrimeSupply.Endpoints (2^e) li) :
    let C := (W:ℝ)/(2^e:ℕ).totient
    |bestActual r B-C|≤C/(2:ℝ)^146 := by
  let C := (W:ℝ)/(2^e:ℕ).totient
  change |bestActual r B-C|≤C/(2:ℝ)^146
  obtain ⟨A,hA,atA⟩ := (bestActual_spec r B).1
  obtain ⟨M,hM,atM⟩ := top.1
  have below : modularShare r A≤C := div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (top.2 ⟨A,hA,rfl⟩)) (Nat.cast_nonneg _)
  have same : modularShare r M=C := by rw [modularShare,←atM]
  have lo := (abs_le.mp (transfer cap h r M)).1
  rw [same] at lo
  have feasible := (bestActual_spec r B).2 ⟨M,hM,rfl⟩
  have hi := (abs_le.mp (transfer cap h r A)).2
  have eps := div_le_div_of_nonneg_right below (show (0:ℝ)≤2^146 by positivity)
  exact abs_le.mpr ⟨by linarith only [lo,feasible],by linarith only [hi,below,eps,atA]⟩

/-- For a fixed odd 161-bit product word, W covered modular pairs means
the best actual success rate is within relative error 2^-146 of W/2^160. -/
theorem optimum_161 (r : U 161) (B W : ℕ)
    (top : IsGreatest {n : ℕ | ∃ A : Finset (ZMod (2^161)), A.card≤B ∧ n=mass r A} W)
    {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints (2^161) li) :
    |bestActual r B-(W:ℝ)/(2:ℝ)^160|≤((W:ℝ)/(2:ℝ)^160)/(2:ℝ)^146 := by
  have result := optimum (le_refl 161) r B W top (fun _ => h)
  simpa only [Nat.totient_prime_pow_succ Nat.prime_two,Nat.reduceSub,Nat.mul_one,Nat.cast_pow,
    Nat.cast_ofNat] using result

end PrimeFactors.DyadicMenuPopulationOptimum
