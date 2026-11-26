import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Linarith

/-! A finite Rankin bound for squarefree-supported square multiples.
The real exponent may be any number at least one half. -/
namespace PrimeFactors.WeightedSubsetRankin
open Finset

/-- A positive excess magnitude whose squarefree part divides the fixed support M. -/
def Supported (M Y D : ℕ) : Prop :=
  D≤Y ∧ ∃ m u : ℕ, Squarefree m ∧ m∣M ∧ 0<u ∧ D=m*u^2

/-- In a single squarefree class there are at most floor(sqrt(Y/m))
possibilities. This also treats m>Y, where the count is zero. -/
theorem root_bound {Y m : ℕ} (mp : 0<m) {θ : ℝ} (half : 1/2≤θ) :
    ((Y/m).sqrt : ℝ) ≤ (Y:ℝ)^θ * (m:ℝ)^(-θ) := by
  let u := (Y/m).sqrt
  by_cases zero : u=0
  · change (u:ℝ) ≤ _
    rw [zero,Nat.cast_zero]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  have up : (1:ℝ)≤u := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr zero
  have size : (m:ℝ)*(u:ℝ)^2≤Y := by
    exact_mod_cast ((Nat.mul_le_mul_left m (Nat.sqrt_le' (Y/m))).trans (Nat.mul_div_le ..))
  have pow := Real.rpow_le_rpow (by positivity : 0≤(m:ℝ)*(u:ℝ)^2) size (by linarith : 0≤θ)
  rw [Real.mul_rpow (by positivity) (by positivity)] at pow
  have small : (u:ℝ)≤((u:ℝ)^2)^θ := calc
    (u:ℝ) = Real.sqrt ((u:ℝ)^2) := (Real.sqrt_sq (by positivity)).symm
    _ = ((u:ℝ)^2)^(1/2 : ℝ) := Real.sqrt_eq_rpow _
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ up) half
  rw [Real.rpow_neg (by positivity),←div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast mp) _)).mpr
  exact (mul_le_mul_of_nonneg_right small (Real.rpow_nonneg (by positivity) _)).trans
    (by simpa only [mul_comm] using pow)

/-- The squarefree kernel determined by a subset of the prime support. -/
noncomputable def kernel (s : Finset ℕ) := ∏ p∈s, p

/-- Count all possible roots in each class, allowing for a set containing
only some of the supported magnitudes. -/
theorem count_le_roots {M Y : ℕ} (mp : 0<M) (S : Finset ℕ)
    (supported : ∀ D∈S, Supported M Y D) :
    S.card ≤ ∑ t∈M.primeFactors.powerset, (Y/kernel t).sqrt := by
  classical
  let cell (t : Finset ℕ) := (Icc 1 (Y/kernel t).sqrt).image (fun u => kernel t*u^2)
  have cover : S⊆M.primeFactors.powerset.biUnion cell := by
    intro D hD
    obtain ⟨size,m,u,free,dvd,up,rfl⟩ := supported D hD
    have pos := Nat.pos_of_ne_zero free.ne_zero
    have rad : kernel m.primeFactors=m := Nat.prod_primeFactors_of_squarefree free
    refine mem_biUnion.mpr ⟨m.primeFactors,mem_powerset.mpr (Nat.primeFactors_mono dvd mp.ne'),
      mem_image.mpr ⟨u,mem_Icc.mpr ⟨up,?_⟩,by rw [rad]⟩⟩
    rw [rad,Nat.le_sqrt',Nat.le_div_iff_mul_le pos]
    rwa [mul_comm]
  apply (card_le_card cover).trans
  apply card_biUnion_le.trans
  exact sum_le_sum (fun t _ => (card_image_le (s:=Icc 1 (Y/kernel t).sqrt)
    (f:=fun u => kernel t*u^2)).trans (by simp))

/-- Rankin's estimate for the finite floor sum over squarefree divisors.
Divisors above Y contribute zero to the left side. -/
theorem floor_sum (M Y : ℕ) (θ : ℝ) (half : 1/2≤θ) :
    (∑ t∈M.primeFactors.powerset, ((Y/kernel t).sqrt:ℝ)) ≤
      (Y:ℝ)^θ * ∏ p∈M.primeFactors, (1+(p:ℝ)^(-θ)) := by
  rw [prod_one_add,mul_sum]
  apply sum_le_sum
  intro t ht
  have sub := mem_powerset.mp ht
  have pos : 0<kernel t := prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (sub hp)).pos
  rw [Real.finset_prod_rpow t (fun p : ℕ => (p:ℝ)) (fun _ _ => Nat.cast_nonneg _) (-θ),←Nat.cast_prod]
  exact root_bound pos half

/-- Euler product bound for any finite set of distinct supported magnitudes.
It includes M=1, Y=0, and the endpoint θ=1/2. -/
theorem radicands {M Y : ℕ} (mp : 0<M) (θ : ℝ) (half : 1/2≤θ) (S : Finset ℕ)
    (supported : ∀ D∈S, Supported M Y D) :
    (S.card:ℝ) ≤ (Y:ℝ)^θ * ∏ p∈M.primeFactors, (1+(p:ℝ)^(-θ)) := by
  apply le_trans _ (floor_sum M Y θ half)
  exact_mod_cast count_le_roots mp S supported

/-- For fixed weight and label, a magnitude admits at most two input products,
one for each sign of the excess A²-4rN. -/
theorem signed_inputs {M Y r A : ℕ} (mp : 0<M) (rp : 0<r) (θ : ℝ) (half : 1/2≤θ)
    (S : Finset ℕ) (supported : ∀ n∈S, ∃ D, Supported M Y D ∧
      (A^2=4*r*n+D ∨ 4*r*n=A^2+D)) :
    (S.card:ℝ) ≤ 2*((Y:ℝ)^θ * ∏ p∈M.primeFactors, (1+(p:ℝ)^(-θ))) := by
  classical
  let magnitudes := (Icc 1 Y).filter (Supported M Y)
  let cell (D : ℕ) : Finset ℕ := {(A^2-D)/(4*r),(A^2+D)/(4*r)}
  have cover : S⊆magnitudes.biUnion cell := by
    intro n hn
    obtain ⟨D,okay,e⟩ := supported n hn
    obtain ⟨m,u,free,_,up,form⟩ := okay.2
    have pos : 0<D := form ▸ Nat.mul_pos (Nat.pos_of_ne_zero free.ne_zero) (pow_pos up _)
    refine mem_biUnion.mpr ⟨D,mem_filter.mpr ⟨mem_Icc.mpr ⟨pos,okay.1⟩,okay⟩,?_⟩
    have wr : 0<4*r := Nat.mul_pos (by decide) rp
    rcases e with e|e
    · exact mem_insert.mpr (Or.inl (by rw [e,Nat.add_sub_cancel,Nat.mul_div_cancel_left _ wr]))
    · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (by rw [←e,Nat.mul_div_cancel_left _ wr])))
  have count : S.card≤magnitudes.card*2 := (card_le_card cover).trans
    (card_biUnion_le_card_mul _ _ _ (fun _ _ => card_le_two))
  have actual : (S.card:ℝ)≤2*(magnitudes.card:ℝ) := by
    exact_mod_cast count.trans_eq (Nat.mul_comm ..)
  exact actual.trans (mul_le_mul_of_nonneg_left
    (radicands mp θ half magnitudes (fun _ h => (mem_filter.mp h).2)) (by norm_num))

end PrimeFactors.WeightedSubsetRankin
