import PrimeFactors.SquareRootPhasePopulation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.ExponentialBounds

/-! Finite dual certificates for the Euler correction of a squarefree support.
The bin counts and reward majorants are certificate inputs. No choice of dual
prices needs to be optimal for the upper bound to hold. -/

namespace PrimeFactors.WeightedPrimeBudget
open Finset

/-- Distinct prime divisors jointly consume at most the bit budget of their product. -/
theorem bit_budget {M : ℕ} (positive : 0 < M) {P : Finset ℕ} (sub : P ⊆ M.primeFactors) :
    ∑ p ∈ P, p.log2 ≤ M.log2 := by
  apply (Nat.le_log2 positive.ne').mpr
  rw [← Finset.prod_pow_eq_pow_sum]
  calc
    ∏ p ∈ P, 2 ^ p.log2 ≤ ∏ p ∈ P, p := by
      apply Finset.prod_le_prod'
      intro p hp
      exact (Nat.le_log2 (Nat.prime_of_mem_primeFactors (sub hp)).ne_zero).mp le_rfl
    _ ≤ M := Nat.le_of_dvd positive <|
      (Finset.prod_dvd_prod_of_subset P M.primeFactors id sub).trans (Nat.prod_primeFactors_dvd M)

/-- The central binomial octave cap applies to the half-open bins used in the
integer program. For j ≥ 2 the lower endpoint is composite. -/
theorem octave_capacity {j : ℕ} (two : 2 ≤ j) (P : Finset ℕ)
    (members : ∀ p ∈ P, p.Prime ∧ 2^j ≤ p ∧ p < 2^(j+1)) :
    P.card ≤ 2^(j+1) / j := by
  have large : 2 < 2^j := lt_of_lt_of_le (by decide : 2 < 2^2)
    (Nat.pow_le_pow_right (by decide) two)
  have composite : ¬(2^j).Prime := Nat.not_prime_of_dvd_of_lt
    (dvd_pow_self 2 (by omega : j ≠ 0)) le_rfl large
  have bound := SquareRootPhasePopulation.prime_upper (x := 2^j) (k := j) rfl (by positivity) P (by
    intro p hp
    obtain ⟨pr,lo,hi⟩ := members p hp
    exact ⟨lt_of_le_of_ne lo (fun e => composite (e ▸ pr)),by simpa [pow_succ, Nat.mul_comm] using hi,pr⟩)
  exact (Nat.le_div_iff_mul_le (by omega : 0 < j)).mpr (by simpa [pow_succ, Nat.mul_comm] using bound)

/-- Count each occupied bin with its actual cardinality. Bins omitted from the
certificate may contain points if their charge is zero. -/
private theorem grouped {α ι : Type*} [DecidableEq ι] (P : Finset α) (I : Finset ι)
    (tag : α → ι) (w cap : ι → ℝ) (nonneg : ∀ i ∈ I, 0 ≤ w i)
    (outside : ∀ p ∈ P, tag p ∉ I → w (tag p) = 0)
    (room : ∀ i ∈ I, ((P.filter (fun p => tag p = i)).card : ℝ) ≤ cap i) :
    ∑ p ∈ P, w (tag p) ≤ ∑ i ∈ I, cap i * w i := by
  classical
  let Q := P.filter (fun p => tag p ∈ I)
  have eq : ∑ p ∈ Q, w (tag p) = ∑ p ∈ P, w (tag p) := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro p hp hq
    exact outside p hp (fun hi => hq (Finset.mem_filter.mpr ⟨hp,hi⟩))
  rw [← eq, ← Finset.sum_fiberwise_of_maps_to (fun _ h => (Finset.mem_filter.mp h).2 :
    ∀ p ∈ Q, tag p ∈ I)]
  apply Finset.sum_le_sum
  intro i hi
  have cell : Q.filter (fun p => tag p = i) = P.filter (fun p => tag p = i) := by
    ext p
    simp only [Q,Finset.mem_filter]
    exact ⟨fun ⟨⟨h,_⟩,e⟩ => ⟨h,e⟩,fun ⟨h,e⟩ => ⟨⟨h,e ▸ hi⟩,e⟩⟩
  rw [cell]
  calc
    ∑ p ∈ P.filter (fun p => tag p = i), w (tag p) = ∑ _p ∈ P.filter (fun p => tag p = i), w i :=
      Finset.sum_congr rfl (fun p hp => congrArg w (Finset.mem_filter.mp hp).2)
    _ ≤ cap i * w i := by
      simpa only [Finset.sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right (room i hi) (nonneg i hi)

/-- Nonnegative bit and octave prices bound the total gain on any finite
support P. The tails can be arbitrarily large if their net gain is nonpositive.
All cap and price values may in particular be rational. -/
theorem finite_dual {α ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : Finset α) (I : Finset ι) (J : Finset κ) (tag : α → ι) (oct : ι → κ)
    (gain : α → ℝ) (upper price cap : ι → ℝ) (octCap μ : κ → ℝ) (rate B : ℝ)
    (rateNonneg : 0 ≤ rate) (μpos : ∀ j ∈ J, 0 ≤ μ j)
    (majorizes : ∀ p ∈ P, gain p ≤ upper (tag p))
    (bits : ∑ p ∈ P, price (tag p) ≤ B)
    (rooms : ∀ i ∈ I, ((P.filter (fun p => tag p = i)).card : ℝ) ≤ cap i)
    (octRooms : ∀ j ∈ J, ((P.filter (fun p => oct (tag p) = j)).card : ℝ) ≤ octCap j)
    (tail : ∀ p ∈ P, tag p ∉ I → upper (tag p) ≤ rate * price (tag p) + μ (oct (tag p)))
    (tailOct : ∀ p ∈ P, oct (tag p) ∉ J → μ (oct (tag p)) = 0) :
    ∑ p ∈ P, gain p ≤ rate * B + (∑ j ∈ J, octCap j * μ j) +
      ∑ i ∈ I, cap i * max 0 (upper i - rate * price i - μ (oct i)) := by
  let extra i := max 0 (upper i - rate * price i - μ (oct i))
  have bonus := grouped P I tag extra cap (fun _ _ => le_max_left ..) (by
    intro p hp missing
    exact max_eq_left (by linarith only [tail p hp missing])) rooms
  have octave := grouped P J (fun p => oct (tag p)) μ octCap μpos tailOct octRooms
  calc
    ∑ p ∈ P, gain p ≤ ∑ p ∈ P, (rate * price (tag p) + μ (oct (tag p)) + extra (tag p)) := by
      apply Finset.sum_le_sum
      intro p hp
      have upperExtra : upper (tag p) - rate * price (tag p) - μ (oct (tag p)) ≤ extra (tag p) := le_max_right ..
      linarith only [majorizes p hp,upperExtra]
    _ ≤ _ := by
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left bits rateNonneg) octave) bonus

/-- A single integer-power comparison checks a scaled reward for an entire
segment of primes starting at `lo`. In the finite calculation den = 64 and
scale = 2^80. Minimality of the supplied upper numerator is unnecessary. -/
theorem quantized_gain {lo p scale u a den : ℕ} (loPos : 0 < lo) (start : lo ≤ p)
    (denPos : 0 < den) (scalePos : 0 < scale) (rounded : scale^den ≤ u^den * lo^a) :
    (p : ℝ)^(-((a : ℝ) / den)) ≤ (u : ℝ) / scale := by
  have pl : (0 : ℝ) < lo := by exact_mod_cast loPos
  have pd : (0 : ℝ) < den := by exact_mod_cast denPos
  have ps : (0 : ℝ) < scale := by exact_mod_cast scalePos
  have pw : (0 : ℝ) < (lo : ℝ)^((a : ℝ) / den) := Real.rpow_pos_of_pos pl _
  calc
    (p : ℝ)^(-((a : ℝ) / den)) ≤ (lo : ℝ)^(-((a : ℝ) / den)) :=
      Real.rpow_le_rpow_of_nonpos pl (by exact_mod_cast start) (neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg a) pd.le))
    _ ≤ _ := by
      rw [Real.rpow_neg pl.le]
      apply (le_div_iff₀ ps).mpr
      rw [inv_mul_eq_div]
      apply (div_le_iff₀ pw).mpr
      apply (pow_le_pow_iff_left₀ ps.le (mul_nonneg (Nat.cast_nonneg _) pw.le) denPos.ne').mp
      rw [mul_pow, ← Real.rpow_mul_natCast pl.le, div_mul_cancel₀ _ pd.ne', Real.rpow_natCast]
      exact_mod_cast rounded

/-- The measured finite gain bounds a real Euler product with no truncation
of the logarithm. An upper bound C on the sum gives a base-two exponent 1.443 C. -/
theorem euler_correction (P : Finset ℕ) (θ C : ℝ)
    (budget : ∑ p ∈ P, (p : ℝ)^(-θ) ≤ C) :
    ∏ p ∈ P, (1 + (p : ℝ)^(-θ)) ≤ (2 : ℝ)^((1443/1000 : ℝ) * C) := by
  have nonneg : 0 ≤ C := (Finset.sum_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)).trans budget
  have conversion : (1:ℝ) ≤ (1443/1000 : ℝ) * Real.log 2 := by linarith only [Real.log_two_gt_d9]
  calc
    ∏ p ∈ P, (1 + (p : ℝ)^(-θ)) ≤ ∏ p ∈ P, Real.exp ((p : ℝ)^(-θ)) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      exact fun p _ => by simpa only [add_comm] using Real.add_one_le_exp ((p : ℝ)^(-θ))
    _ = Real.exp (∑ p ∈ P, (p : ℝ)^(-θ)) := (Real.exp_sum ..).symm
    _ ≤ _ := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
      apply Real.exp_le_exp.mpr
      exact budget.trans (by nlinarith only [mul_le_mul_of_nonneg_right conversion nonneg])

/-- Apply a dual objective in scaled integer reward units directly to the Euler
product. The only rounding condition is that each integer reward majorizes its
prime's true reward, as supplied e.g. by `quantized_gain`. -/
theorem fixed_point_euler (P : Finset ℕ) (θ objective : ℝ) (scale : ℕ) (u : ℕ → ℕ)
    (positive : 0 < scale) (majorant : ∀ p ∈ P, (p : ℝ)^(-θ) ≤ (u p : ℝ) / scale)
    (bound : ∑ p ∈ P, (u p : ℝ) ≤ objective) :
    ∏ p ∈ P, (1 + (p : ℝ)^(-θ)) ≤ (2 : ℝ)^((1443/1000 : ℝ) * (objective / scale)) := by
  apply euler_correction
  calc
    ∑ p ∈ P, (p : ℝ)^(-θ) ≤ ∑ p ∈ P, (u p : ℝ) / scale := Finset.sum_le_sum majorant
    _ = (∑ p ∈ P, (u p : ℝ)) / scale := by rw [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right bound (by exact_mod_cast positive.le)

end PrimeFactors.WeightedPrimeBudget
