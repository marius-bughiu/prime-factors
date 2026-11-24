import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

namespace PrimeFactors

/-- Base-two logarithm of the exact wide-sieve cutoff when the base-two
logarithm of the input is b. All logs inside the correction are natural. -/
noncomputable def wideScaleLog (b : ℝ) : ℝ :=
  b/5 - (2*Real.log (4/3)/25)*b/Real.log (b*Real.log 2)

/-- Uniform finite bounds on the logarithmic cutoff over the entire input width. -/
theorem wideScaleLog_2048 {b : ℝ} (lo : 2047≤b) (hi : b<2048) :
    400 < wideScaleLog b ∧ wideScaleLog b < 406 := by
  have logLo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<4/3)
  have logHi := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4/3)
  norm_num at logLo logHi
  let c := 2*Real.log (4/3)/25
  have cl : (1:ℝ)/50≤c := by dsimp [c]; linarith
  have cu : c≤(2:ℝ)/75 := by dsimp [c]; linarith
  have twoLo : (3:ℝ)/5<Real.log 2 := by linarith [Real.log_two_gt_d9]
  have twoHi : Real.log 2 < (3:ℝ)/4 := by linarith [Real.log_two_lt_d9]
  have Llo : (2:ℝ)^10 < b*Real.log 2 := by
    have h := mul_lt_mul_of_pos_left twoLo (show 0<b by linarith)
    nlinarith
  have Lhi : b*Real.log 2 < (2:ℝ)^11 := by
    have h := mul_lt_mul_of_pos_left twoHi (show 0<b by linarith)
    nlinarith
  have ll := Real.log_lt_log (by norm_num : 0<(2:ℝ)^10) Llo
  have lu := Real.log_lt_log (lt_trans (by norm_num) Llo) Lhi
  rw [Real.log_pow] at ll lu
  norm_num at ll lu
  let d := Real.log (b*Real.log 2)
  have dl : 6<d := by dsimp [d]; linarith
  have du : d<9 := by dsimp [d]; linarith
  have bpos : 0≤b := by linarith
  have corrLo : (1/50:ℝ)*2047/9 < c*b/d := by
    apply (lt_div_iff₀ (show 0<d by linarith)).mpr
    have h := mul_le_mul_of_nonneg_right cl bpos
    nlinarith
  have corrHi : c*b/d < (2/75:ℝ)*2048/6 := by
    apply (div_lt_iff₀ (show 0<d by linarith)).mpr
    have h := mul_le_mul_of_nonneg_right cu bpos
    nlinarith
  change 400 < b/5-c*b/d ∧ b/5-c*b/d < 406
  constructor <;> linarith

/-- The totient can be evaluated on the small known prime list rather than
by looping over all residues of the primorial. -/
theorem wideScale_totient_primorial (n : ℕ) :
    (primorial n).totient =
      ∏ p ∈ (Finset.range (n+1)).filter Nat.Prime, (p-1) := by
  have primes : (primorial n).primeFactors = (Finset.range (n+1)).filter Nat.Prime :=
    Nat.primeFactors_prod (fun _ hp => (Finset.mem_filter.mp hp).2)
  rw [Nat.totient_eq_div_primeFactors_mul, primes]
  change (primorial n / primorial n) * _ = _
  rw [Nat.div_self (primorial_pos n), one_mul]

set_option maxRecDepth 10000 in
/-- The explicit prime list has 62 entries. Their predecessor product gives
the exact number of rows in the complete residue sweep. -/
theorem wideScale_exact_rows :
    ((Finset.range 294).filter Nat.Prime).card = 62 ∧
    (primorial 293).totient =
      199183810352246363281298161307406241615727304265109178959521185026814655750567809261101820844588400640000000000000000000 := by
  rw [wideScale_totient_primorial]
  decide +kernel

set_option maxRecDepth 10000 in
/-- Kernel-checked bookends, unchanged intervening primorial, and row count. -/
theorem wideScale_primorial_checks :
    primorial 293 < 2^400 ∧ primorial 306 = primorial 293 ∧
    2^406 < primorial 307 ∧ 2^396 < (primorial 293).totient := by
  rw [wideScale_totient_primorial]
  decide +kernel

private theorem wideScale_primorial_mono : Monotone primorial := by
  intro i j hij
  apply Nat.le_of_dvd (primorial_pos j)
  apply Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p)
  exact Finset.filter_subset_filter _ (Finset.range_mono (by omega))

/-- Any cutoff in the certified interval selects exactly the primorial 293#.
The second conjunct ranges over every alternative primorial. -/
theorem wideScale_largest {C : ℝ} (lo : (2:ℝ)^400<C) (hi : C<(2:ℝ)^406) :
    (primorial 293 : ℝ)<C ∧ ∀ n : ℕ, (primorial n : ℝ)≤C → primorial n≤primorial 293 := by
  obtain ⟨small, same, large, _⟩ := wideScale_primorial_checks
  constructor
  · exact lt_trans (by exact_mod_cast small) lo
  · intro n permissible
    by_cases h : n<307
    · exact (wideScale_primorial_mono (show n≤306 by omega)).trans_eq same
    · have above := wideScale_primorial_mono (show 307≤n by omega)
      have bump : (2:ℝ)^406 < primorial n := by exact_mod_cast large.trans_le above
      linarith

/-- Unrounded primorial cutoff used by the wide-modulus sieve. -/
noncomputable def wideScaleCutoff (N : ℝ) : ℝ :=
  N^(1/5:ℝ) * Real.exp (-(2*Real.log (4/3)/25)*(Real.log N/Real.log (Real.log N)))

private theorem wideScaleCutoff_eq {N : ℝ} (hN : 0<N) :
    wideScaleCutoff N = (2:ℝ)^wideScaleLog (Real.log N/Real.log 2) := by
  let b := Real.log N/Real.log 2
  have logTwo := Real.log_pos (by norm_num : (1:ℝ)<2)
  have eq : b*Real.log 2 = Real.log N := div_mul_cancel₀ _ logTwo.ne'
  change wideScaleCutoff N = (2:ℝ)^wideScaleLog b
  rw [wideScaleCutoff, Real.rpow_def_of_pos hN, ← Real.exp_add,
    Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2), wideScaleLog, eq]
  apply congrArg Real.exp
  linear_combination (1/5 - (2*Real.log (4/3)/25)/Real.log (Real.log N))*eq.symm

/-- For every 2048-bit integer, the largest eligible primorial in the exact
schedule is 293#. Its full set of unit rows contains more than 2^396 entries. -/
theorem wideScale_2048 {N : ℕ} (lo : 2^2047≤N) (hi : N<2^2048) :
    (primorial 293 : ℝ)<wideScaleCutoff N ∧
    (∀ n : ℕ, (primorial n : ℝ)≤wideScaleCutoff N → primorial n≤primorial 293) ∧
    2^396 < ((Finset.range (primorial 293)).filter (primorial 293).Coprime).card := by
  have L : (2:ℝ)^2047≤N := by exact_mod_cast lo
  have U : (N:ℝ)<2^2048 := by exact_mod_cast hi
  have Npos : (0:ℝ)<N := (by positivity : (0:ℝ)<2^2047).trans_le L
  have lower := Real.log_le_log (by positivity : (0:ℝ)<2^2047) L
  have upper := Real.log_lt_log Npos U
  rw [Real.log_pow] at lower upper
  have logTwo := Real.log_pos (by norm_num : (1:ℝ)<2)
  have bits := wideScaleLog_2048 ((le_div_iff₀ logTwo).mpr (by exact_mod_cast lower))
    ((div_lt_iff₀ logTwo).mpr (by exact_mod_cast upper))
  have below := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) bits.1
  have above := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) bits.2
  rw [← wideScaleCutoff_eq Npos] at below above
  have choice := wideScale_largest (by simpa only [← Real.rpow_natCast] using below)
    (by simpa only [← Real.rpow_natCast] using above)
  exact ⟨choice.1, choice.2, wideScale_primorial_checks.2.2.2⟩

end PrimeFactors
