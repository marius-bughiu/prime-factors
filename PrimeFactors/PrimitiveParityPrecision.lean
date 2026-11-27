import PrimeFactors.PrimitiveParityAverages
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Sensitivity of the normalized even-character mean when its short-support
formula is D + 2(C-D)/U. The estimates are uniform in the complex coefficients
and scale with their total squared norm. -/

namespace PrimeFactors.PrimitiveParityPrecision

open Finset
open scoped ComplexConjugate
set_option exponentiation.threshold 8192
variable {ι : Type*}

/-- Total squared norm of the coefficients on the indicated finite support. -/
noncomputable def energy (I : Finset ι) (a : ι → ℂ) : ℝ := ∑ i ∈ I, ‖a i‖^2

/-- Squared norm after adding all the coefficients. -/
noncomputable def coherent (I : Finset ι) (a : ι → ℂ) : ℝ := ‖∑ i ∈ I, a i‖^2

/-- The real expression obtained from the short-support even-character identity. -/
noncomputable def mean (C D U : ℝ) := D+2*(C-D)/U

/-- Casts identify the real expression with the complex products occurring
in the character average. In the polynomial identity I is the full index set. -/
theorem cast_mean (I : Finset ι) (a : ι → ℂ) (U : ℝ) :
    (mean (coherent I a) (energy I a) U : ℂ) =
      (∑ i ∈ I, a i*conj (a i)) +
        2*((∑ i ∈ I, a i)*conj (∑ i ∈ I, a i) - ∑ i ∈ I, a i*conj (a i))/(U:ℂ) := by
  simp only [mean,coherent,energy,Complex.mul_conj,Complex.normSq_eq_norm_sq,
    Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_sub,
    Complex.ofReal_sum,Complex.ofReal_ofNat]

theorem energy_nonneg (I : Finset ι) (a : ι → ℂ) : 0≤energy I a :=
  sum_nonneg fun i _ => sq_nonneg ‖a i‖

/-- Cauchy-Schwarz gives a support-size bound for arbitrary phases and magnitudes. -/
theorem coherent_le (I : Finset ι) (a : ι → ℂ) : coherent I a ≤ I.card*energy I a := calc
  _ ≤ (∑ i ∈ I, ‖a i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le I a) 2
  _ ≤ _ := sq_sum_le_card_mul_sum_sq

theorem deviation (I : Finset ι) (a : ι → ℂ) :
    |coherent I a-energy I a| ≤ max (1:ℝ) (I.card-1)*energy I a := by
  have D := energy_nonneg I a
  have C : 0≤coherent I a := sq_nonneg _
  have above := coherent_le I a
  have left := mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) (I.card-1)) D
  have right := mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (I.card-1)) D
  exact abs_le.mpr ⟨by linarith only [left,C],by linarith only [above,right]⟩

/-- Constant weights attain the Cauchy-Schwarz upper bound on every support.
At support size at least two they attain the positive endpoint of the deviation bound. -/
theorem flat (I : Finset ι) (z : ℂ) :
    coherent I (fun _ => z) = I.card*energy I (fun _ => z) ∧
    coherent I (fun _ => z)-energy I (fun _ => z) = ((I.card:ℝ)-1)*energy I (fun _ => z) := by
  have eq : coherent I (fun _ => z)=I.card*energy I (fun _ => z) := by
    simp [coherent,energy,nsmul_eq_mul,norm_mul]
    ring
  exact ⟨eq,by rw [eq]; ring⟩

/-- Exact bias and exact change under an eight-unit increase in U. -/
theorem exact_change (C D : ℝ) {U : ℝ} (up : 0<U) :
    |mean C D U-D|=2*|C-D|/U ∧
    |mean C D U-mean C D (U+8)|=16*|C-D|/(U*(U+8)) := by
  have vp : 0<U+8 := by linarith
  have diff : mean C D U-mean C D (U+8)=16*(C-D)/(U*(U+8)) := by
    unfold mean
    field_simp
    ring
  constructor
  · rw [mean,add_sub_cancel_left,abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos up]
  · rw [diff,abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<16),abs_of_pos (mul_pos up vp)]

/-- For every coefficient vector on at most 2^21 indices, changing U by eight
changes the specified mean by at most D/2^4067 when U is at least 2^2046.
The single-mean bias from the diagonal energy is at most D/2^2024. -/
theorem full_size (I : Finset ι) (a : ι → ℂ) {U : ℝ}
    (small : I.card≤2^21) (large : (2:ℝ)^2046≤U) :
    |mean (coherent I a) (energy I a) U-energy I a| ≤ energy I a/2^2024 ∧
    |mean (coherent I a) (energy I a) U-mean (coherent I a) (energy I a) (U+8)| ≤
      energy I a/2^4067 := by
  let C := coherent I a
  let D := energy I a
  have dn : 0≤D := energy_nonneg I a
  have up : 0<U := (by positivity : (0:ℝ)<2^2046).trans_le large
  have u8 : 0<U+8 := by linarith
  have card : (I.card:ℝ)≤2^21 := by exact_mod_cast small
  have bound : max (1:ℝ) (I.card-1)≤2^21 := max_le (by norm_num) (by linarith)
  have coeff : |C-D|≤2^21*D := (deviation I a).trans (mul_le_mul_of_nonneg_right bound dn)
  change |mean C D U-D|≤D/2^2024 ∧ |mean C D U-mean C D (U+8)|≤D/2^4067
  rw [(exact_change C D up).1,(exact_change C D up).2]
  constructor
  · apply (div_le_div_iff₀ up (by positivity : (0:ℝ)<2^2024)).mpr
    calc
      _ ≤ 2*(2^21*D)*2^2024 := by gcongr
      _ = D*2^2046 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left large dn
  · apply (div_le_div_iff₀ (mul_pos up u8) (by positivity : (0:ℝ)<2^4067)).mpr
    have product := mul_le_mul large (show 2^2046≤U+8 by linarith)
      (by positivity : (0:ℝ)≤2^2046) up.le
    calc
      _ ≤ 16*(2^21*D)*2^4067 := by gcongr
      _ = D*(2^2046*2^2046) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left product dn

/-- For factors at least seven, the actual normalizer (p-2)(q-2)+1 is at
least half their product. A 2048-bit product thus meets the lower size
hypothesis in the sensitivity estimate. -/
theorem normalizer_lower {p q : ℕ} (hp : 7≤p) (hq : 7≤q) :
    p*q ≤ 2*((p-2)*(q-2)+1) := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hq
  rw [show 7+i-2=5+i by omega,show 7+j-2=5+j by omega]
  nlinarith only [Nat.zero_le i,Nat.zero_le j,Nat.zero_le (i*j)]

theorem full_normalizer {p q : ℕ} (hp : 7≤p) (hq : 7≤q) (full : 2^2047≤p*q) :
    2^2046≤(p-2)*(q-2)+1 := by
  have bound := full.trans (normalizer_lower hp hq)
  rw [show (2:ℕ)^2047=2*2^2046 by decide +kernel] at bound
  omega

/-- Direct specialization to the normalized even-family average. The second
term compares the actual mean with the hypothetical denominator U+8 at
the same coefficients. -/
theorem normalized_even {ι : Type*} [Fintype ι] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 7≤p) (hq : 7≤q) (full : 2^2047≤p*q) (n : ι → ℕ) (a : ι → ℂ)
    (small : Fintype.card ι≤2^21) (distinct : Function.Injective n) (pos : ∀ i, 0<n i)
    (pbound : ∀ i j, n i+n j<p) (qbound : ∀ i j, n i+n j<q) :
    let U : ℝ := (PrimitiveParityAverages.T p q:ℝ)+1
    let measured := (PrimitiveParityAverages.average p q true (PrimitiveParityAverages.squareValue n a)).re
    |measured-energy univ a|≤energy univ a/2^2024 ∧
    |measured-mean (coherent univ a) (energy univ a) (U+8)|≤energy univ a/2^4067 := by
  classical
  let T := PrimitiveParityAverages.T p q
  let U : ℝ := (T:ℝ)+1
  have lower : 2^2046≤T+1 := full_normalizer hp hq full
  have big : (2:ℝ)^2046≤U := by dsimp [U]; exact_mod_cast lower
  have many : 1<T := by omega
  have formula := (PrimitiveParityAverages.polynomial_means (by omega : 2<p) (by omega : 2<q)
    many n a distinct pos pbound qbound).1
  have cast : (U:ℂ)=(T:ℂ)+1 := by simp [U]
  have eq : PrimitiveParityAverages.average p q true (PrimitiveParityAverages.squareValue n a) =
      (mean (coherent univ a) (energy univ a) U : ℂ) := by
    rw [formula,cast_mean,cast]
    rfl
  have bound := full_size univ a (by simpa using small) big
  simpa only [eq,Complex.ofReal_re] using bound

end PrimeFactors.PrimitiveParityPrecision
