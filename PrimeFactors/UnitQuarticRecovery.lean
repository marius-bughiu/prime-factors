import PrimeFactors.GapPolynomialScale
import PrimeFactors.QuarticUnitLabels
import PrimeFactors.UnitQuarticBox
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace PrimeFactors.UnitQuarticRecovery
open QuarticFactorLane

/-- Coefficients of 1, x-y, x, (x-y)^2-2s^2 and x(x-y) in the original trace. -/
noncomputable def inFactorCoordinates (N s : ℤ) (v : Fin 5 → ℤ) : Weights where
  a := v 1 + v 2
  b := -v 1
  c := v 3 + v 4
  d := v 3
  e := v 0 - 2*(N+s^2)*v 3 - N*v 4

private abbrev widths := UnitQuarticBox.weight

private noncomputable def terms (x y s : ℤ) : Fin 5 → ℤ :=
  ![1, x-y, x, (x-y)^2-2*s^2, x*(x-y)]

theorem gap_trace {x y N : ℤ} (pair : x*y=N) (s : ℤ) (v : Fin 5 → ℤ) :
    trace (inFactorCoordinates N s v) x y = ∑ i, v i * terms x y s i := by
  rw [← pair]
  simp [trace, inFactorCoordinates, terms, Fin.sum_univ_succ]
  ring

theorem different_coordinates {p q : Fin 5 → ℤ} (ne : p ≠ q) (N s : ℤ) :
    let w := inFactorCoordinates N s (p-q)
    w.a ≠ 0 ∨ w.b ≠ 0 ∨ w.c ≠ 0 ∨ w.d ≠ 0 ∨ w.e ≠ 0 := by
  dsimp only
  by_contra! h
  obtain ⟨ha,hb,hc,hd,he⟩ := h
  simp [inFactorCoordinates] at ha hb hc hd he
  apply ne
  funext i
  fin_cases i <;> simp_all <;> omega

theorem value_sub (p q : Fin 5 → ℤ) (N s x : ℤ) :
    value (inFactorCoordinates N s (p-q)) N x =
    value (inFactorCoordinates N s p) N x - value (inFactorCoordinates N s q) N x := by
  simp [value, inFactorCoordinates]
  ring

private theorem bounds {x y : ℤ} {s B : ℕ} (hgap : |x-y|≤2*(s:ℤ)) (hx : |x|≤B) :
    ∀ i, |terms x y s i| ≤ (widths s B i : ℤ) := by
  have sq : (x-y)^2 ≤ (2*(s:ℤ))^2 := by
    rw [← sq_abs (x-y), pow_two, pow_two]
    exact mul_self_le_mul_self (abs_nonneg _) hgap
  have quadratic : |(x-y)^2-2*(s:ℤ)^2|≤2*(s:ℤ)^2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x-y)]
  have product : |x*(x-y)|≤2*(B:ℤ)*s := by
    rw [abs_mul]
    calc _ ≤ (B:ℤ)*(2*s) := mul_le_mul hx hgap (abs_nonneg _) (by positivity)
         _ = _ := by ring
  intro i
  fin_cases i <;> simp [terms,widths,UnitQuarticBox.weight] <;> assumption

theorem trace_bound (v : Fin 5 → ℤ) {x y N : ℤ} {s B : ℕ}
    (pair : x*y=N) (gap : |x-y| ≤ 2*(s:ℤ)) (hx : |x| ≤ B) :
    |trace (inFactorCoordinates N s v) x y| ≤ ∑ i, |v i| *(widths s B i : ℤ) := by
  rw [gap_trace pair]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (bounds gap hx i) (abs_nonneg _)

theorem factor_limits {x y N : ℕ} (mul : x*y=N) (hxy : x≤2*y) (hyx : y≤2*x)
    (hxOdd : Odd x) (hyOdd : Odd y) :
    |(x:ℤ)-y| ≤ 2*((N/8).sqrt : ℤ) ∧ |(x:ℤ)| ≤ ((2*N).sqrt : ℤ) := by
  obtain ⟨a,ha⟩ := hxOdd
  obtain ⟨b,hb⟩ := hyOdd
  have even : (x:ℤ)-y=2*((a:ℤ)-b) := by rw [ha,hb]; push_cast; ring
  have small := GapPolynomialScale.even_gap_radius (by exact_mod_cast mul)
    (by exact_mod_cast hxy) (by exact_mod_cast hyx) even
  have g : |(a:ℤ)-b| ≤ ((N/8).sqrt : ℤ) := by
    simpa only [Int.natCast_natAbs] using (show ((((a:ℤ)-b).natAbs:ℕ):ℤ) ≤ _ by
      exact_mod_cast small)
  have lim : x ≤ (2*N).sqrt := Nat.le_sqrt'.mpr (by nlinarith [Nat.mul_le_mul_left x hxy])
  constructor
  · rw [even, abs_mul]
    simpa using mul_le_mul_of_nonneg_left g (show (0:ℤ)≤2 by decide)
  · simpa using (show (x:ℤ) ≤ ((2*N).sqrt : ℤ) by exact_mod_cast lim)

set_option exponentiation.threshold 4096 in
private theorem modulus_unit {x : ℕ} (unit : x.Coprime 30) :
    IsCoprime (360*((2:ℤ)^614)^4) (x:ℤ) := by
  have c : (360:ℕ).Coprime x :=
    (unit.symm.pow_left 3).of_dvd_left (by decide : 360 ∣ 30^3)
  have d : (2:ℕ).Coprime x := unit.symm.of_dvd_left (by decide : 2 ∣ 30)
  have whole : (360*((2:ℕ)^614)^4).Coprime x := Nat.coprime_mul_iff_left.mpr ⟨c,(d.pow_left 614).pow_left 4⟩
  exact_mod_cast whole.isCoprime

private theorem scale_limits {N : ℕ} (large : 8≤N) (size : N<2^2048) :
    0 < (N/8).sqrt ∧ 0 < (2*N).sqrt ∧
    (N/8).sqrt^2 ≤ 2^2045 ∧ (2*N).sqrt^2 ≤ 2^2049 := by
  have s : 1 ≤ (N/8).sqrt := Nat.le_sqrt'.mpr (by
    rw [one_pow]
    exact (Nat.le_div_iff_mul_le (by decide : 0<8)).mpr (by omega))
  have b : 1 ≤ (2*N).sqrt := Nat.le_sqrt'.mpr (by rw [one_pow]; omega)
  refine ⟨s,b,(Nat.le_sqrt'.mp le_rfl).trans ?_,(Nat.le_sqrt'.mp le_rfl).trans ?_⟩
  · have hs : N/8 < 2^2045 := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by
      rwa [show (2:ℕ)^2045*8=2^2048 by decide +kernel])
    exact hs.le
  · linarith only [size, show (2:ℕ)^2049=2*2^2048 by decide +kernel]

set_option exponentiation.threshold 4096 in
/-- The same coefficient difference works for both signs. The finite set contains
the signed coordinates of every balanced pair in this lane. -/
private theorem recovery {N : ℕ} (pos : 8≤N) (cop : N.Coprime 30) (u : ℤ)
    (p q : Fin 5 → ℤ) (ne : p≠q)
    (short : ∑ i, |p i - q i| * (widths (N/8).sqrt (2*N).sqrt i : ℤ) <
      360*((2:ℤ)^614)^4)
    (labels : ∀ z : ℤ, z ≡ u [ZMOD (2:ℤ)^614] → IsCoprime z 30 →
      360*((2:ℤ)^614)^4 ∣ value (inFactorCoordinates N (N/8).sqrt p) N z -
        value (inFactorCoordinates N (N/8).sqrt q) N z) :
    let S := candidates (inFactorCoordinates N (N/8).sqrt (p-q)) N
    S.card≤4 ∧ ∀ x y : ℕ, x*y=N → x≤2*y → y≤2*x →
      ((x:ℤ) ≡ u [ZMOD (2:ℤ)^614] → (x:ℤ) ∈ S) ∧
      (-(x:ℤ) ≡ u [ZMOD (2:ℤ)^614] → -(x:ℤ) ∈ S) := by
  let s := (N/8).sqrt
  let B := (2*N).sqrt
  let w := inFactorCoordinates N s (p-q)
  have nz := different_coordinates ne (N:ℤ) (s:ℤ)
  have covers {a b : ℤ} (pair : a*b=N) (unit : IsCoprime a 30)
      (full : IsCoprime (360*((2:ℤ)^614)^4) a)
      (gap : |a-b| ≤ 2*(s:ℤ)) (cap : |a| ≤ (B:ℤ)) (lane : a ≡ u [ZMOD (2:ℤ)^614]) :
      a ∈ candidates w N := by
    have div := labels a lane unit
    rw [← value_sub, pair_identity _ pair] at div
    have small := (trace_bound (p-q) pair gap cap).trans_lt short
    have zero : trace w a b=0 := Int.eq_zero_of_abs_lt_dvd
      (full.pow_right.dvd_of_dvd_mul_left div) small
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots (polynomial_nonzero (by exact_mod_cast (show N≠0 by omega)) nz)).mpr
    rw [Polynomial.IsRoot, eval_polynomial, pair_identity _ pair,zero,mul_zero]
  refine ⟨candidates_card .., ?_⟩
  intro x y mul xy yx
  have xc : x.Coprime 30 := cop.of_dvd_left ⟨y,mul.symm⟩
  have yc : y.Coprime 30 := cop.of_dvd_left ⟨x,by rw [Nat.mul_comm]; exact mul.symm⟩
  have unit : IsCoprime (x:ℤ) 30 := by exact_mod_cast xc.isCoprime
  have limits := factor_limits mul xy yx
    (Nat.coprime_two_right.mp (xc.of_dvd_right (by decide)))
    (Nat.coprime_two_right.mp (yc.of_dvd_right (by decide)))
  have prod : (x:ℤ)*(y:ℤ)=N := by exact_mod_cast mul
  constructor
  · exact covers prod unit (modulus_unit xc) limits.1 limits.2
  · intro lane
    refine covers (a := -(x:ℤ)) (b := -(y:ℤ)) ?_ ?_ ?_ ?_ ?_ lane
    · simpa using prod
    · exact unit.neg_left
    · exact (modulus_unit xc).neg_right
    · rw [show -(x:ℤ) - -(y:ℤ) = -((x:ℤ)-y) by ring, abs_neg]
      exact limits.1
    · simpa using limits.2

/-- For every proposed remainder modulo 2^614, at most four signed integers
contain every balanced factor in that lane. The product and the remainder determine
the set. The proof uses a finite box collision and no lattice-reduction assumption. -/
theorem every_2048_lane (N : ℕ) (large : 8≤N) (size : N<2^2048) (unit : N.Coprime 30)
    (u : ℤ) : ∃ v : Fin 5 → ℤ, v≠0 ∧
    (∑ i, |v i| * (UnitQuarticBox.weight (N/8).sqrt (2*N).sqrt i : ℤ)) <
      360*((2:ℤ)^614)^4 ∧
    let w := inFactorCoordinates N (N/8).sqrt v
    let S := candidates w N
    (∀ z : ℤ, z ≡ u [ZMOD (2:ℤ)^614] → IsCoprime z 30 →
      360*((2:ℤ)^614)^4 ∣ value w N z) ∧
    S.card≤4 ∧ ∀ x y : ℕ, x*y=N → x≤2*y → y≤2*x →
      ((x:ℤ) ≡ u [ZMOD (2:ℤ)^614] → (x:ℤ) ∈ S) ∧
      (-(x:ℤ) ≡ u [ZMOD (2:ℤ)^614] → -(x:ℤ) ∈ S) := by
  obtain ⟨hs,hB,hs2,hB2⟩ := scale_limits large size
  let label (v : Fin 5 → ℤ) :=
    QuarticUnitLabels.label (2^614) u N (inFactorCoordinates N (N/8).sqrt v)
  obtain ⟨p,q,ne,same,short⟩ := UnitQuarticBox.collision_2048_of_card hs hB hs2 hB2
    (QuarticUnitLabels.card_labels ((2:ℕ)^614)).le label
  have valid := fun (z : ℤ) (lane : z ≡ u [ZMOD (2:ℤ)^614]) (cop : IsCoprime z 30) =>
    QuarticUnitLabels.divides_of_label_eq same lane cop
  refine ⟨p-q, sub_ne_zero.mpr ne, short, ?_, recovery large unit u p q ne short valid⟩
  intro z lane cop
  rw [value_sub]
  exact valid z lane cop

end PrimeFactors.UnitQuarticRecovery
