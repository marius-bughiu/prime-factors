import PrimeFactors.HasseHankelBilinear
import Mathlib.Algebra.Polynomial.Roots

/-! Polynomial root counts for the two public Hasse Hankel minors at a shift
and its successor. The cubic coefficients and both homogeneous residuals share
their integer definitions with the universal determinant calculation. -/
namespace PrimeFactors.HankelProbePolynomial

open Polynomial Finset HasseHankelBilinear HankelTranslation

noncomputable section
variable {K : Type*} [Field K]

private noncomputable def quadratic : K[X] := 3*X^2-1
private noncomputable def cubic : K[X] := X^3-X

/-- The two residual tests use the primitive degree-six and degree-ten
obstructions, made homogeneous before substituting C² and B³. -/
noncomputable def residualZero : K[X] := homZero (cubic^2) (quadratic^3)
noncomputable def residualOne : K[X] := homOne (cubic^2) (quadratic^3)

noncomputable def probe : K[X] := quadratic*cubic*residualZero*residualOne

theorem residual_zero_degree : (residualZero : K[X]).natDegree ≤ 36 := by
  unfold residualZero homZero cubic quadratic
  compute_degree

theorem residual_one_degree : (residualOne : K[X]).natDegree ≤ 60 := by
  unfold residualOne homOne cubic quadratic
  compute_degree

theorem probe_degree : (probe : K[X]).natDegree ≤ 101 := by
  have qb : (quadratic : K[X]).natDegree≤2 := by unfold quadratic; compute_degree
  have cb : (cubic : K[X]).natDegree≤3 := by unfold cubic; compute_degree
  unfold probe
  have h : (quadratic * cubic : K[X]).natDegree ≤ 5 :=
    natDegree_mul_le.trans (Nat.add_le_add qb cb)
  have h' : (quadratic * cubic * residualZero : K[X]).natDegree ≤ 41 :=
    natDegree_mul_le.trans (Nat.add_le_add h residual_zero_degree)
  exact natDegree_mul_le.trans (Nat.add_le_add h' residual_one_degree)

private theorem eval_zero_res (c : K) : (residualZero : K[X]).eval c =
    homZero ((c^3-c)^2) ((3*c^2-1)^3) := by
  simp [residualZero, homZero, cubic, quadratic]

private theorem eval_one_res (c : K) : (residualOne : K[X]).eval c =
    homOne ((c^3-c)^2) ((3*c^2-1)^3) := by
  simp [residualOne, homOne, cubic, quadratic]

private theorem eval_probe (c : K) : (probe : K[X]).eval c =
    (3*c^2-1)*(c^3-c)*homZero ((c^3-c)^2) ((3*c^2-1)^3)*
      homOne ((c^3-c)^2) ((3*c^2-1)^3) := by
  simp [probe, quadratic, cubic, eval_zero_res, eval_one_res]

/-- Either raw minor vanishing at a shift forces the shared degree-101 probe to vanish. -/
theorem zero_of_raw (c : K) (two : (2:K)≠0)
    (hit : rawMinor (hankel (fun n => TranslatedHasse.value n c)) 0 = 0 ∨
      rawMinor (hankel (fun n => TranslatedHasse.value n c)) 1 = 0) :
    (probe : K[X]).eval c = 0 := by
  rw [show hankel (fun n => TranslatedHasse.value n c) =
      hankel (moment (3*c^2-1) (c^3-c)) from funext (hasse_hankel c),
      raw_zero, raw_one] at hit
  rw [eval_probe]
  simp only [mul_eq_zero, pow_eq_zero_iff (by decide : 4≠0),
    pow_eq_zero_iff (by decide : 8≠0), two, false_or] at hit ⊢
  tauto

private theorem small_ne_zero {p v : ℕ} (large : 2^280 ≤ p)
    (pos : 0<v) (small : v < 2^280) : (v:ZMod p)≠0 :=
  fun h => Nat.not_dvd_of_pos_of_lt pos (small.trans_le large)
    ((ZMod.natCast_zmod_eq_zero_iff_dvd v p).mp h)

set_option exponentiation.threshold 512 in
/-- The two constant shifts in the eight-gcd experiment cannot flag any prime
of at least 2^280. Their combined probe values have 206 and 267 bits. -/
theorem fixed_shifts (p : ℕ) [Fact p.Prime] (large : 2^280 ≤ p) :
    (probe : (ZMod p)[X]).eval 2 ≠ 0 ∧ (probe : (ZMod p)[X]).eval 3 ≠ 0 := by
  have e2 : (probe : (ZMod p)[X]).eval 2 =
      -(69480138368953473119148153704941396846486169660575941918720000 : ZMod p) := by
    rw [eval_probe]
    norm_num [homZero, homOne]
  have e3 : (probe : (ZMod p)[X]).eval 3 =
      -(202411697990455652544378149865838273958411117670048261788899825143030763172659200 : ZMod p) := by
    rw [eval_probe]
    norm_num [homZero, homOne]
  rw [e2,e3]
  constructor <;> apply neg_ne_zero.mpr
  · exact small_ne_zero (v := 69480138368953473119148153704941396846486169660575941918720000) large (by decide) (by decide)
  · exact small_ne_zero (v := 202411697990455652544378149865838273958411117670048261788899825143030763172659200) large (by decide) (by decide)

private theorem eval_at_zero (p : ℕ) [Fact p.Prime] :
    (residualZero : (ZMod p)[X]).eval 0 = -26368 ∧
    (residualOne : (ZMod p)[X]).eval 0 = 7110656 := by
  rw [eval_zero_res,eval_one_res]
  norm_num [homZero,homOne]

set_option exponentiation.threshold 512 in
theorem probe_nonzero (p : ℕ) [Fact p.Prime] (large : 2^280≤p) :
    (probe : (ZMod p)[X])≠0 := by
  have trunc (v : ℕ) (vp : 0<v) (vl : v<2^280) := small_ne_zero large vp vl
  have rz : (residualZero : (ZMod p)[X])≠0 := by
    intro h
    have e := (eval_at_zero p).1
    rw [h, eval_zero] at e
    exact (neg_ne_zero.mpr (trunc 26368 (by decide) (by decide))) e.symm
  have ro : (residualOne : (ZMod p)[X])≠0 := by
    intro h
    have e := (eval_at_zero p).2
    rw [h, eval_zero] at e
    exact trunc 7110656 (by decide) (by decide) e.symm
  have qb : (quadratic : (ZMod p)[X])≠0 := by
    intro h
    have e := congrArg (Polynomial.eval 0) h
    simp [quadratic] at e
  have cb : (cubic : (ZMod p)[X])≠0 := by
    intro h
    have e := congrArg (Polynomial.eval 2) h
    norm_num [cubic] at e
    exact trunc 6 (by decide) (by decide) e
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero qb cb) rz) ro

/-- The two translates are evaluated at r and r+1. -/
noncomputable def residues (p : ℕ) : Finset (ZMod p) := by
  classical
  exact if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    let roots := (probe : (ZMod p)[X]).roots.toFinset
    roots ∪ roots.image (fun x => x-1)
  else ∅

theorem residues_card (p : ℕ) [Fact p.Prime] (_large : 2^280 ≤ p) :
    (residues p).card ≤ 202 := by
  classical
  have cap := (Multiset.toFinset_card_le (probe : (ZMod p)[X]).roots).trans
    ((Polynomial.card_roots' _).trans probe_degree)
  unfold residues
  rw [dif_pos (Fact.out : p.Prime)]
  exact (card_union_le _ _).trans ((Nat.add_le_add cap (card_image_le.trans cap)).trans (by decide))

theorem mem_residues {p : ℕ} [Fact p.Prime] (large : 2^280 ≤ p) (r : ZMod p)
    (hit : (probe : (ZMod p)[X]).eval r = 0 ∨ (probe : (ZMod p)[X]).eval (r+1) = 0) :
    r ∈ residues p := by
  classical
  unfold residues
  rw [dif_pos (Fact.out : p.Prime)]
  rcases hit with h|h
  · exact mem_union_left _ (Multiset.mem_toFinset.mpr ((mem_roots (probe_nonzero p large)).mpr h))
  · exact mem_union_right _ (mem_image.mpr ⟨r+1,
      Multiset.mem_toFinset.mpr ((mem_roots (probe_nonzero p large)).mpr h), add_sub_cancel_right ..⟩)

end
end PrimeFactors.HankelProbePolynomial
