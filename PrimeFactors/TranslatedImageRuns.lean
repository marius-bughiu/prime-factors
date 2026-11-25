import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import PrimeFactors.FactorSum

namespace PrimeFactors.TranslatedImageRuns

open Polynomial

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [Algebra (ZMod p) K]

/-- An absent position is exactly a negative discriminant sign. The second coefficient
can be specialized to the product of a public weight and the input integer. -/
theorem weighted_omission (odd : p ≠ 2) {a b t : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
    (¬ ∃ u : ZMod p, u ≠ 0 ∧ a*u+b/u=t) ↔
      quadraticChar (ZMod p) (t^2-4*(a*b)) = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare, ← admissibleSum_iff_isSquare odd]
  apply not_congr
  constructor
  · rintro ⟨u, hu, h⟩
    refine ⟨a*u, b/u, ?_, h⟩
    field_simp
    ring
  · rintro ⟨x, y, eq, total⟩
    have hx : x ≠ 0 := fun z => (mul_ne_zero ha hb) (by simpa [z] using eq.symm)
    refine ⟨x/a, div_ne_zero hx ha, ?_⟩
    have hy : b/(x/a) = y := by
      field_simp
      linear_combination -eq
    rw [hy, mul_div_cancel₀ _ ha, total]

/-- Every nonempty set of fewer than p shifts has an edge leaving it under any nonzero
additive translation, even in an extension of the prime field. -/
theorem escaping_shift (J : Finset K) (nonempty : J.Nonempty) (small : J.card < p)
    {d : K} (nonzero : d ≠ 0) : ∃ j ∈ J, j+d ∉ J := by
  by_contra! closed
  obtain ⟨x,hx⟩ := nonempty
  have step (n : ℕ) : x+(n : K)*d ∈ J := by
    induction n with
    | zero => simpa using hx
    | succ n h =>
      convert closed _ h using 1
      push_cast
      ring
  let f (t : ZMod p) : J :=
    ⟨x+algebraMap (ZMod p) K t*d, by
      have h := step t.val
      have eq : (t.val : K) = algebraMap (ZMod p) K t := by
        rw [← ZMod.natCast_zmod_val t, map_natCast]
        simp
      rwa [eq] at h⟩
  have inj : Function.Injective f := by
    intro u v same
    have eq := congrArg Subtype.val same
    change x + algebraMap (ZMod p) K u*d = x + algebraMap (ZMod p) K v*d at eq
    exact (algebraMap (ZMod p) K).injective (mul_right_cancel₀ nonzero (add_left_cancel eq))
  have bound := Fintype.card_le_of_injective f inj
  have : p ≤ J.card := by simpa [ZMod.card] using bound
  omega

/-- The quadratic discriminants in a selected collection of translated tests. -/
noncomputable def shiftProduct {R : Type*} [CommRing R] (J : Finset R) (c : R) : R[X] :=
  ∏ j ∈ J, ((X+C j)^2-C c)

/-- A proper collection has a simple root in a field splitting X²−c. No pairwise
coprimality assumption on its quadratic factors is necessary. -/
theorem simple_root (J : Finset K) (nonempty : J.Nonempty) (small : J.card < p)
    (two : (2 : K) ≠ 0) {s : K} (sn : s ≠ 0) :
    ∃ x : K, (shiftProduct J (s^2)).eval x = 0 ∧ (shiftProduct J (s^2)).derivative.eval x ≠ 0 := by
  classical
  have nonzero := neg_ne_zero.mpr (mul_ne_zero two sn)
  obtain ⟨j,jin,out⟩ := escaping_shift (p := p) J nonempty small (d := -(2*s)) nonzero
  let f (k : K) : K[X] := (X+C k)^2-C (s^2)
  let x := s-j
  have at_j : (f j).eval x = 0 := by simp [f,x]
  have others (k : K) (hk : k ∈ J.erase j) : (f k).eval x ≠ 0 := by
    obtain ⟨different,inside⟩ := Finset.mem_erase.mp hk
    intro z
    have eq : (x+k)^2 = s^2 := sub_eq_zero.mp (by simpa [f] using z)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp eq with plus | minus
    · exact different (by dsimp [x] at plus; linear_combination plus)
    · apply out
      convert inside using 1
      dsimp [x] at minus
      linear_combination -minus
  have nonzero_rest : (∏ k ∈ J.erase j, f k).eval x ≠ 0 := by
    rw [Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.mpr others
  have deriv : (f j).derivative.eval x = 2*s := by
    simp [f,Polynomial.derivative_pow,x]
  refine ⟨x,?_,?_⟩
  · change (∏ k ∈ J, f k).eval x = 0
    rw [← Finset.mul_prod_erase J f jin,eval_mul,at_j,zero_mul]
  · change (∏ k ∈ J, f k).derivative.eval x ≠ 0
    rw [← Finset.mul_prod_erase J f jin,derivative_mul,eval_add,eval_mul,eval_mul,
      deriv,at_j,zero_mul,add_zero]
    exact mul_ne_zero (mul_ne_zero two sn) nonzero_rest

/-- Over the algebraic closure the subset polynomial cannot be a scalar times a square.
The shifts can be any distinct field elements, including nonconsecutive positions. -/
theorem not_scalar_square [IsAlgClosed K] (J : Finset K) (nonempty : J.Nonempty)
    (small : J.card < p) (two : (2 : K) ≠ 0) {c : K} (cn : c ≠ 0)
    (a : K) (Q : K[X]) : shiftProduct J c ≠ C a * Q^2 := by
  obtain ⟨s,eq⟩ := IsAlgClosed.exists_pow_nat_eq c (by decide : 0 < 2)
  have sn : s ≠ 0 := fun h => cn (by simp [←eq,h])
  obtain ⟨x,zero,simple⟩ := simple_root (p := p) J nonempty small two sn
  rw [eq] at zero simple
  intro square
  rw [square,eval_mul,eval_C,eval_pow] at zero
  rw [square,derivative_mul,derivative_C,zero_mul,zero_add,derivative_pow] at simple
  simp only [eval_mul,eval_pow,eval_C,Nat.reduceSub,pow_one] at simple
  rcases mul_eq_zero.mp zero with az | qz
  · exact simple (by simp [az])
  · exact simple (by simp [sq_eq_zero_iff.mp qz])

/-- The base-field polynomial satisfies geometric nonsquareness after its coefficients
are mapped to an algebraically closed extension. -/
theorem mapped_not_square [IsAlgClosed K] (J : Finset (ZMod p))
    (nonempty : J.Nonempty) (small : J.card < p) (two : (2 : K) ≠ 0)
    {c : ZMod p} (cn : c ≠ 0) :
    ¬ ∃ g : K[X], g*g = (shiftProduct J c).map (algebraMap (ZMod p) K) := by
  let e : ZMod p ↪ K := ⟨algebraMap (ZMod p) K, (algebraMap (ZMod p) K).injective⟩
  have mapped : (shiftProduct J c).map (algebraMap (ZMod p) K) =
      shiftProduct (J.map e) (algebraMap (ZMod p) K c) := by
    simp [shiftProduct, Polynomial.map_prod, e]
  rintro ⟨g, hg⟩
  apply not_scalar_square (p := p) (J.map e) nonempty.map (by simpa) two
    ((map_ne_zero (algebraMap (ZMod p) K)).mpr cn) 1 g
  simpa [sq] using mapped.symm.trans hg.symm

/-- A bound on affine hyperelliptic points gives exactly the same bound on the character sum. -/
theorem curve_count {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (odd : ringChar F ≠ 2) (f : F[X]) :
    (Fintype.card {z : F × F // z.2^2 = f.eval z.1} : ℤ) =
      Fintype.card F + ∑ x : F, quadraticChar F (f.eval x) := by
  classical
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun (x y : F) => y^2 = f.eval x)),
    Fintype.card_sigma, Nat.cast_sum]
  have count (x : F) : (Fintype.card {y : F // y^2 = f.eval x} : ℤ) =
      quadraticChar F (f.eval x) + 1 := by
    simpa only [Set.toFinset_card] using quadraticChar_card_sqrts odd (f.eval x)
  simp_rw [count]
  simp [Finset.sum_add_distrib,add_comm]

/-- The character expansion has a term for every subset of the requested positions. -/
theorem pattern_expansion {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
    (J : Finset ι) (v : ι → F) :
    ∏ j ∈ J, (1 - quadraticChar F (v j)) =
      ∑ I ∈ J.powerset, (-1 : ℤ)^I.card * quadraticChar F (∏ j ∈ I, v j) := by
  classical
  simp_rw [sub_eq_add_neg]
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro I _
  simp only [map_prod]
  simp_rw [←neg_one_mul (quadraticChar F _), Finset.prod_mul_distrib, Finset.prod_const]

/-- Every occurrence of the all-negative word contributes its full weight. -/
theorem pattern_weight {ι : Type*} (J : Finset ι) (v : ι → ℤ)
    (all_neg : ∀ j ∈ J, v j = -1) : (∏ j ∈ J, (1-v j)) = 2^J.card := by
  calc
    _ = ∏ _j ∈ J, (2 : ℤ) := Finset.prod_congr rfl fun j hj => by rw [all_neg j hj]; decide
    _ = _ := Finset.prod_const _

theorem pattern_positive {ι : Type*} (J : Finset ι) (v : ι → ℤ) {j : ι}
    (hj : j ∈ J) (h : v j = 1) : (∏ j ∈ J, (1-v j)) = 0 :=
  Finset.prod_eq_zero hj (by simp [h])

/-- At a zero of a translated quadratic, the indicator contributes at most half weight. -/
theorem pattern_zero_bound {ι : Type*} (J : Finset ι) (v : ι → ℤ)
    (range : ∀ j ∈ J, v j = -1 ∨ v j = 0 ∨ v j = 1) {j : ι}
    (hj : j ∈ J) (h : v j = 0) :
    (∏ j ∈ J, (1-v j)) ≤ 2^(J.card-1) := by
  classical
  rw [← Finset.mul_prod_erase J _ hj, h, sub_zero, one_mul]
  calc
    _ ≤ ∏ _i ∈ J.erase j, (2 : ℤ) := Finset.prod_le_prod
      (fun i hi => by rcases range i (Finset.mem_of_mem_erase hi) with h | h | h <;> omega)
      (fun i hi => by rcases range i (Finset.mem_of_mem_erase hi) with h | h | h <;> omega)
    _ = _ := by rw [Finset.prod_const, Finset.card_erase_of_mem hj]

end PrimeFactors.TranslatedImageRuns
