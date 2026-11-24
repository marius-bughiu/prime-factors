import PrimeFactors.ResidueCount
import PrimeFactors.FejerProjection
import Mathlib.Algebra.Polynomial.Roots

namespace PrimeFactors

open Polynomial

/-- In characteristic p, translating a nonempty set of fewer than p points
by a nonzero element moves at least one point outside the set. The field can
be an algebraic closure, so the statement also covers nonsplit quadratics. -/
theorem exists_exit_translate {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p]
    (A : Finset K) (nonempty : A.Nonempty) (short : A.card < p) {δ : K} (step : δ ≠ 0) :
    ∃ x ∈ A, x+δ ∉ A := by
  classical
  by_contra! closed
  obtain ⟨x,hx⟩ := nonempty
  have orbit (n : ℕ) : x+(n : K)*δ ∈ A := by
    induction n with
    | zero => simpa using hx
    | succ n ih => simpa [Nat.cast_succ,add_mul,add_assoc] using closed _ ih
  let emb := ZMod.castHom (dvd_refl p) K
  let f (z : ZMod p) := x+emb z*δ
  have inj : Function.Injective f := fun _ _ eq =>
    emb.injective ((mul_left_inj' step).mp (add_left_cancel eq))
  have into : ∀ z ∈ Finset.univ, f z ∈ A := by
    intro z _
    have eq : emb z=(z.val : K) := by
      calc emb z = emb (z.val : ZMod p) := congrArg emb (ZMod.natCast_zmod_val z).symm
           _ = _ := map_natCast emb z.val
    simpa [f,eq] using orbit z.val
  have bound := Finset.card_le_card_of_injOn f into inj.injOn
  simp only [Finset.card_univ,ZMod.card] at bound
  omega

/-- Any nonempty product of fewer than p distinct translates of a quadratic
with two distinct geometric roots has a simple geometric root. This supplies
the nonsquare condition for the character sums at every order of correlation. -/
theorem translated_quadratics_simple_root {p : ℕ} [Fact p.Prime] {K : Type*}
    [Field K] [CharP K p] (A : Finset K) (nonempty : A.Nonempty) (short : A.card < p)
    {a b : K} (distinct : a ≠ b) :
    ∃ z : K, rootMultiplicity z
      (∏ h ∈ A, (X-C (h+a))*(X-C (h+b)))=1 := by
  classical
  obtain ⟨h,hh,exit⟩ := exists_exit_translate A nonempty short (sub_ne_zero.mpr distinct)
  let z := h+a
  let F (i : K) : K[X] := (X-C (i+a))*(X-C (i+b))
  have other (i : K) (hi : i ∈ A) : z ≠ i+b := by
    intro eq
    apply exit
    rwa [show h+(a-b)=i by dsimp [z] at eq; linear_combination eq]
  have nz (i : K) : F i ≠ 0 := mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  have rem : ¬ IsRoot (∏ i ∈ A.erase h, F i) z := by
    rw [IsRoot.def,eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hi
    simpa only [F,eval_mul,eval_sub,eval_X,eval_C,ne_eq,mul_eq_zero,not_or,sub_eq_zero]
      using And.intro (show z ≠ i+a from fun e => ne (add_right_cancel e).symm) (other i mem)
  refine ⟨z,?_⟩
  change rootMultiplicity z (∏ i ∈ A, F i)=1
  rw [← Finset.mul_prod_erase A F hh, rootMultiplicity_mul
    (mul_ne_zero (nz h) (Finset.prod_ne_zero_iff.mpr fun i _ => nz i)),
    rootMultiplicity_eq_zero rem, add_zero]
  unfold F
  rw [rootMultiplicity_mul (nz h),rootMultiplicity_X_sub_C,rootMultiplicity_X_sub_C,
    if_pos (show z=h+a from rfl),if_neg (other h hh)]

/-- A translated product with a simple root cannot be a polynomial square. -/
theorem translated_quadratics_not_square {p : ℕ} [Fact p.Prime] {K : Type*}
    [Field K] [CharP K p] (A : Finset K) (nonempty : A.Nonempty) (short : A.card < p)
    {a b : K} (distinct : a ≠ b) :
    ¬ IsSquare (∏ h ∈ A, (X-C (h+a))*(X-C (h+b))) := by
  obtain ⟨z,hz⟩ := translated_quadratics_simple_root A nonempty short distinct
  rintro ⟨P,hP⟩
  have ne : P*P ≠ 0 := hP ▸ (Finset.prod_ne_zero_iff.mpr fun i _ =>
    mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))
  rw [hP,rootMultiplicity_mul ne] at hz
  omega

section Blocks

variable {M : ℕ} [NeZero M]

/-- Number of survivors among H cyclically consecutive positions starting at c.
Offsets are counted with multiplicity if the block wraps more than once. -/
noncomputable def sumGapBlock (A : Finset (ZMod M)) (H : ℕ) (c : ZMod M) : ℕ :=
  ∑ i ∈ Finset.range H, if c+i ∈ A then 1 else 0

/-- Number of ordered survivor pairs with prescribed displacement. -/
noncomputable def sumGapOverlap (A : Finset (ZMod M)) (d : ZMod M) : ℕ :=
  ∑ z : ZMod M, if z ∈ A ∧ z+d ∈ A then 1 else 0

/-- Exact numerator of the expected survivor count for a uniform translate. -/
theorem sumGapBlock_firstMoment (A : Finset (ZMod M)) (H : ℕ) :
    (∑ c : ZMod M, sumGapBlock A H c)=H*A.card := by
  unfold sumGapBlock
  rw [Finset.sum_comm]
  have term (i : ℕ) : (∑ c : ZMod M, if c+i ∈ A then 1 else 0)=A.card := by
    calc
      _ = ∑ z : ZMod M, if z ∈ A then 1 else 0 :=
        Equiv.sum_comp (Equiv.addRight (i : ZMod M)) (fun z => if z ∈ A then 1 else 0)
      _ = _ := by simp
  simp only [term,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id]

/-- Exact numerator of the second moment, including repeated offsets and
zero shifts. Together with the first moment this determines the variance
using only the cyclic overlap counts. -/
theorem sumGapBlock_secondMoment (A : Finset (ZMod M)) (H : ℕ) :
    (∑ c : ZMod M, (sumGapBlock A H c)^2)=
      ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, sumGapOverlap A ((j : ZMod M)-i) := by
  let f (z : ZMod M) : ℕ := if z ∈ A then 1 else 0
  have term (i j : ℕ) : (∑ c : ZMod M, f (c+i)*f (c+j))=sumGapOverlap A ((j : ZMod M)-i) := by
    calc
      _ = ∑ c : ZMod M, f (c+i)*f ((c+i)+(j-i : ZMod M)) := by simp [add_assoc,add_left_comm]
      _ = ∑ z : ZMod M, f z*f (z+(j-i : ZMod M)) :=
        Equiv.sum_comp (Equiv.addRight (i : ZMod M)) (fun z => f z*f (z+(j-i : ZMod M)))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z _
        dsimp [f]
        split_ifs <;> simp_all
  change (∑ c : ZMod M, (∑ i ∈ Finset.range H, f (c+i))^2)=_
  simp_rw [pow_two,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp only [term]

end Blocks

/-- At every nonzero frequency complete periods of a rectangular window
cancel, leaving only its remainder modulo the conductor. -/
private theorem window_remainder {d : ℕ} [NeZero d] (H : ℕ) (k : ZMod d) (nonzero : k ≠ 0) :
    bandMass d (Finset.range H) (fun _ => 1) k =
      bandMass d (Finset.range (H%d)) (fun _ => 1) k := by
  let f (i : ℕ) := ZMod.stdAddChar ((i : ZMod d)*k)
  have full : (∑ i ∈ Finset.range d, f i)=0 := by
    rw [← Fin.sum_univ_eq_sum_range f]
    have eq (i : Fin d) : (ZMod.finEquiv d) i=(i.val : ZMod d) := by
      rw [← map_natCast (ZMod.finEquiv d) i.val]
      simp
    calc
      _ = ∑ i : Fin d, ZMod.stdAddChar ((ZMod.finEquiv d i)*k) := by simp only [eq,f]
      _ = ∑ z : ZMod d, ZMod.stdAddChar (z*k) :=
        Equiv.sum_comp (ZMod.finEquiv d).toEquiv (fun z : ZMod d => ZMod.stdAddChar (z*k))
      _ = 0 := by rw [AddChar.sum_mulShift k (ZMod.isPrimitive_stdAddChar d)]; simp [nonzero]
  have cut (n : ℕ) : (∑ i ∈ Finset.range (d+n), f i) = ∑ i ∈ Finset.range n, f i := by
    rw [Finset.sum_range_add,full,zero_add]
    simp [f]
  have strip (j : ℕ) : (∑ i ∈ Finset.range (H%d+d*j), f i)=∑ i ∈ Finset.range (H%d), f i := by
    induction j with
    | zero => simp
    | succ n ih =>
      rw [show H%d+d*(n+1)=d+(H%d+d*n) by ring,cut,ih]
  have eq := strip (H/d)
  rw [Nat.mod_add_div] at eq
  simpa only [bandMass,one_mul] using congrArg Complex.normSq eq

/-- Exact nonzero Fourier energy of a block of arbitrary width H at
denominator d. The formula also handles widths exceeding one period. -/
theorem sumGap_windowEnergy (d H : ℕ) [NeZero d] :
    let r := H%d
    (∑ k ∈ (Finset.univ : Finset (ZMod d)).erase 0,
      bandMass d (Finset.range H) (fun _ => 1) k) = (r : ℝ)*(d-r) := by
  let r := H%d
  have short : r≤d := (Nat.mod_lt H (Nat.pos_of_ne_zero (NeZero.ne d))).le
  have move (Q : ℕ) [NeZero Q] (eq : Q=d) :
      (∑ k : ZMod d, bandMass Q (Finset.range r) (fun _ => 1) (k.val : ZMod Q))=
      (∑ k : ZMod d, bandMass d (Finset.range r) (fun _ => 1) k) := by subst Q; simp
  have total : (∑ k : ZMod d, bandMass d (Finset.range r) (fun _ => 1) k)=(d : ℝ)*r := by
    rw [← move (1*d) (Nat.one_mul d)]
    simpa only [zero_add,Nat.cast_one,one_mul] using
      fejer_uniform_fiber (m:=1) (n:=d) (H:=r) short 0
  have dc : bandMass d (Finset.range r) (fun _ => 1) 0=(r : ℝ)^2 := by
    simp [bandMass,AddChar.map_zero_eq_one,Complex.normSq_apply,pow_two]
  have erased := Finset.sum_erase_add Finset.univ
    (fun k : ZMod d => bandMass d (Finset.range r) (fun _ => 1) k) (Finset.mem_univ 0)
  dsimp only at erased ⊢
  rw [dc,total] at erased
  rw [Finset.sum_congr rfl (fun k hk => window_remainder H k (Finset.mem_erase.mp hk).1)]
  change _ = (r : ℝ)*(d-r)
  nlinarith only [erased]

end PrimeFactors
