import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! A finite list of scalar shifts separates a distinguished conjugate from the
oppositely signed evaluation. The number of possible failures is independent of the
size of the splitting field. -/

namespace PrimeFactors.CubicTraceMasks
open scoped BigOperators Classical

variable {ι F : Type*} [Field F]

/-- The factor contributed by a conjugate with coordinates `a,b` at shift `c`. -/
def term (m z a b c : F) : F := z*(m+c) - (a+c)*b

/-- The shifted characteristic product, evaluated in any common splitting field. -/
noncomputable def signal (I : Finset ι) (a δ : ι → F) (m z c : F) : F :=
  ∏ i ∈ I, term m z (a i) (δ i) c

/-- With unequal slopes, the unique forbidden shift is explicit. -/
theorem term_zero {m z a b c : F} (hb : b ≠ z) :
    term m z a b c = 0 ↔ c = (a*b-z*m)/(z-b) := by
  rw [eq_div_iff (sub_ne_zero.mpr hb.symm)]
  unfold term
  constructor <;> intro h <;> linear_combination h

/-- For a nonzero target, matching both coordinates is precisely what makes the
linear factor vanish at every shift. -/
theorem all_shifts_zero {m z a b : F} (hz : z ≠ 0) :
    (∀ c, term m z a b c = 0) ↔ a = m ∧ b = z := by
  constructor
  · intro all
    have h0 := all 0
    have h1 := all 1
    unfold term at h0 h1
    have hb : b = z := by linear_combination h0 - h1
    refine ⟨?_, hb⟩
    rw [hb] at h0
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show z*(a-m) = 0 by linear_combination -h0)).resolve_left hz
  · rintro ⟨rfl, rfl⟩ c
    unfold term
    ring

/-- Among any candidate shifts, every failure belongs to a single forbidden
shift contributed by an index with unequal slopes. Distinct indices may forbid
the same shift. -/
theorem bad_count (I : Finset ι) (a δ : ι → F) (m z : F) (S : Finset F)
    (hz : z ≠ 0) (safe : ∀ i ∈ I, ¬(a i = m ∧ δ i = z)) :
    (S.filter (fun c => signal I a δ m z c = 0)).card ≤
      (I.filter (fun i => δ i ≠ z)).card := by
  classical
  let src := I.filter (fun i => δ i ≠ z)
  let root := fun i => (a i * δ i - z*m)/(z-δ i)
  have inclusion : S.filter (fun c => signal I a δ m z c = 0) ⊆ src.image root := by
    intro c hc
    obtain ⟨i, hi, hit⟩ := Finset.prod_eq_zero_iff.mp (Finset.mem_filter.mp hc).2
    have diff : δ i ≠ z := by
      intro h
      have factor : z*(m-a i) = 0 := by
        change term m z (a i) (δ i) c = 0 at hit
        unfold term at hit
        rw [h] at hit
        linear_combination hit
      have eq := sub_eq_zero.mp ((mul_eq_zero.mp factor).resolve_left hz)
      exact safe i hi ⟨eq.symm, h⟩
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨hi, diff⟩, ((term_zero diff).mp hit).symm⟩
  exact (Finset.card_le_card inclusion).trans Finset.card_image_le

/-- A public set of sufficiently many distinct shifts contains a separator. -/
theorem exists_shift (I : Finset ι) (a δ : ι → F) (m z : F) (S : Finset F)
    (hz : z ≠ 0) (safe : ∀ i ∈ I, ¬(a i = m ∧ δ i = z))
    (room : (I.filter (fun i => δ i ≠ z)).card < S.card) :
    ∃ c ∈ S, signal I a δ m z c ≠ 0 := by
  classical
  by_contra! miss
  have bound := bad_count I a δ m z S hz safe
  rw [Finset.filter_eq_self.mpr miss] at bound
  omega

private theorem consecutive {I : Finset ι} {a δ : ι → F} {m z : F} {k : ℕ}
    (hz : z ≠ 0) (safe : ∀ i ∈ I, ¬(a i = m ∧ δ i = z))
    (room : (I.filter (fun i => δ i ≠ z)).card < k)
    (char : ringChar F = 0 ∨ k ≤ ringChar F) :
    ∃ j < k, signal I a δ m z (j : F) ≠ 0 := by
  classical
  let S := (Finset.range k).image (Nat.cast : ℕ → F)
  have size : S.card = k := by
    unfold S
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro x hx y hy eq
    have he := (CharP.natCast_eq_natCast F (ringChar F)).mp eq
    rcases char with zero | large
    · simpa [zero] using he
    · exact he.eq_of_lt_of_lt ((Finset.mem_range.mp hx).trans_le large)
        ((Finset.mem_range.mp hy).trans_le large)
  obtain ⟨c, hc, ok⟩ := exists_shift I a δ m z S hz safe (size ▸ room)
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
  exact ⟨j, Finset.mem_range.mp hj, ok⟩

/-- For distinct conjugates, a distinguished evaluation of the opposite sign
excludes the identically zero case, leaving at most one bad shift per conjugate.
The list here is exactly the public integers `0,…,I.card`. -/
theorem distinguished {I : Finset ι} {a δ : ι → F} {m z : F} {i₀ : ι}
    (hi : i₀ ∈ I) (inj : Set.InjOn a (I : Set ι)) (hm : a i₀ = m)
    (neg : δ i₀ = -z) (sep : -z ≠ z) (hz : z ≠ 0)
    (char : ringChar F = 0 ∨ I.card < ringChar F) :
    ∃ j ≤ I.card, signal I a δ m z (j : F) ≠ 0 := by
  have safe : ∀ i ∈ I, ¬(a i = m ∧ δ i = z) := by
    rintro i h ⟨e, both⟩
    have eq := inj h hi (e.trans hm.symm)
    exact sep (neg.symm.trans (eq ▸ both))
  obtain ⟨j, bound, ok⟩ := consecutive hz safe
    (k := I.card+1) (Nat.lt_succ_of_le (Finset.card_filter_le ..))
    (char.imp_right Nat.succ_le_of_lt)
  exact ⟨j, Nat.le_of_lt_succ bound, ok⟩

/-- A zero in the ordinary, unshifted characteristic product saves one shift.
Such a conjugate has equal slopes, so it never contributes a forbidden shift. -/
theorem after_original_zero {I : Finset ι} {a δ : ι → F} {m z : F}
    (hz : z ≠ 0) (safe : ∀ i ∈ I, ¬(a i = m ∧ δ i = z))
    (original : ∏ i ∈ I, (z - δ i) = 0)
    (char : ringChar F = 0 ∨ I.card ≤ ringChar F) :
    ∃ j < I.card, signal I a δ m z (j : F) ≠ 0 := by
  obtain ⟨i, hi, hit⟩ := Finset.prod_eq_zero_iff.mp original
  refine consecutive hz safe (lt_of_le_of_ne (Finset.card_filter_le ..) ?_) char
  intro eq
  exact Finset.card_filter_eq_iff.mp eq i hi (sub_eq_zero.mp hit).symm

/-- In a residue field where the distinguished evaluation instead equals
`z`, the same minus-sign product vanishes for every shift. -/
theorem matching_zero {I : Finset ι} {a δ : ι → F} {m z : F} {i₀ : ι}
    (hi : i₀ ∈ I) (hm : a i₀ = m) (matchValue : δ i₀ = z) (c : F) :
    signal I a δ m z c = 0 := by
  apply Finset.prod_eq_zero_iff.mpr
  refine ⟨i₀, hi, ?_⟩
  rw [hm, matchValue]
  unfold term
  ring

/-- On the plus side, a distinguished evaluation of the opposite sign makes
the product zero for every shift, with no separability or size requirement. -/
theorem plus_zero {I : Finset ι} {a δ : ι → F} {m z : F} {i₀ : ι}
    (hi : i₀ ∈ I) (hm : a i₀ = m) (neg : δ i₀ = -z) (c : F) :
    ∏ i ∈ I, (z*(m+c) + (a i+c)*δ i) = 0 := by
  apply Finset.prod_eq_zero_iff.mpr
  refine ⟨i₀, hi, ?_⟩
  rw [hm, neg]
  ring

/-- Three arbitrary conjugate evaluations can rule out the first three shifts.
The fourth works. This example concerns the field lemma alone. -/
theorem sharp_three (c : ℚ) :
    term 0 1 0 (-1) c * term 0 1 1 (1/2) c * term 0 1 2 (1/2) c =
      c*(c-1)*(c-2)/2 := by
  unfold term
  ring

end PrimeFactors.CubicTraceMasks
