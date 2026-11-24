import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- Parity of the passing entries selected by a row mask and a column mask. -/
noncomputable def maskedMidpointParity {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ZMod 2) (u : I → ZMod 2) (v : J → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, u i * A i j * v j

private theorem maskedMidpointParity_add_left {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ZMod 2) (u w : I → ZMod 2) (v : J → ZMod 2) :
    maskedMidpointParity A (u+w) v = maskedMidpointParity A u v + maskedMidpointParity A w v := by
  simp [maskedMidpointParity,add_mul,Finset.sum_add_distrib]

private theorem maskedMidpointParity_add_right {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ZMod 2) (u : I → ZMod 2) (v w : J → ZMod 2) :
    maskedMidpointParity A u (v+w) = maskedMidpointParity A u v + maskedMidpointParity A u w := by
  simp [maskedMidpointParity,mul_add,Finset.sum_add_distrib]

/-- Toggling two fixed mask coordinates gives four parities whose sum is
exactly their intersection entry. Thus at least one detects a nonzero pivot. -/
theorem maskedMidpointParity_corners {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : I → J → ZMod 2)
    (u : I → ZMod 2) (v : J → ZMod 2) (i : I) (j : J) :
    let e := fun x : I => if i=x then (1 : ZMod 2) else 0
    let f := fun y : J => if j=y then (1 : ZMod 2) else 0
    maskedMidpointParity A (u+e) (v+f) - maskedMidpointParity A (u+e) v -
      maskedMidpointParity A u (v+f) + maskedMidpointParity A u v = A i j := by
  dsimp only
  simp only [maskedMidpointParity_add_left, maskedMidpointParity_add_right]
  convert (show maskedMidpointParity A (fun x => if i=x then 1 else 0)
    (fun y => if j=y then 1 else 0) = A i j by
    simp [maskedMidpointParity,ite_mul,mul_ite]) using 1
  ring

/-- Under independent uniform row and column masks at least one quarter
of all mask pairs detect any nonzero matrix, regardless of its sparsity. -/
theorem maskedMidpointParity_quarter {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : I → J → ZMod 2) (i : I) (j : J) (pivot : A i j ≠ 0) :
    Fintype.card ((I → ZMod 2) × (J → ZMod 2)) ≤
      4 * ((Finset.univ : Finset ((I → ZMod 2) × (J → ZMod 2))).filter
        (fun w => maskedMidpointParity A w.1 w.2 ≠ 0)).card := by
  classical
  let good := (Finset.univ : Finset ((I → ZMod 2) × (J → ZMod 2))).filter
    (fun w => maskedMidpointParity A w.1 w.2 ≠ 0)
  let e : I → ZMod 2 := fun x => if i=x then 1 else 0
  let f : J → ZMod 2 := fun y => if j=y then 1 else 0
  let shift (b : Bool × Bool) : (I → ZMod 2) × (J → ZMod 2) :=
    (if b.1 then e else 0, if b.2 then f else 0)
  let setOfStarts (b : Bool × Bool) := good.image (fun w => w-shift b)
  have covered : Finset.univ ⊆ Finset.univ.biUnion setOfStarts := by
    intro w _
    have choose (b : Bool × Bool) (hit : maskedMidpointParity A
        (w.1+(shift b).1) (w.2+(shift b).2) ≠ 0) :
        w ∈ Finset.univ.biUnion setOfStarts := by
      apply Finset.mem_biUnion.mpr
      refine ⟨b,Finset.mem_univ _,Finset.mem_image.mpr ⟨w+shift b,?_,by simp⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩
    have corners := maskedMidpointParity_corners A w.1 w.2 i j
    change maskedMidpointParity A (w.1+e) (w.2+f) - maskedMidpointParity A (w.1+e) w.2 -
      maskedMidpointParity A w.1 (w.2+f) + maskedMidpointParity A w.1 w.2 = A i j at corners
    by_cases c : maskedMidpointParity A w.1 w.2 ≠ 0
    · exact choose (false,false) (by simpa [shift] using c)
    by_cases d : maskedMidpointParity A (w.1+e) w.2 ≠ 0
    · exact choose (true,false) (by simpa [shift] using d)
    by_cases h : maskedMidpointParity A w.1 (w.2+f) ≠ 0
    · exact choose (false,true) (by simpa [shift] using h)
    apply choose (true,true)
    simp [shift,not_ne_iff.mp c,not_ne_iff.mp d,not_ne_iff.mp h] at corners ⊢
    exact corners.trans_ne pivot
  calc
    _ = (Finset.univ : Finset ((I → ZMod 2) × (J → ZMod 2))).card := rfl
    _ ≤ _ := Finset.card_le_card covered
    _ ≤ ∑ b : Bool × Bool, (setOfStarts b).card := Finset.card_biUnion_le
    _ ≤ ∑ _ : Bool × Bool, good.card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ = _ := by simp [good]

private theorem short_shift_boundary {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (s : Finset K) (inhabited : s.Nonempty) (short : s.card < p) {d : K} (step : d ≠ 0) :
    ∃ c ∈ s, c+d ∉ s := by
  by_contra! closed
  obtain ⟨a,ha⟩ := inhabited
  have inSet (n : ℕ) : a + (n : K)*d ∈ s := by
    induction n with
    | zero => simpa using ha
    | succ n ih => simpa [Nat.cast_succ,add_mul,add_assoc] using closed _ ih
  let ι := ZMod.castHom (dvd_refl p) K
  have bound : (Finset.univ : Finset (ZMod p)).card ≤ s.card := by
    apply Finset.card_le_card_of_injOn (fun z : ZMod p => a + ι z*d)
    · intro z _
      have cast : ι z = (z.val : K) := by
        calc
          ι z = ι (z.val : ZMod p) := congrArg ι (ZMod.natCast_zmod_val z).symm
          _ = _ := map_natCast ι _
      simpa [cast] using inSet z.val
    · intro z _ w _ same
      apply ZMod.castHom_injective K
      exact mul_right_cancel₀ step (add_left_cancel same)
  have impossible : p ≤ s.card := by simpa [ZMod.card] using bound
  exact (Nat.not_le_of_lt short) impossible

/-- In any splitting field of odd characteristic, a nonempty selection
of fewer than p shifted quadratic factors has a root unique to one factor. -/
theorem shifted_midpoints_unique_root {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (s : Finset K) (inhabited : s.Nonempty) (short : s.card < p) (r : K)
    (separate : r+r ≠ 0) :
    ∃ c ∈ s, ∃ x : K, x+c = -r ∧ ∀ b ∈ s, (x+b)^2 = r^2 → b=c := by
  obtain ⟨c,hc,gap⟩ := short_shift_boundary s inhabited short separate
  refine ⟨c,hc,-c-r,by ring,?_⟩
  intro b hb h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with plus | minus
  · apply False.elim (gap ?_)
    convert hb using 1
    linear_combination -plus
  · linear_combination minus

example :
    ((Finset.univ : Finset ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2))).filter (fun w =>
      maskedMidpointParity (fun i j => if i=0 ∧ j=0 then 1 else 0) w.1 w.2 ≠ 0)).card = 4 := by
  decide

end PrimeFactors
