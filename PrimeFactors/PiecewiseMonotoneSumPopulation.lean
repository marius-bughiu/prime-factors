import PrimeFactors.AntitoneSumPopulation
import PrimeFactors.MonotoneSumExtension

/-! Population bounds when the product selects among predictions with different
directions of monotonicity. Each prediction needs to obey its direction only on
its own domain. The domains can overlap and the sum tolerance is inclusive. -/

namespace PrimeFactors.PiecewiseMonotoneSumPopulation

open Finset MixedPrefixSample MonotoneSumPopulation
open scoped Classical

set_option exponentiation.threshold 4096
attribute [local irreducible] eligible primes

variable {ι : Type*}

/-- A global prediction agreeing at finitely many selected inputs exists in the same
direction. For a decreasing piece, take the maximum at inputs on or to the right. -/
theorem extend_piece (D : Finset ℕ) (g : ℕ→ℕ)
    (dir : MonotoneOn g D ∨ AntitoneOn g D) :
    ∃ h : ℕ→ℕ, (Monotone h ∨ Antitone h) ∧ ∀ n∈D,h n=g n := by
  rcases dir with up|down
  · obtain ⟨h,m,e⟩ := (MonotoneSumExtension.ordered_iff_exists (A:=D) (input:=id)
      (value:=g)).mp (fun _ hx _ hy le => up hx hy le)
    exact ⟨h,Or.inl m,e⟩
  · let h (n : ℕ) := (D.filter fun m => n≤m).sup g
    refine ⟨h,Or.inr (fun a b ab => sup_mono (fun x hx =>
      mem_filter.mpr ⟨(mem_filter.mp hx).1,ab.trans (mem_filter.mp hx).2⟩)),?_⟩
    intro n hn
    exact le_antisymm (Finset.sup_le fun m hm => down hn (mem_filter.mp hm).1 (mem_filter.mp hm).2)
      (le_sup (mem_filter.mpr ⟨hn,le_rfl⟩))

def fit (g : ℕ→ℕ) (E : ℕ) (z : ℕ×ℕ) : Prop :=
  g (z.1*z.2)≤z.1+z.2+E ∧ z.1+z.2≤g (z.1*z.2)+E

/-- Every counted pair has an applicable prediction in its tolerance band. -/
def Covered (A : Finset (ℕ×ℕ)) (I : Finset ι) (piece : ι→Set ℕ) (g : ι→ℕ→ℕ) (E : ℕ) : Prop :=
  ∀ z∈A, z∈eligible ∧ ∃ i∈I,z.1*z.2∈piece i ∧ fit (g i) E z

private theorem piece_subset (A : Finset (ℕ×ℕ)) (S : Set ℕ) (g : ℕ→ℕ) (E : ℕ)
    (direction : MonotoneOn g S ∨ AntitoneOn g S) :
    ∃ h : ℕ→ℕ, (Monotone h ∨ Antitone h) ∧
      ∀ z∈A, z∈eligible → z.1*z.2∈S → fit g E z → z∈agreement h E := by
  classical
  let D := (A.image (fun z => z.1*z.2)).filter (fun n => n∈S)
  have sub : (D : Set ℕ)⊆S := fun _ hn => (mem_filter.mp hn).2
  obtain ⟨h,m,e⟩ := extend_piece D g (direction.imp (fun h => h.mono sub) (fun h => h.mono sub))
  refine ⟨h,m,?_⟩
  intro z hz he hs hf
  have eq := e (z.1*z.2) (mem_filter.mpr ⟨mem_image.mpr ⟨z,hz,rfl⟩,hs⟩)
  exact mem_filter.mpr ⟨he,by simpa only [eq] using hf⟩

/-- Complete each piece to a total prediction while preserving all of the
counted hits, regardless of how the product selects its piece. -/
theorem covered_by_total (A : Finset (ℕ×ℕ)) (I : Finset ι) (piece : ι→Set ℕ) (g : ι→ℕ→ℕ)
    {E : ℕ} (direction : ∀ i∈I,MonotoneOn (g i) (piece i) ∨ AntitoneOn (g i) (piece i))
    (covered : Covered A I piece g E) :
    ∃ h : ι→ℕ→ℕ, (∀ i∈I,Monotone (h i) ∨ Antitone (h i)) ∧
      A⊆I.biUnion fun i => agreement (h i) E := by
  classical
  let P (i : ι) (h : ℕ→ℕ) := (Monotone h ∨ Antitone h) ∧
    ∀ z∈A, z∈eligible → z.1*z.2∈piece i → fit (g i) E z → z∈agreement h E
  have ex (i : ι) (hi : i∈I) : ∃ h,P i h := piece_subset A _ _ E (direction i hi)
  let h (i : ι) : ℕ→ℕ := if hi : i∈I then (ex i hi).choose else fun _ => 0
  have prop (i : ι) (hi : i∈I) : P i (h i) := by
    simpa only [h,dif_pos hi] using (ex i hi).choose_spec
  have sub : A⊆I.biUnion (fun i => agreement (h i) E) := by
    intro z hz
    obtain ⟨he,i,hi,hs,hf⟩ := covered z hz
    exact mem_biUnion.mpr ⟨i,hi,(prop i hi).2 z hz he hs hf⟩
  exact ⟨h,fun i hi => (prop i hi).1,sub⟩

/-- An absolute population bound for any tolerance and any finite number
of pieces, using a choice of product-block dimensions for the increasing pieces. -/
theorem count (A : Finset (ℕ×ℕ)) (I : Finset ι) (piece : ι→Set ℕ) (g : ι→ℕ→ℕ)
    (B W E : ℕ) (width : 0<W) (blocks : B*W=2^2048)
    (direction : ∀ i∈I,MonotoneOn (g i) (piece i) ∨ AntitoneOn (g i) (piece i))
    (covered : Covered A I piece g E) :
    A.card ≤ I.card*max (((2^1025-1)+(2*E+1)*B)*(W.sqrt+1)) ((2*E+1)*primes.card) := by
  obtain ⟨h,dir,sub⟩ := covered_by_total A I piece g direction covered
  calc
    _ ≤ (I.biUnion fun i => agreement (h i) E).card := card_le_card sub
    _ ≤ ∑ i∈I,(agreement (h i) E).card := card_biUnion_le
    _ ≤ ∑ _i∈I,max (((2^1025-1)+(2*E+1)*B)*(W.sqrt+1)) ((2*E+1)*primes.card) :=
      sum_le_sum fun i hi => (dir i hi).elim
        (fun up => le_max_of_le_left (MonotoneSumPopulation.count _ up B W E width blocks))
        (fun down => le_max_of_le_right (AntitoneSumPopulation.count _ down E))
    _ = _ := by simp

/-- The union bound charges each piece once, including when different pieces
predict on the same products. A selector using only N is a special case. -/
theorem fraction (A : Finset (ℕ×ℕ)) (I : Finset ι) (piece : ι→Set ℕ) (g : ι→ℕ→ℕ)
    {D E : ℕ} (nonempty : I.Nonempty)
    (direction : ∀ i∈I,MonotoneOn (g i) (piece i) ∨ AntitoneOn (g i) (piece i))
    (covered : Covered A I piece g E)
    (cap : ∀ h : ℕ→ℕ,(Monotone h ∨ Antitone h) → D*(agreement h E).card<eligible.card) :
    D*A.card<I.card*eligible.card := by
  obtain ⟨h,dir,sub⟩ := covered_by_total A I piece g direction covered
  calc
    _ ≤ D*((I.biUnion fun i => agreement (h i) E).card) :=
      Nat.mul_le_mul_left D (card_le_card sub)
    _ ≤ D*(∑ i∈I,(agreement (h i) E).card) := Nat.mul_le_mul_left D card_biUnion_le
    _ = ∑ i∈I,D*(agreement (h i) E).card := mul_sum ..
    _ < ∑ _i∈I,eligible.card := sum_lt_sum_of_nonempty nonempty (fun i hi => cap _ (dir i hi))
    _ = _ := by simp

private theorem down_cap {D E : ℕ} (small : D*(2*E+1)≤2^1007)
    (h : ℕ→ℕ) (down : Antitone h) : D*(agreement h E).card<eligible.card := by
  have h₁ := Nat.mul_le_mul_right (agreement h E).card small
  have h₂ := h₁.trans_lt (AntitoneSumPopulation.fraction h down E)
  apply Nat.lt_of_mul_lt_mul_left (a:=2*E+1)
  simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h₂

variable (A : Finset (ℕ×ℕ)) (I : Finset ι) (piece : ι→Set ℕ) (g : ι→ℕ→ℕ)
    (direction : ∀ i∈I,MonotoneOn (g i) (piece i) ∨ AntitoneOn (g i) (piece i))

include direction in
theorem exact_menu (nonempty : I.Nonempty) (covered : Covered A I piece g 0) :
    2^484*A.card<I.card*eligible.card :=
  fraction A I piece g nonempty direction covered (fun h dir =>
    dir.elim (MonotoneSumPopulation.exact_fraction h) (down_cap (by decide +kernel) h))

include direction in
theorem approximate_menu (nonempty : I.Nonempty) (covered : Covered A I piece g (2^128)) :
    2^419*A.card<I.card*eligible.card :=
  fraction A I piece g nonempty direction covered (fun h dir =>
    dir.elim (MonotoneSumPopulation.tolerance_128 h) (down_cap (by decide +kernel) h))

private theorem from_menu {D L : ℕ} {E : ℕ} (covered : Covered A I piece g E)
    (budget : I.card≤L)
    (bound : I.Nonempty → (L*D)*A.card<I.card*eligible.card) :
    D*A.card<eligible.card := by
  rcases I.eq_empty_or_nonempty with empty|nonempty
  · have ha : A=∅ := eq_empty_iff_forall_not_mem.mpr (by
      intro z hz
      obtain ⟨_,i,hi,_⟩ := covered z hz
      simp [empty] at hi)
    have den := ChebyshevPrimeSample.eligible_count
    rw [ha,card_empty,Nat.mul_zero]
    omega
  · apply Nat.lt_of_mul_lt_mul_left (a:=L)
    exact (Nat.mul_assoc ..).symm.le.trans_lt ((bound nonempty).trans_le (Nat.mul_le_mul_right _ budget))

include direction in
/-- A menu of at most 2^32 pieces, including an empty menu. -/
theorem exact_32 (budget : I.card≤2^32) (covered : Covered A I piece g 0) :
    2^452*A.card<eligible.card :=
  from_menu A I piece g covered budget (fun ne => by
    rw [show (2:ℕ)^32*2^452=2^484 by decide +kernel]
    exact exact_menu A I piece g direction ne covered)

include direction in
theorem approximate_32 (budget : I.card≤2^32) (covered : Covered A I piece g (2^128)) :
    2^387*A.card<eligible.card :=
  from_menu A I piece g covered budget (fun ne => by
    rw [show (2:ℕ)^32*2^387=2^419 by decide +kernel]
    exact approximate_menu A I piece g direction ne covered)

end PrimeFactors.PiecewiseMonotoneSumPopulation
