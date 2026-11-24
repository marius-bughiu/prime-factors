import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

namespace PrimeFactors.RationalSquareCount

open Finset

/-- Ordered choices of two different tuple positions. -/
noncomputable def positions : Finset (Fin 12 × Fin 12) := (univ : Finset (Fin 12)).offDiag

theorem positions_card : positions.card = 132 := by simp [positions]

noncomputable def matching (colour : Fin 12 → Fin 4) : Finset (Fin 12 × Fin 12) :=
  positions.filter fun ij => colour ij.1 = colour ij.2

private theorem class_lower (n : ℕ) : 5*n ≤ n*n-n+9 := by
  have hn : 6*n ≤ n*n+9 := by
    exact_mod_cast (show 6*(n : ℤ) ≤ (n : ℤ)*n+9 by nlinarith [sq_nonneg ((n : ℤ)-3)])
  omega

/-- Even a balanced four-colouring gives 24 ordered monochromatic pairs. -/
theorem at_least_twenty_four (colour : Fin 12 → Fin 4) : 24 ≤ (matching colour).card := by
  let bucket := fun c : Fin 4 => univ.filter (fun i => colour i = c)
  have mass : (∑ c, (bucket c).card) = 12 := by
    simpa [bucket] using (card_eq_sum_card_fiberwise (s := univ) (t := univ)
      (f := colour) (fun _ _ => mem_univ _)).symm
  have fibre (c : Fin 4) :
      (matching colour).filter (fun ij => colour ij.1 = c) = (bucket c).offDiag := by
    ext ⟨a,b⟩
    simp only [matching, positions, bucket, mem_filter, mem_offDiag, mem_univ, true_and]
    aesop
  have agreement : (∑ c, (bucket c).offDiag.card) = (matching colour).card := by
    simpa only [fibre] using (card_eq_sum_card_fiberwise (s := matching colour) (t := univ)
      (f := fun ij => colour ij.1) (fun _ _ => mem_univ _)).symm
  have lower : (∑ c, 5*(bucket c).card) ≤ ∑ c, ((bucket c).offDiag.card+9) := by
    exact sum_le_sum fun c _ => by simpa only [offDiag_card] using class_lower (bucket c).card
  rw [← mul_sum, mass, sum_add_distrib, agreement] at lower
  simp at lower
  omega

/-- If each allowed ordered pair has the same positive multiplicity in the
tuple/position incidences, at least 2/11 of those pairs have matching colours. -/
theorem uniform_pairs {T P : Type*} [DecidableEq T] [DecidableEq P]
    (tuples : Finset T) (pairs good : Finset P) (subset : good ⊆ pairs)
    (colour : T → Fin 12 → Fin 4) (emit : T × (Fin 12 × Fin 12) → P) {k : ℕ}
    (positive : 0 < k)
    (allowed : ∀ w ∈ tuples ×ˢ positions, emit w ∈ pairs)
    (uniform : ∀ a ∈ pairs, ((tuples ×ˢ positions).filter (fun w => emit w = a)).card = k)
    (agrees : ∀ t ∈ tuples, ∀ ij ∈ positions, emit (t,ij) ∈ good ↔ colour t ij.1 = colour t ij.2) :
    2*pairs.card ≤ 11*good.card := by
  classical
  let allPairs := tuples ×ˢ positions
  let marked := allPairs.filter (fun w => emit w ∈ good)
  have allCount : tuples.card*132 = pairs.card*k := by
    have h := card_eq_sum_card_fiberwise (f := emit) (s := allPairs) (t := pairs) allowed
    rw [sum_congr rfl uniform] at h
    simpa [allPairs, positions_card] using h
  have markedCount : marked.card = good.card*k := by
    change (allPairs.filter _).card = _
    rw [← sum_card_fiberwise_eq_card_filter allPairs good emit]
    rw [sum_congr rfl (fun a ha => uniform a (subset ha))]
    simp
  have markedFibre (t : T) (ht : t ∈ tuples) :
      marked.filter (fun w => w.1 = t) = {t} ×ˢ matching (colour t) := by
    ext ⟨v,ij⟩
    by_cases hv : v = t
    · subst v
      by_cases hi : ij ∈ positions <;> simp [marked, allPairs, matching, ht, hi, agrees t ht ij]
    · simp [hv, Ne.symm hv]
  have lower : 24*tuples.card ≤ marked.card := by
    have maps : marked.toSet.MapsTo Prod.fst tuples := by
      intro w hw
      exact (mem_product.mp (mem_filter.mp hw).1).1
    rw [card_eq_sum_card_fiberwise maps]
    calc
      _ = ∑ _t ∈ tuples, 24 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun t ht => by simpa [markedFibre t ht] using at_least_twenty_four (colour t)
  have cross : 2*(pairs.card*k) ≤ 11*(good.card*k) := by
    rw [← allCount, ← markedCount]
    omega
  exact Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_assoc] using cross) positive

/-- Ordered lists of disjoint k-element subsets of a finite bin. -/
noncomputable def disjointChoices {α : Type*} [DecidableEq α] (k : ℕ) :
    ℕ → Finset α → Finset (List (Finset α))
  | 0, _ => {[]}
  | n+1, pool => (pool.powersetCard k).biUnion fun head =>
      (disjointChoices k n (pool \ head)).image (head :: ·)

/-- Multiplying the successive binomial choices counts completions without
reference to the identities of the elements that were already used. -/
noncomputable def completionCount (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n+1, m => m.choose k * completionCount k n (m-k)

theorem completionCount_pos {k n m : ℕ} (room : n*k ≤ m) : 0 < completionCount k n m := by
  induction n generalizing m with
  | zero => simp [completionCount]
  | succ n ih =>
    rw [Nat.succ_mul] at room
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (ih (by omega))

theorem disjointChoices_card {α : Type*} [DecidableEq α] (k n : ℕ) (pool : Finset α) :
    (disjointChoices k n pool).card = completionCount k n pool.card := by
  induction n generalizing pool with
  | zero => simp [disjointChoices, completionCount]
  | succ n ih =>
    rw [disjointChoices, card_biUnion]
    · have term (x : Finset α) (hx : x ∈ pool.powersetCard k) :
          ((disjointChoices k n (pool \ x)).image (x :: ·)).card =
            completionCount k n (pool.card-k) := by
        obtain ⟨sub, size⟩ := mem_powersetCard.mp hx
        rw [card_image_of_injective _ List.cons_injective, ih, card_sdiff sub, size]
      rw [sum_congr rfl term]
      simp [completionCount, card_powersetCard]
    · intro x _ y _ ne
      apply disjoint_left.mpr
      rintro _ hx hy
      obtain ⟨xs, _, rfl⟩ := mem_image.mp hx
      obtain ⟨ys, _, eqn⟩ := mem_image.mp hy
      exact ne (List.cons.inj eqn).1.symm

/-- Fix two disjoint components in specified positions. The other ten have
the same number of ordered completions for every such choice in this bin. -/
theorem after_two {α : Type*} [DecidableEq α] (pool x y : Finset α) {k : ℕ}
    (sx : x ⊆ pool) (sy : y ⊆ pool) (dx : Disjoint x y)
    (cx : x.card = k) (cy : y.card = k) :
    (disjointChoices k 10 (pool \ (x ∪ y))).card = completionCount k 10 (pool.card-2*k) := by
  rw [disjointChoices_card, card_sdiff (union_subset sx sy), card_union_of_disjoint dx,
    cx, cy, two_mul]

/-- For independently chosen bins the completion multiplicities multiply.
Fixing either ordered pair of slots is the same count after permuting slots. -/
theorem binned_completions {B α : Type*} [Fintype B] [DecidableEq B] [DecidableEq α]
    (pool x y : B → Finset α) (k : B → ℕ)
    (sx : ∀ b, x b ⊆ pool b) (sy : ∀ b, y b ⊆ pool b) (dx : ∀ b, Disjoint (x b) (y b))
    (cx : ∀ b, (x b).card = k b) (cy : ∀ b, (y b).card = k b) :
    (Fintype.piFinset fun b => disjointChoices (k b) 10 (pool b \ (x b ∪ y b))).card =
      ∏ b, completionCount (k b) 10 ((pool b).card-2*k b) := by
  rw [Fintype.card_piFinset]
  exact prod_congr rfl fun b _ => after_two _ _ _ (sx b) (sy b) (dx b) (cx b) (cy b)

theorem sharp_example : (matching (fun i => ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩)).card = 24 := by
  decide

/-- Ordered same-colour pairs, including pairs with equal entries. -/
noncomputable def matchingPairs {α : Type*} (s : Finset α) (colour : α → Fin 4) :=
  (s ×ˢ s).filter fun xy => colour xy.1 = colour xy.2

/-- At least one quarter of the ordered pairs in any four-colouring agree. -/
theorem four_colour_pairs {α : Type*} (s : Finset α) (colour : α → Fin 4) :
    s.card^2 ≤ 4*(matchingPairs s colour).card := by
  classical
  let bucket := fun c => s.filter (fun x => colour x = c)
  have mass : (∑ c, (bucket c).card) = s.card :=
    (card_eq_sum_card_fiberwise (f := colour) (t := univ) (fun _ _ => mem_univ _)).symm
  have fibre (c : Fin 4) : (matchingPairs s colour).filter (fun xy => colour xy.1 = c) =
      bucket c ×ˢ bucket c := by
    ext ⟨x,y⟩
    simp only [matchingPairs, bucket, mem_filter, mem_product]
    aesop
  have count : (∑ c, (bucket c).card^2) = (matchingPairs s colour).card := by
    simpa only [fibre, card_product, sq] using
      (card_eq_sum_card_fiberwise (s := matchingPairs s colour) (t := univ)
        (f := fun xy => colour xy.1) (fun _ _ => mem_univ _)).symm
  have cs := sum_mul_sq_le_sq_mul_sq univ (fun _ : Fin 4 => 1) (fun c => (bucket c).card)
  simpa [mass, count] using cs

/-- Discarding an exceptional set of size at most O loses at most O pairs. -/
theorem four_colour_after_overlap {α : Type*} [DecidableEq α] (s : Finset α)
    (colour : α → Fin 4) (overlap : Finset (α × α)) {O : ℕ} (bound : overlap.card ≤ O) :
    s.card^2 ≤ 4*((matchingPairs s colour) \ overlap).card + 4*O := by
  have total := four_colour_pairs s colour
  have remove := card_le_card_sdiff_add_card (s := matchingPairs s colour) (t := overlap)
  omega

/-- Count a pair once for each common support element. This upper bounds
the number of pairs with nonempty intersection even when several elements recur. -/
theorem shared_support_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (keys : Finset β) (support : α → Finset β)
    (contained : ∀ x ∈ s, support x ⊆ keys) :
    ((s ×ˢ s).filter (fun xy => ¬Disjoint (support xy.1) (support xy.2))).card ≤
      ∑ j ∈ keys, (s.filter (fun x => j ∈ support x)).card^2 := by
  let hits := fun j => s.filter (fun x => j ∈ support x)
  have covered : (s ×ˢ s).filter (fun xy => ¬Disjoint (support xy.1) (support xy.2)) ⊆
      keys.biUnion (fun j => hits j ×ˢ hits j) := by
    intro xy hxy
    obtain ⟨h, overlap⟩ := mem_filter.mp hxy
    obtain ⟨hx,hy⟩ := mem_product.mp h
    obtain ⟨j,hjx,hjy⟩ := not_disjoint_iff.mp overlap
    exact mem_biUnion.mpr ⟨j, contained _ hx hjx,
      mem_product.mpr ⟨mem_filter.mpr ⟨hx,hjx⟩, mem_filter.mpr ⟨hy,hjy⟩⟩⟩
  calc
    _ ≤ _ := card_le_card covered
    _ ≤ ∑ j ∈ keys, (hits j ×ˢ hits j).card := card_biUnion_le
    _ = _ := by simp [hits, sq]

end PrimeFactors.RationalSquareCount
