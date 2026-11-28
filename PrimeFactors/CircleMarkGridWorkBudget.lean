import PrimeFactors.CircleMarkRationalFrequency
import PrimeFactors.CircleMarkRationalProduct

/-! For one fixed product, allow a different positive-prefix rectangle for every
negative-Jacobi target. A bound on the sum of the two list lengths limits the
union of all reachable cells. Counts concern uniform targets, independently of
the work needed to choose a shape or to evaluate its product. -/

namespace PrimeFactors.CircleMarkGridWorkBudget

open Finset CircleMarkTargetFrequency
open CircleMarkRationalFrequency (rectangle)
open private PrimeFactors.CircleMarkRationalFrequency.point PrimeFactors.CircleMarkRationalFrequency.in_rect
  from PrimeFactors.CircleMarkRationalFrequency
open private PrimeFactors.CircleMarkRationalFrequency.normalize PrimeFactors.CircleMarkRationalFrequency.denom
  PrimeFactors.CircleMarkRationalFrequency.fraction_eq PrimeFactors.CircleMarkRationalFrequency.square_injective
  PrimeFactors.CircleMarkRationalFrequency.local_point PrimeFactors.CircleMarkRationalFrequency.clear_point
  from PrimeFactors.CircleMarkRationalFrequency
open PrimeFactors.CircleMarkRationalFrequency (point in_rect normalize denom fraction_eq square_injective
  local_point clear_point)

/-- Positive cells reachable by some prefix rectangle with list lengths summing to at most L. -/
noncomputable def cells (L : ℕ) : Finset (ℕ × ℕ) :=
  (rectangle L L).filter fun z => z.1 + z.2 ≤ L

theorem mem_cells {L : ℕ} {z : ℕ × ℕ} :
    z ∈ cells L ↔ 0 < z.1 ∧ 0 < z.2 ∧ z.1 + z.2 ≤ L := by
  simp only [cells, mem_filter, in_rect]
  omega

theorem reachable {L : ℕ} {z : ℕ × ℕ} :
    z ∈ cells L ↔ ∃ H D, H + D ≤ L ∧ z ∈ rectangle H D := by
  rw [mem_cells]
  constructor
  · rintro ⟨a,b,cap⟩
    exact ⟨z.1,z.2,cap,in_rect.mpr ⟨⟨a,le_rfl⟩,⟨b,le_rfl⟩⟩⟩
  · rintro ⟨H,D,cap,inside⟩
    obtain ⟨⟨a,h⟩,⟨b,d⟩⟩ := in_rect.mp inside
    exact ⟨a,b,by omega⟩

noncomputable def menu (n L : ℕ) : Finset ℕ :=
  (cells L).image fun z => (point n z).val

/-- An oracle that sees the target can succeed with some allowed shape exactly when
the target hits the union menu. Selection and evaluation may cost additional work. -/
theorem some_shape {n L : ℕ} [NeZero n] (t : ZMod n) :
    t ∈ hits n (menu n L) ↔ ∃ H D, H + D ≤ L ∧
      t ∈ hits n (CircleMarkRationalFrequency.menu n H D) := by
  simp only [hits, mem_filter, menu, CircleMarkRationalFrequency.menu, Finset.exists_mem_image]
  constructor
  · rintro ⟨neg,z,inside,mark⟩
    obtain ⟨H,D,cap,mem⟩ := reachable.mp inside
    exact ⟨H,D,cap,neg,z,mem,mark⟩
  · rintro ⟨H,D,cap,neg,z,mem,mark⟩
    exact ⟨neg,z,reachable.mpr ⟨H,D,cap,mem⟩,mark⟩

/-- For invertible denominators, the union counts exactly the negative targets for
which an actual integer gcd at an eligible cell is greater than one. -/
theorem gcd_hit {n L : ℕ} [NeZero n]
    (units : ∀ z ∈ cells L, z.2.Coprime n) (t : ZMod n) :
    t ∈ hits n (menu n L) ↔ t ∈ targets n ∧ ∃ z ∈ cells L,
      n.gcd (NormBatchGCD.leaf t.val z.1 z.2) ≠ 1 := by
  rw [some_shape]
  constructor
  · rintro ⟨H,D,cap,hit⟩
    have sub z (mem : z ∈ rectangle H D) := reachable.mpr ⟨H,D,cap,mem⟩
    obtain ⟨neg,z,mem,nontrivial⟩ :=
      (CircleMarkRationalFrequency.gcd_hit (fun z mem => units z (sub z mem)) t).mp hit
    exact ⟨neg,z,sub _ mem,nontrivial⟩
  · rintro ⟨neg,z,inside,nontrivial⟩
    obtain ⟨H,D,cap,mem⟩ := reachable.mp inside
    exact ⟨H,D,cap,(CircleMarkRationalFrequency.gcd_hit
      (fun w hw => units w (reachable.mpr ⟨H,D,cap,hw⟩)) t).mpr ⟨neg,z,mem,nontrivial⟩⟩

/-- The same event can be tested with the product of all norm leaves in the chosen rectangle. -/
theorem product_hit {n L : ℕ} [NeZero n]
    (units : ∀ z ∈ cells L, z.2.Coprime n) (t : ZMod n) :
    t ∈ hits n (menu n L) ↔ t ∈ targets n ∧ ∃ H D, H + D ≤ L ∧
      ¬n.Coprime (CircleMarkRationalProduct.product t.val H D) := by
  rw [gcd_hit units]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨z,hz,nontrivial⟩
    obtain ⟨H,D,cap,mem⟩ := reachable.mp hz
    obtain ⟨i,j⟩ := mem_product.mp mem
    exact ⟨H,D,cap,(CircleMarkRationalProduct.has_hit ..).mpr ⟨z.1,i,z.2,j,nontrivial⟩⟩
  · rintro ⟨H,D,cap,hit⟩
    obtain ⟨i,im,j,jm,nontrivial⟩ := (CircleMarkRationalProduct.has_hit ..).mp hit
    exact ⟨(i,j),reachable.mpr ⟨H,D,cap,mem_product.mpr ⟨im,jm⟩⟩,nontrivial⟩

/-- Ordinary reduced slopes in the triangle, before reduction modulo any prime. -/
noncomputable def reduced (L : ℕ) : Finset (ℕ × ℕ) :=
  (cells L).filter fun z => z.1.Coprime z.2

private theorem fiber {k L : ℕ} (mem : k ∈ Icc 2 L) :
    ((reduced L).filter (fun z => z.1 + z.2 = k)).card = k.totient := by
  obtain ⟨lo,hi⟩ := mem_Icc.mp mem
  rw [Nat.totient_eq_card_coprime]
  apply card_bij (fun z _ => z.1)
  · intro z hz
    obtain ⟨h,sum⟩ := mem_filter.mp hz
    obtain ⟨m,cop⟩ := mem_filter.mp h
    obtain ⟨a,b,cap⟩ := mem_cells.mp m
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),sum ▸ Nat.coprime_self_add_left.mpr cop.symm⟩
  · intro z hz w hw eq
    have a := (mem_filter.mp hz).2
    have b := (mem_filter.mp hw).2
    exact Prod.ext eq (by omega)
  · intro i ih
    obtain ⟨bound,cop⟩ := mem_filter.mp ih
    have small := mem_range.mp bound
    have pos : 0 < i := by
      apply Nat.pos_of_ne_zero
      intro zero
      subst i
      simp at cop
      omega
    refine ⟨(i,k-i),mem_filter.mpr ⟨mem_filter.mpr ⟨mem_cells.mpr ?_,?_⟩,?_⟩,rfl⟩
    · dsimp
      omega
    · exact (Nat.coprime_sub_self_right small.le).mpr cop.symm
    · dsimp
      omega

/-- The positive coprime cells of each sum k correspond to the reduced residues modulo k. -/
theorem reduced_count (L : ℕ) : (reduced L).card = ∑ k ∈ Icc 2 L, k.totient := by
  calc
    (reduced L).card = ∑ k ∈ Icc 2 L, ((reduced L).filter (fun z => z.1 + z.2 = k)).card := by
      apply card_eq_sum_card_fiberwise (f := fun z : ℕ × ℕ => z.1 + z.2)
      intro z hz
      obtain ⟨a,b,cap⟩ := mem_cells.mp (mem_filter.mp hz).1
      exact mem_Icc.mpr ⟨by change 2 ≤ z.1 + z.2; omega,cap⟩
    _ = _ := sum_congr rfl (fun _ hk => fiber hk)


private theorem normalize_cell {L : ℕ} {z : ℕ × ℕ} (inside : z ∈ cells L) :
    ∃ w ∈ reduced L, z.1 * w.2 = w.1 * z.2 := by
  obtain ⟨i,j,cap⟩ := mem_cells.mp inside
  obtain ⟨w,hm,same⟩ := normalize (in_rect.mpr ⟨⟨i,le_rfl⟩,⟨j,le_rfl⟩⟩)
  obtain ⟨bounds,cop⟩ := mem_filter.mp hm
  obtain ⟨⟨a,b⟩,⟨c,d⟩⟩ := in_rect.mp bounds
  exact ⟨w,mem_filter.mpr ⟨mem_cells.mpr ⟨a,c,(Nat.add_le_add b d).trans cap⟩,cop⟩,same⟩

private theorem local_cover {n r L : ℕ} [NeZero n] [Fact r.Prime] (dv : r ∣ n)
    (large : 2 * (L*L) < r) (units : ∀ z ∈ cells L, z.2.Coprime n) :
    (covered r (menu n L)).card = (reduced L).card := by
  let f := fun z => (point r z)^2
  have box (z) (hz : z ∈ cells L) : z ∈ rectangle L L := (mem_filter.mp hz).1
  have cp (z) (hz : z ∈ cells L) := denom (box z hz) large
  have same : ((menu n L).image fun x : ℕ => (x : ZMod r)^2) = (reduced L).image f := by
    rw [menu,image_image]
    ext x
    constructor
    · intro h
      obtain ⟨z,hz,eqn⟩ := mem_image.mp h
      obtain ⟨w,hw,eqw⟩ := normalize_cell hz
      refine mem_image.mpr ⟨w,hw,?_⟩
      change (((point n z).val : ZMod r)^2) = x at eqn
      rwa [local_point dv z (units z hz), fraction_eq (cp z hz) (cp w (mem_filter.mp hw).1) eqw] at eqn
    · intro h
      obtain ⟨z,hz,rfl⟩ := mem_image.mp h
      have m := (mem_filter.mp hz).1
      refine mem_image.mpr ⟨z,m,?_⟩
      exact congrArg (fun y : ZMod r => y^2) (local_point dv z (units z m))
  have nz : (0 : ZMod r) ∉ (reduced L).image f := by
    intro h
    obtain ⟨z,hz,zero⟩ := mem_image.mp h
    have hm := (mem_filter.mp hz).1
    have swapped : (z.2,z.1) ∈ cells L := by
      obtain ⟨a,b,k⟩ := mem_cells.mp hm
      exact mem_cells.mpr ⟨b,a,(Nat.add_comm z.1 z.2) ▸ k⟩
    have unit : IsUnit (z.1 : ZMod r) := (ZMod.isUnit_iff_coprime ..).mpr (cp _ swapped)
    have clear := clear_point z (cp _ hm)
    rw [show point r z = 0 from sq_eq_zero_iff.mp zero,zero_mul] at clear
    exact (isUnit_iff_ne_zero.mp unit) clear.symm
  have inj : Set.InjOn f (reduced L) := by
    apply (square_injective large).mono
    intro z hz
    obtain ⟨h,cop⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨box _ h,cop⟩
  rw [covered,same,erase_eq_of_not_mem nz,card_image_of_injOn inj]

/-- When twice the enclosing square's area is below both primes, the optimal
target-aware shape success rate is exactly the totient count times the sum of
the reciprocal local group orders. -/
theorem exact_rate {p q L : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p ≠ q)
    (op : p ≠ 2) (oq : q ≠ 2) (pl : 2 * (L*L) < p) (ql : 2 * (L*L) < q) :
    rate (p*q) (menu (p*q) L) =
      ((∑ k ∈ Icc 2 L, k.totient : ℕ) : ℚ) * (1 / (p-1) + 1 / (q-1)) := by
  have unit z (hz : z ∈ cells L) : z.2.Coprime (p*q) :=
    (denom (mem_filter.mp hz).1 pl).mul_right (denom (mem_filter.mp hz).1 ql)
  rw [rate_eq diff op oq, local_cover (dvd_mul_right p q) pl unit,
    local_cover (dvd_mul_left q p) ql unit, reduced_count]
  ring

/-- Counting with repetitions gives the triangular number, for all budgets including zero. -/
theorem cell_count (L : ℕ) : (cells L).card = L * (L-1) / 2 := by
  rw [← Finset.sum_range_id]
  calc
    (cells L).card = ∑ k ∈ range L,
        ((cells L).filter (fun z => z.1 + z.2 - 1 = k)).card := by
      apply card_eq_sum_card_fiberwise (f := fun z : ℕ × ℕ => z.1 + z.2 - 1)
      intro z hz
      obtain ⟨a,b,cap⟩ := mem_cells.mp hz
      exact mem_range.mpr (by change z.1 + z.2 - 1 < L; omega)
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      have bound := mem_range.mp hk
      conv_rhs => rw [show k = (Icc 1 k).card by simp [Nat.card_Icc]]
      apply card_bij (fun z _ => z.1)
      · intro z hz
        obtain ⟨mem,eq⟩ := mem_filter.mp hz
        obtain ⟨a,b,cap⟩ := mem_cells.mp mem
        exact mem_Icc.mpr ⟨a,by omega⟩
      · intro z hz w hw eq
        obtain ⟨hz,s⟩ := mem_filter.mp hz
        obtain ⟨hw,t⟩ := mem_filter.mp hw
        obtain ⟨a,b,_⟩ := mem_cells.mp hz
        obtain ⟨c,d,_⟩ := mem_cells.mp hw
        exact Prod.ext eq (by omega)
      · intro i hi
        obtain ⟨lo,up⟩ := mem_Icc.mp hi
        refine ⟨(i,k+1-i),mem_filter.mpr ⟨mem_cells.mpr ?_,?_⟩,rfl⟩ <;> dsimp <;> omega

private theorem cover_le (p n L : ℕ) :
    (covered p (menu n L)).card ≤ L * (L-1) / 2 := by
  exact (card_le_card (erase_subset ..)).trans
    (card_image_le.trans (card_image_le.trans_eq (cell_count L)))

set_option exponentiation.threshold 1024 in
/-- Even choosing the shape freely after inspecting each target has negligible uniform
success when two 1024-bit factors meet a total prefix-list budget of 2^256. -/
theorem full_width {p q L : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p ≠ q)
    (po : 2^1023 ≤ p) (qo : 2^1023 ≤ q) (cap : L ≤ 2^256) :
    rate (p*q) (menu (p*q) L) < 1 / (2:ℚ)^511 := by
  have op : p≠2 := by intro h; rw [h] at po; norm_num at po
  have oq : q≠2 := by intro h; rw [h] at qo; norm_num at qo
  have triangle : L * (L-1) / 2 ≤ 2^255 * (2^256-1) :=
    (Nat.div_le_div_right (Nat.mul_le_mul cap (Nat.sub_le_sub_right cap 1))).trans_eq (by decide)
  have term (r : ℕ) (size : 2^1023 ≤ r) :
      ((covered r (menu (p*q) L)).card : ℚ) / (r-1) ≤
        ((2:ℚ)^255 * (2^256-1)) / (2^1023-1) := by
    apply div_le_div₀ (by positivity) _ (by norm_num) _
    · have bound := (cover_le r (p*q) L).trans triangle
      norm_num at bound ⊢
      exact_mod_cast bound
    · apply sub_le_sub_right
      exact_mod_cast size
  rw [rate_eq diff op oq]
  exact (add_le_add (term p po) (term q qo)).trans_lt (by norm_num)

end PrimeFactors.CircleMarkGridWorkBudget
