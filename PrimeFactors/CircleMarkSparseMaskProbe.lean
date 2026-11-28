import PrimeFactors.CircleMarkJacobiMask

/-! Squaring a set of positive coordinates below p identifies two different
coordinates modulo p precisely when they sum to p. The larger prime has no
collision when the sum of every two distinct coordinates is below q. -/
namespace PrimeFactors.CircleMarkSparseMaskProbe

open Finset CircleMarkJacobiMask CircleMarkTargetFrequency
open scoped Classical

/-- One orientation for every complementary pair. -/
noncomputable def pairs (p : ℕ) (C : Finset ℕ) : Finset (ℕ×ℕ) :=
  (C ×ˢ C).filter fun z => z.1<z.2 ∧ z.1+z.2=p

/-- The larger member of each complementary pair. -/
private noncomputable def repeats (p : ℕ) (C : Finset ℕ) : Finset ℕ :=
  C.filter fun x => ∃ y∈C, y<x ∧ y+x=p

private theorem count_repeats (p : ℕ) (C : Finset ℕ) : (pairs p C).card=(repeats p C).card := by
  apply card_bij (fun z _ => z.2)
  · intro z hz
    obtain ⟨mem,lt,eqn⟩ := mem_filter.mp hz
    obtain ⟨x,y⟩ := mem_product.mp mem
    exact mem_filter.mpr ⟨y,z.1,x,lt,eqn⟩
  · intro z hz w hw eqn
    have a := (mem_filter.mp hz).2.2
    have b := (mem_filter.mp hw).2.2
    exact Prod.ext (by omega) eqn
  · intro x hx
    obtain ⟨xc,y,yc,lt,eqn⟩ := mem_filter.mp hx
    exact ⟨(y,x),mem_filter.mpr ⟨mem_product.mpr ⟨yc,xc⟩,lt,eqn⟩,rfl⟩

/-- Equality of squared coordinates has exactly two possibilities inside
the positive representatives below the prime. -/
theorem square_eq {r x y : ℕ} [Fact r.Prime] (xp : 0<x) (xr : x<r) (yr : y<r) :
    (x:ZMod r)^2=(y:ZMod r)^2 ↔ x=y ∨ x+y=r := by
  rw [sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · rintro (eqn|eqn)
    · exact Or.inl (by simpa only [ZMod.val_natCast_of_lt xr,ZMod.val_natCast_of_lt yr] using congrArg ZMod.val eqn)
    · have zero : ((x+y:ℕ):ZMod r)=0 := by rw [Nat.cast_add,eqn,neg_add_cancel]
      exact Or.inr (Nat.eq_of_dvd_of_lt_two_mul (by omega) ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp zero) (by omega))
  · rintro (rfl|eqn)
    · exact Or.inl rfl
    · apply Or.inr
      apply eq_neg_of_add_eq_zero_left
      rw [←Nat.cast_add,eqn,ZMod.natCast_self]

private theorem all_nonzero {r : ℕ} [Fact r.Prime] (C : Finset ℕ) (coords : ∀x∈C, 0<x ∧ x<r) :
    covered r C=C.image (fun x : ℕ => (x:ZMod r)^2) := by
  apply erase_eq_of_not_mem
  intro zero
  obtain ⟨x,hx,eqn⟩ := mem_image.mp zero
  have val := congrArg ZMod.val (sq_eq_zero_iff.mp eqn)
  rw [ZMod.val_natCast_of_lt (coords x hx).2,ZMod.val_zero] at val
  exact (coords x hx).1.ne' val

private theorem smaller_count {p : ℕ} [Fact p.Prime] (C : Finset ℕ) (coords : ∀x∈C, 0<x ∧ x<p) :
    (covered p C).card=C.card-(pairs p C).card := by
  let R := repeats p C
  let f := fun x : ℕ => (x:ZMod p)^2
  have sub : C \ R ⊆ C := sdiff_subset
  have once : Set.InjOn f (C \ R : Finset ℕ) := by
    intro x hx y hy same
    have xc := sub hx
    have yc := sub hy
    rcases (square_eq (coords x xc).1 (coords x xc).2 (coords y yc).2).mp same with eqn|eqn
    · exact eqn
    · rcases lt_trichotomy x y with lt|eq|gt
      · exact False.elim ((mem_sdiff.mp hy).2 (mem_filter.mpr ⟨yc,x,xc,lt,eqn⟩))
      · exact eq
      · exact False.elim ((mem_sdiff.mp hx).2 (mem_filter.mpr ⟨xc,y,yc,gt,by omega⟩))
  have same_image : C.image f=(C \ R).image f := by
    apply Subset.antisymm _ (image_subset_image sub)
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    by_cases loss : x∈R
    · obtain ⟨_,y,yc,lt,sum⟩ := mem_filter.mp loss
      have before : y∉R := by
        rintro hy
        obtain ⟨_,w,_,wy,ws⟩ := mem_filter.mp hy
        omega
      refine mem_image.mpr ⟨y,mem_sdiff.mpr ⟨yc,before⟩,?_⟩
      exact (square_eq (coords y yc).1 (coords y yc).2 (coords x hx).2).mpr (Or.inr sum)
    · exact mem_image.mpr ⟨x,mem_sdiff.mpr ⟨hx,loss⟩,rfl⟩
  rw [all_nonzero C coords]
  change (C.image f).card=_
  rw [same_image,card_image_of_injOn once,card_sdiff (show R⊆C from filter_subset ..),count_repeats]

private theorem larger_count {q : ℕ} [Fact q.Prime] (C : Finset ℕ) (coords : ∀x∈C, 0<x ∧ x<q)
    (sumcap : ∀x∈C, ∀y∈C, x≠y → x+y<q) : (covered q C).card=C.card := by
  rw [all_nonzero C coords]
  apply card_image_of_injOn
  intro x hx y hy eqn
  rcases (square_eq (coords x hx).1 (coords x hx).2 (coords y hy).2).mp eqn with same|sum
  · exact same
  · by_contra ne
    exact (sumcap x hx y hy ne).ne sum

/-- The exact loss in the complete sum counts the unordered pairs summing
to the smaller prime, including empty and singleton menus. -/
theorem exact_sum {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (C : Finset ℕ) (coords : ∀x∈C, 0<x ∧ x<p)
    (sumcap : ∀x∈C, ∀y∈C, x≠y → x+y<q) :
    globalSum (p*q) (squareMask C)= ((C.card*(C.card-(pairs p C).card):ℕ):ℤ) := by
  rw [factorization order.ne,square_sum p op,square_sum q oq,smaller_count C coords,
    larger_count C (fun x hx => ⟨(coords x hx).1,(coords x hx).2.trans order⟩) sumcap,Nat.cast_mul]
  ring

/-- Falling below the collision-free square is equivalent to containing a
pair whose sum is p. An empty menu gives equality. -/
theorem detect {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (C : Finset ℕ) (coords : ∀x∈C, 0<x ∧ x<p)
    (sumcap : ∀x∈C, ∀y∈C, x≠y → x+y<q) :
    globalSum (p*q) (squareMask C)<(C.card:ℤ)^2 ↔ ∃x∈C, ∃y∈C, x<y ∧ x+y=p := by
  rw [exact_sum order op oq C coords sumcap]
  constructor
  · intro small
    have non : (pairs p C).Nonempty := by
      by_contra empty
      rw [not_nonempty_iff_eq_empty.mp empty,card_empty,Nat.sub_zero,Nat.cast_mul,←sq] at small
      exact lt_irrefl _ small
    obtain ⟨z,mem⟩ := non
    obtain ⟨inside,lt,hs⟩ := mem_filter.mp mem
    obtain ⟨hx,hy⟩ := mem_product.mp inside
    exact ⟨z.1,hx,z.2,hy,lt,hs⟩
  · rintro ⟨x,hx,y,hy,lt,sum⟩
    have pos := card_pos.mpr (show (pairs p C).Nonempty from
      ⟨(x,y),mem_filter.mpr ⟨mem_product.mpr ⟨hx,hy⟩,lt,sum⟩⟩)
    have cpos := card_pos.mpr (show C.Nonempty from ⟨x,hx⟩)
    rw [sq]
    exact_mod_cast Nat.mul_lt_mul_of_pos_left (Nat.sub_lt cpos pos) cpos

theorem gcd_witness {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (C : Finset ℕ) (coords : ∀x∈C, 0<x ∧ x<p)
    (sumcap : ∀x∈C, ∀y∈C, x≠y → x+y<q)
    (hit : globalSum (p*q) (squareMask C)<(C.card:ℤ)^2) :
    ∃x∈C, ∃y∈C, x<y ∧ (p*q).gcd (x+y)=p := by
  obtain ⟨x,hx,y,hy,lt,sum⟩ := (detect order op oq C coords sumcap).mp hit
  exact ⟨x,hx,y,hy,lt,by rw [sum,Nat.gcd_eq_right (dvd_mul_right ..)]⟩

/-- A cap on pair sums alone allows collisions from a difference of p.
Here 12−1=11, while the only pair sum is 13. -/
theorem sum_cap_only :
    1+12≤(11*19:ℕ).sqrt ∧ (pairs 11 {1,12})=∅ ∧
      globalSum (11*19) (squareMask {1,12})=2 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  letI : Fact (Nat.Prime 19) := ⟨by decide⟩
  have a : (covered 11 {1,12}).card=1 := by decide +kernel
  have b : (covered 19 {1,12}).card=2 := by decide +kernel
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  rw [factorization (by decide : 11≠19),square_sum 11 (by decide),square_sum 19 (by decide),a,b]
  decide

end PrimeFactors.CircleMarkSparseMaskProbe
