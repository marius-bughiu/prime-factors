import PrimeFactors.CircleMarkSparseMaskProbe

/-! Capacity of fixed binary probes that report membership in the distinct
odd pair sums of their coordinate menus. Candidates may be any odd integers
in the specified finite population. -/
namespace PrimeFactors.CircleMarkSparseMaskCapacity

open Finset CircleMarkSparseMaskProbe
open scoped Classical

/-- Form each possible odd sum by adding one even and one odd coordinate. -/
noncomputable def oddSums (C : Finset ℕ) : Finset ℕ :=
  ((C.filter Even) ×ˢ (C.filter Odd)).image (fun z => z.1+z.2)

theorem mem_oddSums {C : Finset ℕ} {s : ℕ} :
    s∈oddSums C ↔ Odd s ∧ (pairs s C).Nonempty := by
  constructor
  · intro hs
    obtain ⟨⟨x,y⟩,mem,rfl⟩ := mem_image.mp hs
    obtain ⟨xc,xe⟩ := mem_filter.mp (mem_product.mp mem).1
    obtain ⟨yc,yo⟩ := mem_filter.mp (mem_product.mp mem).2
    refine ⟨xe.add_odd yo,?_⟩
    have ne : x≠y := fun e => (Nat.not_even_iff_odd.mpr yo) (e ▸ xe)
    rcases lt_or_gt_of_ne ne with lt|gt
    · exact ⟨(x,y),mem_filter.mpr ⟨mem_product.mpr ⟨xc,yc⟩,lt,rfl⟩⟩
    · exact ⟨(y,x),mem_filter.mpr ⟨mem_product.mpr ⟨yc,xc⟩,gt,Nat.add_comm ..⟩⟩
  · rintro ⟨odd,z,hz⟩
    obtain ⟨m,_,sum⟩ := mem_filter.mp hz
    obtain ⟨xc,yc⟩ := mem_product.mp m
    have parity := Nat.odd_iff.mp odd
    by_cases xe : Even z.1
    · have ye : Odd z.2 := by rw [Nat.odd_iff]; have := Nat.even_iff.mp xe; omega
      exact mem_image.mpr ⟨z,mem_product.mpr ⟨mem_filter.mpr ⟨xc,xe⟩,mem_filter.mpr ⟨yc,ye⟩⟩,sum⟩
    · have xo := Nat.not_even_iff_odd.mp xe
      have ye : Even z.2 := by rw [Nat.even_iff]; have := Nat.odd_iff.mp xo; omega
      exact mem_image.mpr ⟨(z.2,z.1),mem_product.mpr ⟨mem_filter.mpr ⟨yc,ye⟩,mem_filter.mpr ⟨xc,xo⟩⟩,
        (Nat.add_comm ..).trans sum⟩

/-- The distinct odd pair sums are bounded first by the product of the
parity counts, then by the square of the menu size divided by four. -/
theorem menu_capacity (C : Finset ℕ) :
    (oddSums C).card≤(C.filter Even).card*(C.filter Odd).card ∧
      (C.filter Even).card*(C.filter Odd).card≤C.card^2/4 := by
  refine ⟨card_image_le.trans_eq (card_product ..),?_⟩
  let e := (C.filter Even).card
  let o := (C.filter Odd).card
  have part : e+o=C.card := by
    simpa only [e,o,Nat.not_even_iff_odd] using filter_card_add_filter_neg_card_eq_card (s:=C) Even
  change e*o≤C.card^2/4
  apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
  rw [←part]
  exact_mod_cast (show (e:ℤ)*o*4≤((e:ℤ)+o)^2 by nlinarith only [sq_nonneg ((e:ℤ)-o)])

/-- Which of the fixed menus report this candidate. -/
noncomputable def answers {B : ℕ} (M : Fin B → Finset ℕ) (s : ℕ) : Finset (Fin B) :=
  univ.filter fun i => s∈oddSums (M i)

/-- For distinguishable candidates, at most one can have no positive report.
Each menu contributes at most its own capacity. -/
theorem candidate_count {B : ℕ} (C : Finset ℕ) (M : Fin B → Finset ℕ)
    (unique : Set.InjOn (answers M) C) :
    C.card≤1+∑ i : Fin B, (M i).card^2/4 := by
  let U := univ.biUnion (fun i => oddSums (M i))
  have blind {s : ℕ} (out : s∉U) : answers M s=∅ := by
    apply eq_empty_of_forall_not_mem
    intro i hi
    exact out (mem_biUnion.mpr ⟨i,mem_univ _,(mem_filter.mp hi).2⟩)
  have lost : (C \ U).card≤1 := by
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨xc,xo⟩ := mem_sdiff.mp hx
    obtain ⟨yc,yo⟩ := mem_sdiff.mp hy
    exact unique xc yc ((blind xo).trans (blind yo).symm)
  have cover : U.card≤∑ i : Fin B, (M i).card^2/4 :=
    card_biUnion_le.trans (sum_le_sum (fun i _ => (menu_capacity _).1.trans (menu_capacity (M i)).2))
  exact (card_le_card_sdiff_add_card (s:=C) (t:=U)).trans (Nat.add_le_add lost cover)

/-- B fixed membership bits with menus of at most d coordinates cannot
distinguish a population of W candidates unless 4(W−1) ≤ B*d². -/
theorem fixed_budget {B d : ℕ} (C : Finset ℕ) (M : Fin B → Finset ℕ)
    (limit : ∀i, (M i).card≤d) (unique : Set.InjOn (answers M) C) :
    4*(C.card-1)≤B*d^2 := by
  have ceil := candidate_count C M unique
  have cap : ∑ i : Fin B, (M i).card^2/4 ≤ B*(d^2/4) := by
    simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using
      sum_le_sum (s:=univ) (fun i _ => Nat.div_le_div_right (Nat.pow_le_pow_left (limit i) 2) (c:=4))
  have n : C.card-1≤B*(d^2/4) := by omega
  calc _ ≤ 4*(B*(d^2/4)) := Nat.mul_le_mul_left 4 n
       _ = B*((d^2/4)*4) := by ring
       _ ≤ _ := Nat.mul_le_mul_left _ (Nat.div_mul_le_self ..)

/-- The parity-product bound is sharp for every even menu size. The even
coordinates encode a remainder and the odd ones encode its quotient. -/
theorem sharp_even (m : ℕ) : ∃ C : Finset ℕ, C.card=2*m ∧ (oddSums C).card=m^2 := by
  let e (i : ℕ) := 2*i+2
  let o (j : ℕ) := 2*((m+1)*j)+1
  let E := (range m).image e
  let O := (range m).image o
  let C := E∪O
  have ep (x : ℕ) (h : x∈E) : Even x := by
    obtain ⟨i,_,rfl⟩ := mem_image.mp h
    exact ⟨i+1,by dsimp [e]; omega⟩
  have op (x : ℕ) (h : x∈O) : Odd x := by
    obtain ⟨j,_,rfl⟩ := mem_image.mp h
    exact ⟨(m+1)*j,rfl⟩
  have disjoint : Disjoint E O := disjoint_left.mpr (fun _ h k => (Nat.not_even_iff_odd.mpr (op _ k)) (ep _ h))
  have ec : E.card=m := by
    rw [show E.card=(range m).card from card_image_of_injective _ (fun _ _ h => by dsimp [e] at h; omega),card_range]
  have oc : O.card=m := by
    have inj : Function.Injective o := by
      intro i j h
      dsimp [o] at h
      exact Nat.mul_left_cancel (by omega : 0<m+1) (by omega)
    rw [show O.card=(range m).card from card_image_of_injective _ inj,card_range]
  have size : C.card=2*m := by rw [card_union_of_disjoint disjoint,ec,oc]; omega
  let f (z : ℕ×ℕ) := e z.1+o z.2
  let box := range m ×ˢ range m
  have inj : Set.InjOn f box := by
    intro z hz w hw eqn
    obtain ⟨zi,_⟩ := mem_product.mp hz
    obtain ⟨wi,_⟩ := mem_product.mp hw
    have zl : z.1<m+1 := (mem_range.mp zi).trans (Nat.lt_succ_self _)
    have wl : w.1<m+1 := (mem_range.mp wi).trans (Nat.lt_succ_self _)
    have s : z.1+(m+1)*z.2=w.1+(m+1)*w.2 := by dsimp [f,e,o] at eqn; omega
    have r := congrArg (fun x : ℕ => x%(m+1)) s
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt zl,Nat.mod_eq_of_lt wl] at r
    exact Prod.ext r (Nat.mul_left_cancel (by omega : 0<m+1) (by omega))
  have subset : box.image f ⊆ oddSums C := by
    intro z hz
    obtain ⟨⟨i,j⟩,mem,rfl⟩ := mem_image.mp hz
    obtain ⟨im,jm⟩ := mem_product.mp mem
    have em : e i∈E := mem_image.mpr ⟨i,im,rfl⟩
    have om : o j∈O := mem_image.mpr ⟨j,jm,rfl⟩
    exact mem_image.mpr ⟨(e i,o j),mem_product.mpr ⟨mem_filter.mpr ⟨mem_union_left _ em,ep _ em⟩,
      mem_filter.mpr ⟨mem_union_right _ om,op _ om⟩⟩,rfl⟩
  have lower := card_le_card subset
  rw [card_image_of_injOn inj,show box.card=m*m by simp [box]] at lower
  have upper := (menu_capacity C).1.trans (menu_capacity C).2
  rw [size,mul_pow,show 2^2=4 by decide,Nat.mul_div_cancel_left _ (by decide : 0<4)] at upper
  exact ⟨C,size,le_antisymm upper (by simpa only [sq] using lower)⟩

end PrimeFactors.CircleMarkSparseMaskCapacity
