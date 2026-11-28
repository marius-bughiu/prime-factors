import PrimeFactors.FullPopulationFavoredSums
import PrimeFactors.PrimeGridMass

/-! Partition the full balanced prime-pair population by modulus five and
by disjoint prime intervals (iW,(i+1)W] of width B/256. -/

open private PrimeFactors.FullPopulationFavoredSums.mem_eligible from PrimeFactors.FullPopulationFavoredSums

namespace PrimeFactors.SumGridPopulation

open Finset FullRangeResidueEstimates PrimeGridMass
open WideResiduePrimeSupply (B mem_band)
open PrimeProductRegion (K)
open MixedPrefixSample (eligible)
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

def W : ℕ := 2^1016
abbrev Label := ℕ×ℕ
noncomputable def grid : Finset Label := Ico 128 256 ×ˢ Ico 128 256
noncomputable def possible := grid.filter (fun ij => ij.1≤ ij.2 ∧ 256^2<2*(ij.1+1)*(ij.2+1))
noncomputable def full := grid.filter (fun ij => ij.1< ij.2 ∧ 256^2≤2*ij.1*ij.2)

private def mate (f : Bool) (a : ZMod 5) := if f then a else -a

/-- Equal factor residues form the favored group. The other square-unit
products have opposite factor residues. -/
noncomputable def group (f : Bool) : Finset (ℕ×ℕ) := eligible.filter
  (fun v => (v.2 : ZMod 5)=mate f v.1)

def index (v : ℕ×ℕ) : Label := ((v.1-1)/W,(v.2-1)/W)
noncomputable def tile (f : Bool) (ij : Label) := (group f).filter (fun v => index v=ij)

theorem width_positive : 0<W := by decide +kernel
theorem left_edge : 128*W=X := by decide +kernel
theorem right_edge : 256*W=B := by decide +kernel
private theorem threshold : 256^2*W^2=2*K := by decide +kernel

attribute [local irreducible] W eligible group tile grid possible full

theorem eligible_data {p q : ℕ} : (p,q)∈eligible ↔ X≤p ∧ p<q ∧ q<B ∧
    p.Prime ∧ q.Prime ∧ K≤p*q := PrimeFactors.FullPopulationFavoredSums.mem_eligible

private theorem mate_iff (f : Bool) (p q : ℕ) : (q:ZMod 5)=mate f p ↔
    if f then p%5=q%5 else (p%5+q%5)%5=0 := by
  cases f with
  | false =>
    change (q:ZMod 5)= -(p:ZMod 5) ↔ _
    have h : (q:ZMod 5)= -(p:ZMod 5) ↔ ((p+q:ℕ):ZMod 5)=0 := by
      rw [Nat.cast_add,add_comm,eq_neg_iff_add_eq_zero]
    rw [h,ZMod.natCast_zmod_eq_zero_iff_dvd,Nat.dvd_iff_mod_eq_zero,Nat.add_mod]
    rfl
  | true =>
    change (q:ZMod 5)=(p:ZMod 5) ↔ p%5=q%5
    rw [ZMod.natCast_eq_natCast_iff]
    exact eq_comm

theorem mem_group {f p q} : (p,q)∈group f ↔ (p,q)∈eligible ∧
    (if f then p%5=q%5 else (p%5+q%5)%5=0) := by
  rw [group,mem_filter,mate_iff]

private theorem prime_unit {p : ℕ} (lo : X≤p) (pp : p.Prime) : p%5≠0 := by
  intro h
  have eq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) pp).mp (Nat.dvd_of_mod_eq_zero h)
  exact ((by decide : 5<X).trans_le lo).ne eq

private theorem signs {p q : ℕ} (ok : (p,q)∈eligible) :
    ((p%5=q%5 ∨ (p%5+q%5)%5=0) ↔ (p*q)%5=1 ∨ (p*q)%5=4) ∧
    ¬(p%5=q%5 ∧ (p%5+q%5)%5=0) := by
  obtain ⟨lo,ord,_,pp,qp,_⟩ := eligible_data.mp ok
  have table : ∀ a b : Fin 5, a.val≠0 → b.val≠0 →
      ((a.val=b.val ∨ (a.val+b.val)%5=0) ↔ (a.val*b.val)%5=1 ∨ (a.val*b.val)%5=4) ∧
      ¬(a.val=b.val ∧ (a.val+b.val)%5=0) := by decide
  rw [Nat.mul_mod]
  exact table ⟨p%5,Nat.mod_lt _ (by decide)⟩ ⟨q%5,Nat.mod_lt _ (by decide)⟩
    (prime_unit lo pp) (prime_unit (lo.trans ord.le) qp)

theorem group_union : group true ∪ group false =
    eligible.filter (fun v => (v.1*v.2)%5=1 ∨ (v.1*v.2)%5=4) := by
  ext ⟨p,q⟩
  simp only [mem_union,mem_group,mem_filter,if_true,if_false,Bool.false_eq_true]
  by_cases h : (p,q)∈eligible
  · simpa only [h,true_and] using (signs h).1
  · simp [h]

theorem groups_disjoint : Disjoint (group true) (group false) := by
  apply disjoint_left.mpr
  rintro ⟨p,q⟩ a b
  obtain ⟨ok,one⟩ := mem_group.mp a
  exact (signs ok).2 ⟨one,(mem_group.mp b).2⟩

private theorem bin_index {p i : ℕ} (pos : 0<p) :
    (p-1)/W=i ↔ i*W<p ∧ p≤(i+1)*W := by
  rw [Nat.div_eq_iff width_positive,Nat.succ_mul]
  have := width_positive
  omega

theorem tile_subset (f : Bool) (ij : Label) : tile f ij⊆group f := by
  rw [tile]; exact filter_subset ..

/-- The conventions at the left and right endpoints assign each prime
to precisely one index, including at the boundaries of partial tiles. -/
theorem mem_tile {f p q i j} : (p,q)∈tile f (i,j) ↔ (p,q)∈group f ∧
    i*W<p ∧ p≤(i+1)*W ∧ j*W<q ∧ q≤(j+1)*W := by
  rw [tile,mem_filter]
  constructor
  · rintro ⟨ok,eq⟩
    obtain ⟨_,_,_,pp,qp,_⟩ := eligible_data.mp (mem_group.mp ok).1
    obtain ⟨x,y⟩ := Prod.mk.inj (show ((p-1)/W,(q-1)/W)=(i,j) from eq)
    obtain ⟨lp,hp⟩ := (bin_index pp.pos).mp x
    exact ⟨ok,lp,hp,(bin_index qp.pos).mp y⟩
  · rintro ⟨ok,a,b,c,d⟩
    exact ⟨ok,Prod.ext ((bin_index (by omega)).mpr ⟨a,b⟩) ((bin_index (by omega)).mpr ⟨c,d⟩)⟩

private theorem strict_left {p : ℕ} (lo : X≤p) (pp : p.Prime) : X<p := by
  have ne : p≠X := fun eq => (Nat.Prime.not_prime_pow (by decide : 2≤1023) (x:=2)) ((congrArg Nat.Prime eq).mp pp)
  exact lo.lt_of_ne ne.symm

private theorem strict_right {p : ℕ} (top : p≤B) (pp : p.Prime) : p<B := by
  have ne : p≠B := fun eq => (Nat.Prime.not_prime_pow (by decide : 2≤1024) (x:=2)) ((congrArg Nat.Prime eq).mp pp)
  exact top.lt_of_ne ne

private theorem box_index {p : ℕ} (lo : X<p) (hi : p≤B) : (p-1)/W∈Ico 128 256 := by
  apply mem_Ico.mpr
  constructor
  · apply (Nat.le_div_iff_mul_le width_positive).mpr
    rw [left_edge]; omega
  · apply (Nat.div_lt_iff_lt_mul width_positive).mpr
    rw [right_edge]; have := (by decide : 0<B); omega

theorem index_possible {p q : ℕ} (ok : (p,q)∈eligible) : index (p,q)∈possible := by
  obtain ⟨lo,pq,hi,pp,qp,mass⟩ := eligible_data.mp ok
  have lo' := strict_left lo pp
  have odd := Nat.odd_iff.mp ((pp.odd_of_ne_two ((by decide : 2<X).trans lo').ne').mul
    (qp.odd_of_ne_two (((by decide : 2<X).trans lo').trans pq).ne'))
  have strict : K<p*q := mass.lt_of_ne (fun eq => (by decide : K%2≠1) (eq ▸ odd))
  let i := (p-1)/W
  let j := (q-1)/W
  have up₁ := ((bin_index pp.pos).mp (rfl : (p-1)/W=i)).2
  have up₂ := ((bin_index qp.pos).mp (rfl : (q-1)/W=j)).2
  have place : 256^2*W^2 < (2*(i+1)*(j+1))*W^2 := by
    calc
      _ = 2*K := threshold
      _ < 2*(p*q) := by omega
      _ ≤ 2*(((i+1)*W)*((j+1)*W)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul up₁ up₂)
      _ = _ := by ring
  rw [possible,mem_filter,grid,mem_product]
  exact ⟨⟨box_index lo' (pq.trans hi).le,box_index (lo'.trans pq) hi.le⟩,
    Nat.div_le_div_right (Nat.sub_le_sub_right pq.le 1),Nat.lt_of_mul_lt_mul_right place⟩

/-- Each eligible group member lies in exactly one of the possible tiles. -/
theorem unique_tile {f : Bool} {v : ℕ×ℕ} (ok : v∈group f) :
    ∃! ij : Label, ij∈possible ∧ v∈tile f ij := by
  refine ⟨index v,⟨index_possible (mem_group.mp ok).1,?_⟩,?_⟩
  · rw [tile,mem_filter]
    exact ⟨ok,rfl⟩
  · rintro ij ⟨_,mem⟩
    rw [tile,mem_filter] at mem
    exact mem.2.symm

theorem full_subset_possible : full⊆possible := by
  intro ij h
  obtain ⟨gr,lt,low⟩ := mem_filter.mp (show ij∈grid.filter _ by simpa only [full] using h)
  rw [possible,mem_filter]
  exact ⟨gr,lt.le,by nlinarith only [low,Nat.zero_le ij.1,Nat.zero_le ij.2]⟩

/-- Sums of arbitrary signed real weights can be split into the possible
tiles. Boundary tiles retain their actual eligible pairs. -/
theorem sum_tiles (f : Bool) (g : ℕ×ℕ → ℝ) :
    ∑ v∈group f,g v = ∑ ij∈possible, ∑ v∈tile f ij,g v := by
  have mapped (v : ℕ×ℕ) (hv : v∈group f) : index v∈possible :=
    index_possible (mem_group.mp hv).1
  simpa only [tile] using (sum_fiberwise_of_maps_to mapped g).symm

private noncomputable def units : Finset (ZMod 5) := univ.erase 0
private theorem units_card : units.card=4 := by decide +kernel

/-- The full rectangle for a unit first residue and its designated second
residue. On a boundary tile this includes pairs outside the population. -/
noncomputable def rectangle (f : Bool) (ij : Label) (a : ZMod 5) :=
  fiveBin a (ij.1*W) W ×ˢ fiveBin (mate f a) (ij.2*W) W

private theorem bin_mem {p i : ℕ} {a : ZMod 5} :
    p∈fiveBin a (i*W) W ↔ p.Prime ∧ (p : ZMod 5)=a ∧ i*W<p ∧ p≤(i+1)*W := by
  rw [mem_band,Nat.succ_mul]
  have rem : p%5=a.val ↔ (p:ZMod 5)=a := by
    rw [←ZMod.val_natCast 5 p]; exact ⟨fun h => ZMod.val_injective 5 h,congrArg ZMod.val⟩
  rw [rem]

private theorem limits {i : ℕ} (x : i∈Ico 128 256) : X≤ i*W ∧ i*W+W≤B := by
  obtain ⟨left,right⟩ := mem_Ico.mp x
  rw [←left_edge,←right_edge,←Nat.succ_mul]
  exact ⟨Nat.mul_le_mul_right _ left,Nat.mul_le_mul_right _ right⟩

private theorem bins {li : ℕ → ℝ} (h : FiveEndpoints li) {i : ℕ} (ok : i∈Ico 128 256)
    (a : ZMod 5) (unit : IsUnit a) :
    W/2851≤(fiveBin a (i*W) W).card ∧ (fiveBin a (i*W) W).card≤W/2826 :=
  bmor_five_bin h Mesh.grid256 (limits ok).1 (limits ok).2 right_edge.ge a unit

/-- Every prime pair in an off-diagonal full rectangle already meets the
ordering and full 2,048-bit product threshold. -/
theorem full_rectangle {ij : Label} (fullCell : ij∈full) (f : Bool) (a : ZMod 5) :
    rectangle f ij a ⊆ tile f ij := by
  obtain ⟨i,j⟩ := ij
  obtain ⟨gr,ord,minProd⟩ := mem_filter.mp (show (i,j)∈grid.filter _ by simpa only [full] using fullCell)
  obtain ⟨ib,jb⟩ := mem_product.mp (show (i,j)∈Ico 128 256 ×ˢ Ico 128 256 by simpa only [grid] using gr)
  rintro ⟨p,q⟩ hv
  obtain ⟨fp,fq⟩ := mem_product.mp hv
  obtain ⟨pp,hp,lp,up⟩ := bin_mem.mp fp
  obtain ⟨qp,hq,lq,uq⟩ := bin_mem.mp fq
  have lower : X≤p := (limits ib).1.trans lp.le
  have order : p<q := (up.trans (Nat.mul_le_mul_right _ ord)).trans_lt lq
  have high : q<B := strict_right (uq.trans (by simpa only [Nat.succ_mul] using (limits jb).2)) qp
  have mass : K≤p*q := by
    have product : 2*K≤2*(p*q) := calc
      _ = 256^2*W^2 := threshold.symm
      _ ≤ (2*i*j)*W^2 := Nat.mul_le_mul_right _ minProd
      _ = 2*((i*W)*(j*W)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul lp.le lq.le)
    omega
  apply mem_tile.mpr
  refine ⟨?_,lp,up,lq,uq⟩
  rw [group,mem_filter]
  exact ⟨eligible_data.mpr ⟨lower,order,high,pp,qp,mass⟩,by simpa only [hp] using hq⟩

private noncomputable def firstFiber (S : Finset (ℕ×ℕ)) (a : ZMod 5) :=
  S.filter (fun v => (v.1 : ZMod 5)=a)

private noncomputable abbrev fiber (f : Bool) (ij : Label) := firstFiber (tile f ij)

private theorem fiber_subset (f : Bool) (ij : Label) (a : ZMod 5) :
    fiber f ij a⊆rectangle f ij a := by
  obtain ⟨i,j⟩ := ij
  rintro ⟨p,q⟩ hv
  obtain ⟨ok,rep⟩ := mem_filter.mp hv
  obtain ⟨g,pl,ph,ql,qh⟩ := mem_tile.mp ok
  obtain ⟨elig,eq⟩ := mem_filter.mp (show (p,q)∈eligible.filter _ by simpa only [group] using g)
  obtain ⟨_,_,_,pp,qp,_⟩ := eligible_data.mp elig
  have mateEq : (q:ZMod 5)=mate f a := by change (q:ZMod 5)=mate f p at eq; rwa [←rep]
  exact mem_product.mpr ⟨bin_mem.mpr ⟨pp,rep,pl,ph⟩,bin_mem.mpr ⟨qp,mateEq,ql,qh⟩⟩

private theorem first_unit {p q : ℕ} (ok : (p,q)∈eligible) : (p : ZMod 5)∈units := by
  obtain ⟨lo,_,_,pp,_,_⟩ := eligible_data.mp ok
  apply mem_erase.mpr
  exact ⟨(ZMod.natCast_zmod_eq_zero_iff_dvd p 5).mp.mt
    (fun div => prime_unit lo pp (Nat.dvd_iff_mod_eq_zero.mp div)),mem_univ _⟩

private theorem fiber_card (S : Finset (ℕ×ℕ)) (maps : ∀ v∈S, (v.1 : ZMod 5)∈units) :
    S.card=∑ a∈units,(firstFiber S a).card :=
  card_eq_sum_card_fiberwise (s:=S) (t:=units) (f:=fun v : ℕ×ℕ => (v.1 : ZMod 5)) maps

private theorem tile_unit (f : Bool) (ij : Label) (v : ℕ×ℕ) (ok : v∈tile f ij) :
    (v.1 : ZMod 5)∈units :=
  first_unit (mem_group.mp (tile_subset f ij ok)).1

private theorem fiber_total (f : Bool) (ij : Label) :
    (tile f ij).card=∑ a∈units,(firstFiber (tile f ij) a).card :=
  fiber_card (tile f ij) (tile_unit f ij)

private theorem rectangle_bounds {li : ℕ → ℝ} (h : FiveEndpoints li) {ij : Label} (gr : ij∈grid)
    (f : Bool) {a : ZMod 5} (ha : a∈units) :
    (W/2851)^2≤(rectangle f ij a).card ∧ (rectangle f ij a).card≤(W/2826)^2 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have unit : IsUnit a := isUnit_iff_ne_zero.mpr (mem_erase.mp ha).1
  have partner : IsUnit (mate f a) := by cases f <;> first | exact unit.neg | exact unit
  obtain ⟨i,j⟩ := mem_product.mp (show ij∈Ico 128 256 ×ˢ Ico 128 256 by simpa only [grid] using gr)
  rw [rectangle,card_product,pow_two,pow_two]
  exact ⟨Nat.mul_le_mul (bins h i a unit).1 (bins h j _ partner).1,
    Nat.mul_le_mul (bins h i a unit).2 (bins h j _ partner).2⟩

theorem tile_upper {li : ℕ → ℝ} (h : FiveEndpoints li) (f : Bool) {ij : Label} (ok : ij∈possible) :
    (tile f ij).card≤4*(W/2826)^2 := by
  have gr := (mem_filter.mp (show ij∈grid.filter _ by simpa only [possible] using ok)).1
  rw [fiber_total]
  calc
    _ ≤ ∑ _a∈units,(W/2826)^2 := sum_le_sum (fun a ha =>
      (card_le_card (fiber_subset f ij a)).trans (rectangle_bounds h gr f ha).2)
    _ = _ := by rw [sum_const,smul_eq_mul,units_card]

theorem tile_lower_group {li : ℕ → ℝ} (h : FiveEndpoints li) (f : Bool) {ij : Label} (ok : ij∈full) :
    4*(W/2851)^2≤(tile f ij).card := by
  have gr := (mem_filter.mp (show ij∈grid.filter _ by simpa only [full] using ok)).1
  rw [fiber_total]
  calc
    _ = ∑ _a∈units,(W/2851)^2 := by rw [sum_const,smul_eq_mul,units_card]
    _ ≤ _ := by
      apply sum_le_sum
      intro a ha
      apply (rectangle_bounds h gr f ha).1.trans
      apply card_le_card
      intro v hv
      exact mem_filter.mpr ⟨full_rectangle ok f a hv,(bin_mem.mp (mem_product.mp hv).1).2.1⟩

theorem tile_lower {li : ℕ → ℝ} (h : FiveEndpoints li) {ij : Label} (ok : ij∈full) :
    4*(W/2851)^2≤(tile true ij).card := tile_lower_group h true ok

end PrimeFactors.SumGridPopulation
