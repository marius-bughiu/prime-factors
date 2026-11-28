import PrimeFactors.SumGridPopulation

/-! The two nonsquare product residues modulo five complete the grid
partition of the eligible balanced prime pairs. Each such grid tile is
contained in eight ordered rectangles of prime residue classes. -/

open private PrimeFactors.SumGridPopulation.prime_unit PrimeFactors.SumGridPopulation.bin_mem
  PrimeFactors.SumGridPopulation.bin_index PrimeFactors.SumGridPopulation.bins
  from PrimeFactors.SumGridPopulation

namespace PrimeFactors.OtherSumGridPopulation

open Finset PrimeGridMass
open SumGridPopulation (W Label grid possible index group)
open MixedPrefixSample (eligible)
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

noncomputable def other : Finset (ℕ×ℕ) := eligible.filter fun v =>
  (v.1*v.2)%5=2 ∨ (v.1*v.2)%5=3

noncomputable def tile (ij : Label) := other.filter (fun v => index v=ij)

theorem mem_other {p q : ℕ} : (p,q)∈other ↔ (p,q)∈eligible ∧
    ((p*q)%5=2 ∨ (p*q)%5=3) := by rw [other,mem_filter]

attribute [local irreducible] other tile eligible SumGridPopulation.grid SumGridPopulation.possible W

theorem other_disjoint : Disjoint (group true ∪ group false) other := by
  rw [SumGridPopulation.group_union]
  apply disjoint_left.mpr
  rintro ⟨p,q⟩ hs hn
  have s := (mem_filter.mp hs).2
  change (p*q)%5=1 ∨ (p*q)%5=4 at s
  have n := (mem_other.mp hn).2
  omega

/-- The two square-unit groups and the remaining products exhaust the
same canonical prime-pair population, including every permissible residue. -/
theorem all_groups : group true ∪ group false ∪ other=eligible := by
  rw [SumGridPopulation.group_union]
  ext ⟨p,q⟩
  simp only [mem_union,mem_filter,mem_other]
  constructor
  · rintro (⟨ok,_⟩|⟨ok,_⟩) <;> exact ok
  · intro ok
    obtain ⟨lo,order,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp ok
    have notdiv : ¬5∣p*q := by
      intro hit
      rcases (Nat.prime_five.dvd_mul.mp hit) with hp|hq
      · exact PrimeFactors.SumGridPopulation.prime_unit lo pp (Nat.dvd_iff_mod_eq_zero.mp hp)
      · exact PrimeFactors.SumGridPopulation.prime_unit (lo.trans order.le) qp (Nat.dvd_iff_mod_eq_zero.mp hq)
    have nz : (p*q)%5≠0 := notdiv.comp (Nat.dvd_iff_mod_eq_zero.mpr ·)
    have small := Nat.mod_lt (p*q) (by decide : 0<5)
    have values : ((p*q)%5=1 ∨ (p*q)%5=4) ∨ ((p*q)%5=2 ∨ (p*q)%5=3) := by omega
    exact values.elim (fun h => Or.inl ⟨ok,h⟩) (fun h => Or.inr ⟨ok,h⟩)

theorem tile_subset (ij : Label) : tile ij ⊆ other := by rw [tile]; exact filter_subset ..

theorem mem_tile {p q i j : ℕ} : (p,q)∈tile (i,j) ↔ (p,q)∈other ∧
    i*W<p ∧ p≤(i+1)*W ∧ j*W<q ∧ q≤(j+1)*W := by
  rw [tile,mem_filter]
  constructor
  · rintro ⟨ok,eq⟩
    obtain ⟨_,_,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp (mem_other.mp ok).1
    obtain ⟨x,y⟩ := Prod.mk.inj (show ((p-1)/W,(q-1)/W)=(i,j) from eq)
    obtain ⟨lp,hp⟩ := (PrimeFactors.SumGridPopulation.bin_index pp.pos).mp x
    exact ⟨ok,lp,hp,(PrimeFactors.SumGridPopulation.bin_index qp.pos).mp y⟩
  · rintro ⟨ok,l₁,u₁,l₂,u₂⟩
    exact ⟨ok,Prod.ext ((PrimeFactors.SumGridPopulation.bin_index (by omega)).mpr ⟨l₁,u₁⟩)
      ((PrimeFactors.SumGridPopulation.bin_index (by omega)).mpr ⟨l₂,u₂⟩)⟩

theorem sum_tiles (g : ℕ×ℕ → ℝ) : ∑ v∈other,g v = ∑ ij∈possible, ∑ v∈tile ij,g v := by
  have maps (v : ℕ×ℕ) (ok : v∈other) : index v∈possible :=
    SumGridPopulation.index_possible (mem_other.mp ok).1
  simpa only [tile] using (sum_fiberwise_of_maps_to maps g).symm

private abbrev Residue := ZMod 5 × ZMod 5
private noncomputable def labels : Finset Residue := univ.filter fun r => r.1*r.2=2 ∨ r.1*r.2=3
private theorem label_count : labels.card=8 := by decide +kernel
private def residue (v : ℕ×ℕ) : Residue := (v.1,v.2)

private theorem mapped (v : ℕ×ℕ) (ok : v∈other) : residue v∈labels := by
  obtain ⟨a,b⟩ := v
  have nz := (mem_other.mp ok).2
  have reduce (c : ℕ) (eq : (a*b)%5=c) : (a:ZMod 5)*(b:ZMod 5)=(c:ZMod 5) := by
    rw [←Nat.cast_mul,←eq,ZMod.natCast_mod]
  refine mem_filter.mpr ⟨mem_univ _,?_⟩
  rcases nz with h|h
  · exact Or.inl (reduce 2 h)
  · exact Or.inr (reduce 3 h)

private noncomputable def fiber (S : Finset (ℕ×ℕ)) (r : Residue) :=
  S.filter fun v => residue v=r

private theorem fiber_count (S : Finset (ℕ×ℕ)) (cover : ∀ v∈S, residue v∈labels) :
    S.card=∑ r∈labels,(fiber S r).card :=
  card_eq_sum_card_fiberwise (s:=S) (t:=labels) (f:=residue) cover

private theorem units_of_label {r : Residue} (ok : r∈labels) : IsUnit r.1 ∧ IsUnit r.2 := by
  have table : ∀ a b : ZMod 5, a*b=2 ∨ a*b=3 → a≠0 ∧ b≠0 := by decide
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨left,right⟩ := table r.1 r.2 (mem_filter.mp ok).2
  exact ⟨isUnit_iff_ne_zero.mpr left,isUnit_iff_ne_zero.mpr right⟩

private theorem fiber_upper {li : ℕ → ℝ} (h : FiveEndpoints li) {ij : Label} (cell : ij∈grid)
    {r : Residue} (ok : r∈labels) : (fiber (tile ij) r).card≤(W/2826)^2 := by
  obtain ⟨i,j⟩ := ij
  have ranges := mem_product.mp (show (i,j)∈Ico 128 256 ×ˢ Ico 128 256 by simpa only [SumGridPopulation.grid] using cell)
  have incl : fiber (tile (i,j)) r ⊆ fiveBin r.1 (i*W) W ×ˢ fiveBin r.2 (j*W) W := by
    rintro ⟨p,q⟩ member
    obtain ⟨inTile,reps⟩ := mem_filter.mp member
    obtain ⟨inOther,l₁,u₁,l₂,u₂⟩ := mem_tile.mp inTile
    obtain ⟨_,_,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp (mem_other.mp inOther).1
    have f : (p:ZMod 5)=r.1 := congrArg Prod.fst reps
    have s : (q:ZMod 5)=r.2 := congrArg Prod.snd reps
    exact mem_product.mpr ⟨PrimeFactors.SumGridPopulation.bin_mem.mpr ⟨pp,f,l₁,u₁⟩,
      PrimeFactors.SumGridPopulation.bin_mem.mpr ⟨qp,s,l₂,u₂⟩⟩
  have total := card_le_card incl
  rw [card_product] at total
  rw [pow_two]
  have us := units_of_label ok
  exact total.trans (Nat.mul_le_mul (PrimeFactors.SumGridPopulation.bins h ranges.1 _ us.1).2
    (PrimeFactors.SumGridPopulation.bins h ranges.2 _ us.2).2)

/-- Every possible nonsquare-product tile contains at most eight rectangles
at the upper prime-bin capacity. This includes partially filled tiles
and diagonal tiles, where ignoring the ordering gives an upper bound. -/
theorem tile_upper {li : ℕ → ℝ} (h : FiveEndpoints li) {ij : Label} (ok : ij∈possible) :
    (tile ij).card≤8*(W/2826)^2 := by
  have gr := (mem_filter.mp (show ij∈grid.filter _ by simpa only [SumGridPopulation.possible] using ok)).1
  rw [fiber_count (tile ij) (fun v hv => mapped _ (tile_subset ij hv))]
  calc
    _ ≤ ∑ _r∈labels,(W/2826)^2 := sum_le_sum (fun _ hr => fiber_upper h gr hr)
    _ = _ := by rw [sum_const,smul_eq_mul,label_count]

end PrimeFactors.OtherSumGridPopulation
