import PrimeFactors.MeanSumOrderWork
import PrimeFactors.ProductSelectedQuarticDenominators

/-! Cost in scheduled denominators, before an early successful return, over
the uniform population of eligible distinct prime pairs. The analytic input
is the published unconditional residue-class estimate packaged by FiveEndpoints. -/
namespace PrimeFactors.QuarticGatePopulation

open Finset
open SumGridPopulation (W Label grid possible full index eligible_data)
open MixedPrefixSample (eligible)
open PrimeGridMass (fiveBin FiveEndpoints)
open WideResiduePrimeSupply (B)
open PrimeProductRegion (K)
open private PrimeFactors.SumGridPopulation.bins PrimeFactors.SumGridPopulation.bin_mem
  PrimeFactors.SumGridPopulation.limits PrimeFactors.SumGridPopulation.prime_unit
  PrimeFactors.SumGridPopulation.strict_right PrimeFactors.SumGridPopulation.bin_index
  PrimeFactors.SumGridPopulation.threshold from PrimeFactors.SumGridPopulation
open private PrimeFactors.MeanSumOrderWork.full_sums PrimeFactors.MeanSumOrderWork.possible_sums
  from PrimeFactors.MeanSumOrderWork
open scoped Classical
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

attribute [local irreducible] eligible W

def scheduled (n : ℕ) : ℕ := 1 + (if 9*n<5*2^2048 then 1 else 0) + (if 3*n<2*2^2048 then 1 else 0)

private def skipped (n : ℕ) : ℕ := (if 5*2^2048≤9*n then 1 else 0) + (if 2*2^2048≤3*n then 1 else 0)

private theorem complement (n : ℕ) : scheduled n+skipped n=3 := by
  unfold scheduled skipped
  split_ifs <;> omega

private def credit (i j : ℕ) : ℕ := (if 5*256^2≤9*i*j then 1 else 0) + (if 2*256^2≤3*i*j then 1 else 0)

private noncomputable def bin (i : ℕ) := (Ioc (i*W) ((i+1)*W)).filter Nat.Prime
private noncomputable def cell (ij : Label) := eligible.filter (fun v => index v=ij)

private theorem in_bin {i p : ℕ} : p∈bin i ↔ p.Prime ∧ i*W<p ∧ p≤(i+1)*W := by
  simp only [bin,mem_filter,mem_Ioc]
  tauto

private theorem in_cell {i j p q : ℕ} :
    (p,q)∈cell (i,j) ↔ (p,q)∈eligible ∧ i*W<p ∧ p≤(i+1)*W ∧ j*W<q ∧ q≤(j+1)*W := by
  rw [cell,mem_filter]
  constructor
  · rintro ⟨ok,eq⟩
    obtain ⟨_,_,_,pp,qp,_⟩ := eligible_data.mp ok
    have a := (PrimeFactors.SumGridPopulation.bin_index pp.pos).mp (congrArg Prod.fst eq)
    have b := (PrimeFactors.SumGridPopulation.bin_index qp.pos).mp (congrArg Prod.snd eq)
    exact ⟨ok,a.1,a.2,b.1,b.2⟩
  · rintro ⟨ok,l,r,u,v⟩
    obtain ⟨_,_,_,pp,qp,_⟩ := eligible_data.mp ok
    exact ⟨ok,Prod.ext ((PrimeFactors.SumGridPopulation.bin_index pp.pos).mpr ⟨l,r⟩)
      ((PrimeFactors.SumGridPopulation.bin_index qp.pos).mpr ⟨u,v⟩)⟩

private theorem sum_cells (f : ℕ×ℕ → ℕ) :
    (∑ v∈eligible,f v) = ∑ ij∈possible, ∑ v∈cell ij,f v := by
  have mapped (v : ℕ×ℕ) (hv : v∈eligible) : index v∈possible := SumGridPopulation.index_possible hv
  simpa only [cell] using (sum_fiberwise_of_maps_to mapped f).symm

private theorem bin_size {li : ℕ → ℝ} (h : FiveEndpoints li) {i : ℕ} (ii : i∈Ico 128 256) :
    4*(W/2851)≤(bin i).card ∧ (bin i).card≤4*(W/2826) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let units := (univ : Finset (ZMod 5)).erase 0
  have count : units.card=4 := by decide +kernel
  have maps (p : ℕ) (hp : p∈bin i) : (p:ZMod 5)∈units := by
    obtain ⟨pp,pl,_⟩ := in_bin.mp hp
    have good := PrimeFactors.SumGridPopulation.prime_unit ((PrimeFactors.SumGridPopulation.limits ii).1.trans pl.le) pp
    exact mem_erase.mpr ⟨fun z => good (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp z)),mem_univ _⟩
  have fiber (a : ZMod 5) : (bin i).filter (fun p : ℕ => (p:ZMod 5)=a)=fiveBin a (i*W) W := by
    ext p
    rw [mem_filter,in_bin,PrimeFactors.SumGridPopulation.bin_mem]
    tauto
  have eq := card_eq_sum_card_fiberwise (s:=bin i) (t:=units) (f:=fun p : ℕ => (p:ZMod 5)) maps
  simp only [fiber] at eq
  have size (a : ZMod 5) (ha : a∈units) := PrimeFactors.SumGridPopulation.bins h ii a
    (isUnit_iff_ne_zero.mpr (mem_erase.mp ha).1)
  constructor
  · rw [eq]
    simpa only [sum_const,smul_eq_mul,count] using sum_le_sum (s:=units) (fun a ha => (size a ha).1)
  · rw [eq]
    simpa only [sum_const,smul_eq_mul,count] using sum_le_sum (s:=units) (fun a ha => (size a ha).2)

private theorem inside {i j : ℕ} : cell (i,j) ⊆ bin i ×ˢ bin j := by
  rintro ⟨p,q⟩ mem
  obtain ⟨ok,l,r,u,v⟩ := in_cell.mp mem
  obtain ⟨_,_,_,pp,qp,_⟩ := eligible_data.mp ok
  exact mem_product.mpr ⟨in_bin.mpr ⟨pp,l,r⟩,in_bin.mpr ⟨qp,u,v⟩⟩

private theorem grid_edges {i j : ℕ} (ij : (i,j)∈grid) : i∈Ico 128 256 ∧ j∈Ico 128 256 :=
  mem_product.mp ij

private theorem square_in {i j : ℕ} (ij : (i,j)∈full) : bin i ×ˢ bin j ⊆ cell (i,j) := by
  obtain ⟨gr,ord,prod⟩ := mem_filter.mp ij
  obtain ⟨ii,jj⟩ := grid_edges gr
  rintro ⟨p,q⟩ mem
  obtain ⟨bp,bq⟩ := mem_product.mp mem
  obtain ⟨pp,l,r⟩ := in_bin.mp bp
  obtain ⟨qp,u,v⟩ := in_bin.mp bq
  have low := (PrimeFactors.SumGridPopulation.limits ii).1.trans l.le
  have increasing : p<q := (r.trans (Nat.mul_le_mul_right W ord)).trans_lt u
  have top : q<B := PrimeFactors.SumGridPopulation.strict_right
    (v.trans (by simpa only [Nat.succ_mul] using (PrimeFactors.SumGridPopulation.limits jj).2)) qp
  have mass : K≤p*q := by
    have h : 2*K≤2*(p*q) := calc
      _ = 256^2*W^2 := PrimeFactors.SumGridPopulation.threshold.symm
      _ ≤ (2*i*j)*W^2 := Nat.mul_le_mul_right _ prod
      _ = 2*((i*W)*(j*W)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul l.le u.le)
    omega
  exact in_cell.mpr ⟨eligible_data.mpr ⟨low,increasing,top,pp,qp,mass⟩,l,r,u,v⟩

private theorem lower {li : ℕ → ℝ} (h : FiveEndpoints li) {ij : Label} (ok : ij∈full) :
    (4*(W/2851))^2≤(cell ij).card := by
  obtain ⟨i,j⟩ := ij
  obtain ⟨ii,jj⟩ := grid_edges (mem_filter.mp ok).1
  have inc := card_le_card (square_in ok)
  rw [card_product] at inc
  rw [pow_two]
  exact (Nat.mul_le_mul (bin_size h ii).1 (bin_size h jj).1).trans inc

private theorem upper {li : ℕ → ℝ} (h : FiveEndpoints li) {ij : Label} (ok : ij∈possible) :
    (cell ij).card≤(4*(W/2826))^2 := by
  obtain ⟨i,j⟩ := ij
  obtain ⟨ii,jj⟩ := grid_edges (mem_filter.mp ok).1
  have inc := card_le_card (inside (i:=i) (j:=j))
  rw [card_product] at inc
  exact inc.trans (by simpa only [pow_two] using Nat.mul_le_mul (bin_size h ii).2 (bin_size h jj).2)

private theorem gate_corner {k l i j p q : ℕ} (a : l*256^2≤k*i*j) (lowerP : i*W≤p) (lowerQ : j*W≤q) :
    l*2^2048≤k*(p*q) := calc
  _ = (l*256^2)*W^2 := by rw [mul_assoc,show 256^2*W^2=2^2048 by decide +kernel]
  _ ≤ (k*i*j)*W^2 := Nat.mul_le_mul_right _ a
  _ = k*((i*W)*(j*W)) := by ring
  _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul lowerP lowerQ)

private theorem credit_bound {ij v : Label} (mem : v∈cell ij) : credit ij.1 ij.2≤skipped (v.1*v.2) := by
  obtain ⟨i,j⟩ := ij
  obtain ⟨p,q⟩ := v
  obtain ⟨_,l,_,u,_⟩ := in_cell.mp mem
  have t : 5*256^2≤9*i*j → 5*2^2048≤9*(p*q) := fun h => gate_corner h l.le u.le
  have s : 2*256^2≤3*i*j → 2*2^2048≤3*(p*q) := fun h => gate_corner h l.le u.le
  dsimp only [credit,skipped]
  split_ifs <;> omega

set_option maxRecDepth 24000 in
private theorem grid_credit : MeanSumOrderGeometry.sumFull credit=5771 := by decide +kernel

attribute [local irreducible] cell bin possible full scheduled skipped credit

private theorem count_possible : possible.card=5124 := by
  have e := PrimeFactors.MeanSumOrderWork.possible_sums (fun _ _ => 1)
  simpa only [sum_const,smul_eq_mul,mul_one] using e.trans MeanSumOrderGeometry.grid_totals.2.2.2.2.2

private theorem count_credit : (∑ ij∈full,credit ij.1 ij.2)=5771 :=
  (PrimeFactors.MeanSumOrderWork.full_sums credit).trans grid_credit

private def lo : ℕ := (4*(W/2851))^2
private def hi : ℕ := (4*(W/2826))^2

private theorem mass_generic {α β : Type*} (S : Finset α) (T : Finset β) (C : β → Finset α)
    {k u : ℕ} (part : (∑ _x∈S,(1:ℕ))=∑ i∈T, ∑ _x∈C i,(1:ℕ))
    (bound : ∀ i∈T,(C i).card≤u) (number : T.card=k) : S.card≤k*u := by
  simp only [sum_const,smul_eq_mul,mul_one] at part
  rw [part]
  simpa only [sum_const,smul_eq_mul,number] using sum_le_sum bound

private theorem mass_bound {li : ℕ → ℝ} (h : FiveEndpoints li) : eligible.card≤5124*hi :=
  mass_generic eligible possible cell (sum_cells (fun _ => 1)) (fun _ ok => upper h ok) count_possible

private theorem gain_bound {li : ℕ → ℝ} (h : FiveEndpoints li) :
    5771*lo≤∑ v∈eligible,skipped (v.1*v.2) := calc
  _ = ∑ ij∈full,credit ij.1 ij.2*lo := by rw [←sum_mul,count_credit]
  _ ≤ ∑ ij∈full,∑ v∈cell ij,skipped (v.1*v.2) := by
    apply sum_le_sum
    intro ij ok
    calc
      _ ≤ credit ij.1 ij.2*(cell ij).card := Nat.mul_le_mul_left _ (lower h ok)
      _ = ∑ _v∈cell ij,credit ij.1 ij.2 := by rw [sum_const,smul_eq_mul,mul_comm]
      _ ≤ _ := sum_le_sum (fun _ mem => credit_bound mem)
  _ ≤ ∑ ij∈possible,∑ v∈cell ij,skipped (v.1*v.2) := sum_le_sum_of_subset SumGridPopulation.full_subset_possible
  _ = _ := (sum_cells (fun v => skipped (v.1*v.2))).symm

private theorem total (pairs : Finset (ℕ×ℕ)) :
    (∑ v∈pairs,scheduled (v.1*v.2))+(∑ v∈pairs,skipped (v.1*v.2))=pairs.card*3 := by
  rw [←sum_add_distrib]
  simp only [complement,sum_const,smul_eq_mul]

private theorem margin : 11*(5124*hi)<10*(5771*lo) := by decide +kernel

private theorem length_eq (n : ℕ) : (ProductSelectedQuarticDenominators.denominators n).length=scheduled n := by
  unfold ProductSelectedQuarticDenominators.denominators scheduled
  split_ifs <;> rfl

/-- Fewer than 1.90 scheduled denominator checks per eligible prime pair on
average, compared with three for the ungated menu. All entries selected by
the gates are charged even if an earlier entry would return the answer. -/
theorem average {li : ℕ → ℝ} (h : FiveEndpoints li) :
    10*(∑ v∈eligible,(ProductSelectedQuarticDenominators.denominators (v.1*v.2)).length) < 19*eligible.card := by
  simp only [length_eq]
  have m := mass_bound h
  have g := gain_bound h
  have r := margin
  have t := total eligible
  omega

end PrimeFactors.QuarticGatePopulation
