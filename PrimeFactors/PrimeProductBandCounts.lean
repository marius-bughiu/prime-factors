import PrimeFactors.FiveSquareAllPrimeRanks
import PrimeFactors.ProductIntervalCellSpread

/-! Exact counting by the leading product bits across all distinct pairs of
1,024-bit primes with a 2,048-bit product. A band includes its upper endpoint
and excludes its lower endpoint. The identities use only finite counts. -/

namespace PrimeFactors.PrimeProductBandCounts

open Finset PrimeResidueRankTransfer
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open PrimeProductRegion (K)
open MixedPrefixSample (eligible)
open ProductIntervalCellSpread (bandPairs band_count)
open private PrimeFactors.PrimeProductRegion.whole PrimeFactors.PrimeProductRegion.mem_whole
  PrimeFactors.PrimeProductRegion.mem_pool from PrimeFactors.PrimeProductRegion
open private PrimeFactors.FiveSquareAllPrimeRanks.weighted_twice
  PrimeFactors.FiveSquareAllPrimeRanks.regroup PrimeFactors.FiveSquareAllPrimeRanks.average_eq
  PrimeFactors.FiveSquareAllPrimeRanks.card_of_ones
  from PrimeFactors.FiveSquareAllPrimeRanks
open private PrimeFactors.ProductIntervalCellSpread.decreases from PrimeFactors.ProductIntervalCellSpread
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

abbrev Band (k : ℕ) := Fin (2^k)
def width (k : ℕ) := 2^(2047-k)
def edge (k i : ℕ) := K+i*width k

/-- On the product population the tag is the quotient of N−(K+1) by
the band width. The fallback makes the definition total outside the range. -/
noncomputable def tag (k N : ℕ) : Band k :=
  if h : (N-(K+1))/width k<2^k then ⟨(N-(K+1))/width k,h⟩ else ⟨0,by positivity⟩

private theorem width_pos (k : ℕ) : 0<width k := by unfold width; positivity
private theorem span {k : ℕ} (hk : k≤2047) : 2^k*width k=K := by
  rw [width,←pow_add,show k+(2047-k)=2047 by omega]

theorem first_edge (k : ℕ) : edge k 0=K := by simp [edge]
theorem last_edge {k : ℕ} (hk : k≤2047) : edge k (2^k)=B^2 := by
  rw [edge,span hk]
  decide +kernel

theorem edge_start (k i : ℕ) : K≤edge k i := Nat.le_add_right ..
theorem edge_step (k i : ℕ) : edge k i≤edge k (i+1) := by
  rw [edge,edge,Nat.add_mul,one_mul]; omega

private theorem div_eq {n i w : ℕ} (wp : 0<w) :
    n/w=i ↔ i*w≤n ∧ n<(i+1)*w := by
  have eq : (n / w = i) ↔ (i ≤ n / w ∧ (n / w) < i + 1) := by omega
  rwa [Nat.le_div_iff_mul_le wp,Nat.div_lt_iff_lt_mul wp] at eq

theorem tag_iff {k N : ℕ} (hk : k≤2047) (lo : K<N) (hi : N≤B^2) (i : Band k) :
    tag k N=i ↔ edge k i.val<N ∧ N≤edge k (i.val+1) := by
  have top : B^2=K+K := by decide +kernel
  have valid : (N-(K+1))/width k<2^k := (Nat.div_lt_iff_lt_mul (width_pos k)).mpr (by
    rw [span hk]; omega)
  rw [tag,dif_pos valid,Fin.ext_iff]
  change (N-(K+1))/width k=i.val ↔ _
  rw [div_eq (width_pos k)]
  unfold edge
  omega

/-- With at least one low bit below the band boundary, odd products
cannot lie on an even edge. The tag is then the usual next k high bits. -/
theorem leading_bits {k N : ℕ} (hk : k<2047) (odd : Odd N) (lo : K<N) (hi : N≤B^2) :
    (tag k N).val=(N/width k) % (2^k) := by
  let i := tag k N
  obtain ⟨left,right⟩ := (tag_iff hk.le lo hi i).mp rfl
  have evenWidth : 2∣width k := dvd_pow_self 2 (by omega : 2047-k≠0)
  have evenEdge : 2∣edge k (i.val+1) :=
    Nat.dvd_add (by decide +kernel : 2∣K) (dvd_mul_of_dvd_right evenWidth _)
  have strict := right.lt_of_ne (fun eq => by
    have h := Nat.odd_iff.mp odd
    rw [eq,Nat.mod_eq_zero_of_dvd evenEdge] at h
    contradiction)
  have block (j : ℕ) : (2^k+j)*width k=edge k j := by rw [Nat.add_mul,span hk.le,edge]
  have quotient : N/width k=2^k+i.val := (div_eq (width_pos k)).mpr ⟨by rw [block]; exact left.le,
    by rw [Nat.add_assoc,block]; exact strict⟩
  rw [quotient,Nat.add_mod_left,Nat.mod_eq_of_lt i.isLt]

variable {d : ℕ} [NeZero d]

/-- Ordered distinct-prime pairs in the specified residue classes and band. -/
noncomputable def count (k : ℕ) (i : Band k) (v : ZMod d×ZMod d) :=
  cell X B (edge k i.val) v-cell X B (edge k (i.val+1)) v

omit [NeZero d] in
theorem between (k : ℕ) (i : Band k) (v : ZMod d×ZMod d) :
    (bandPairs (edge k i.val) (edge k (i.val+1)) v).card=count k i v :=
  band_count v (edge_step k i.val)

private theorem above_empty (b : ℕ) (A C : Finset ℕ)
    (ha : ∀ a∈A,a≤b) (hc : ∀ c∈C,c≤b) :
    ThresholdPairCount.distinctRegion (b^2) A C=∅ := by
  apply eq_empty_of_forall_not_mem
  rintro ⟨p,q⟩ hv
  simp only [ThresholdPairCount.distinctRegion,ThresholdPairCount.region,mem_filter,mem_product] at hv
  exact (not_lt_of_ge (by simpa only [pow_two] using Nat.mul_le_mul (ha p hv.1.1.1) (hc q hv.1.1.2))) hv.1.2

theorem top_zero (v : ZMod d×ZMod d) : cell X B (B^2) v=0 := by
  rw [cell,above_empty B _ _ (fun _ h => (mem_tail.mp h).2.1) (fun _ h => (mem_tail.mp h).2.1),card_empty]

private theorem telescope {f : ℕ→ℕ} (down : ∀ i,f (i+1)≤f i) (n : ℕ) :
    (∑ i∈range n,(f i-f (i+1)))+f n=f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ]; have h := down n; omega

theorem sum_count {k : ℕ} (hk : k≤2047) (v : ZMod d×ZMod d) :
    (∑ i : Band k,count k i v)=cell X B K v := by
  have h := telescope (f:=fun j => cell X B (edge k j) v)
    (fun j => PrimeFactors.ProductIntervalCellSpread.decreases v (edge_step k j)) (2^k)
  rw [last_edge hk,top_zero,add_zero,first_edge] at h
  exact (Fin.sum_univ_eq_sum_range (fun j => cell X B (edge k j) v-cell X B (edge k (j+1)) v) (2^k)).trans h

private noncomputable def observe (k : ℕ) (z : ℕ×ℕ) : Band k×(ZMod d×ZMod d) :=
  (tag k (z.1*z.2),(z.1,z.2))

attribute [local irreducible] PrimeFactors.PrimeProductRegion.whole eligible cell

private theorem fiber {k : ℕ} (hk : k≤2047) (i : Band k) (v : ZMod d×ZMod d) :
    (PrimeFactors.PrimeProductRegion.whole.filter (fun z => observe k z=(i,v))).card=count k i v := by
  rw [←between]
  apply congrArg Finset.card
  obtain ⟨a,b⟩ := v
  ext ⟨p,q⟩
  simp only [mem_filter,PrimeFactors.PrimeProductRegion.mem_whole,PrimeFactors.PrimeProductRegion.mem_pool,
    observe,Prod.mk.injEq,bandPairs,mem_product,mem_tail]
  constructor
  · rintro ⟨⟨⟨lp,bp,P⟩,⟨lq,bq,Q⟩,low,ne⟩,ti,pa,qa⟩
    have top : p*q≤B^2 := by simpa only [pow_two] using Nat.mul_le_mul bp bq
    obtain ⟨left,right⟩ := (tag_iff hk low top i).mp ti
    exact ⟨⟨⟨lp,bp,P,pa⟩,⟨lq,bq,Q,qa⟩⟩,left,right,ne⟩
  · rintro ⟨⟨⟨lp,bp,P,pa⟩,⟨lq,bq,Q,qa⟩⟩,left,right,ne⟩
    have low := (edge_start k i.val).trans_lt left
    have top : p*q≤B^2 := by simpa only [pow_two] using Nat.mul_le_mul bp bq
    exact ⟨⟨⟨lp,bp,P⟩,⟨lq,bq,Q⟩,low,ne⟩,(tag_iff hk low top i).mpr ⟨left,right⟩,pa,qa⟩

abbrev UnitPair (d : ℕ) := (ZMod d)ˣ×(ZMod d)ˣ
abbrev raw (v : UnitPair d) : ZMod d×ZMod d := (v.1,v.2)

private abbrev embed (k : ℕ) (v : Band k×UnitPair d) : Band k×(ZMod d×ZMod d) :=
  (v.1,raw v.2)

noncomputable def actual (k : ℕ) (cost : Band k→ZMod d→ZMod d→ℕ) : ℝ :=
  ((∑ z∈eligible,cost (tag k (z.1*z.2)) z.1 z.2:ℕ):ℝ)/eligible.card

private theorem twice {k : ℕ} (hk : k≤2047) (cost : Band k→ZMod d→ZMod d→ℕ)
    (sym : ∀ i a b,cost i a b=cost i b a) (good : ∀ {p : ℕ},X<p→p.Prime→IsUnit (p:ZMod d)) :
    2*(∑ z∈eligible,cost (tag k (z.1*z.2)) z.1 z.2)=
      ∑ v : Band k×UnitPair d,count k v.1 (raw v.2)*cost v.1 v.2.1 v.2.2 := by
  let c (z : ℕ×ℕ) := cost (tag k (z.1*z.2)) z.1 z.2
  have eq (p q : ℕ) : c (p,q)=c (q,p) := by dsimp [c]; rw [Nat.mul_comm q p]; exact sym _ _ _
  rw [←PrimeFactors.FiveSquareAllPrimeRanks.weighted_twice c eq]
  apply PrimeFactors.FiveSquareAllPrimeRanks.regroup PrimeFactors.PrimeProductRegion.whole
    (observe (d:=d) k) (embed k) _ (fun v => count k v.1 (raw v.2))
    (fun z => cost z.1 z.2.1 z.2.2)
  · rintro ⟨p,q⟩ h
    obtain ⟨P,Q,_⟩ := (PrimeFactors.PrimeProductRegion.mem_whole (p:=p) (q:=q)).mp h
    obtain ⟨lp,_,hp⟩ := PrimeFactors.PrimeProductRegion.mem_pool.mp P
    obtain ⟨lq,_,hq⟩ := PrimeFactors.PrimeProductRegion.mem_pool.mp Q
    have a := good lp hp
    have b := good lq hq
    exact ⟨(tag k (p*q),a.unit,b.unit),Prod.ext rfl (Prod.ext a.unit_spec b.unit_spec)⟩
  · exact fun v => fiber hk v.1 (raw v.2)
  · rintro ⟨i,a,b⟩ ⟨j,c,e⟩ h
    change (i,((a:ZMod d),(b:ZMod d)))=(j,((c:ZMod d),(e:ZMod d))) at h
    obtain ⟨eq,ab⟩ := Prod.mk.inj h
    exact Prod.ext eq (Prod.ext (Units.ext (congrArg Prod.fst ab)) (Units.ext (congrArg Prod.snd ab)))

private theorem grid_average {α β γ : Type*} [Fintype β] [Fintype γ] (S : Finset α) (g : α→ℕ)
    (w c : β→γ→ℕ)
    (total : 2*(∑ z∈S,g z)=∑ v : β×γ,w v.1 v.2*c v.1 v.2)
    (mass : 2*S.card=∑ v : β×γ,w v.1 v.2) :
    ((∑ z∈S,g z:ℕ):ℝ)/S.card=(∑ i,∑ v,(w i v:ℝ)*c i v)/(∑ i,∑ v,(w i v:ℝ)) := by
  have h := PrimeFactors.FiveSquareAllPrimeRanks.average_eq S g (fun v : β×γ => w v.1 v.2)
    (fun v => c v.1 v.2) total mass
  simpa only [Fintype.sum_prod_type] using h

attribute [local irreducible] tag edge width count
/-- Exact prime-population mean for any symmetric natural cost depending
jointly on the public product band and both factor residues. -/
theorem actual_weighted {k : ℕ} (hk : k≤2047) (cost : Band k→ZMod d→ZMod d→ℕ)
    (sym : ∀ i a b,cost i a b=cost i b a) (good : ∀ {p : ℕ},X<p→p.Prime→IsUnit (p:ZMod d)) :
    actual k cost=(∑ i : Band k,∑ v : UnitPair d,(count k i (raw v):ℝ)*cost i v.1 v.2)/
      (∑ i : Band k,∑ v : UnitPair d,(count k i (raw v):ℝ)) := by
  have mass := PrimeFactors.FiveSquareAllPrimeRanks.card_of_ones eligible (fun v : Band k×UnitPair d => count k v.1 (raw v.2))
    (twice (d:=d) hk (fun _ _ _ => 1) (fun _ _ _ => rfl) good)
  exact grid_average eligible (fun z => cost (tag k (z.1*z.2)) z.1 z.2)
    (fun i v => count k i (raw (d:=d) v)) (fun i v => cost i v.1 v.2)
    (twice hk cost sym good) mass

end PrimeFactors.PrimeProductBandCounts
