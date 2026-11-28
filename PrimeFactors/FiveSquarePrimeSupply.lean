import PrimeFactors.PrimeResidueRankTransfer
import PrimeFactors.FiveSquareGuessRanks
import PrimeFactors.PrimeProductRegion

/-! Counts of distinct, full-width actual prime pairs in individual residue
cells for the five-prime example. The analytic estimates are explicit inputs
from Ernvall-Hytönen and Palojärvi, Corollary 2, assuming Dirichlet GRH. -/

namespace PrimeFactors.FiveSquarePrimeSupply

open Finset WideResiduePrimeSupply PrimeResidueRankTransfer
open FullRangeResidueEstimates (X)
open PrimeProductRegion (K)
open PrimeSquareSumWeights (Pairs)
open private PrimeFactors.WideResiduePrimeSupply.count_add from PrimeFactors.WideResiduePrimeSupply
open private PrimeFactors.PrimeProductRegion.cutoff from PrimeFactors.PrimeProductRegion
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

noncomputable abbrev m : ℕ := CoprimeGuessTables.modulus FiveSquareGuessRanks.primes
abbrev D := 52800*2^512
abbrev M := 2^975
abbrev F := 2^380

/-- Common logarithmic integral and published estimates at every integer
endpoint used by the product threshold. -/
structure Endpoints (li : ℕ→ℝ) : Prop where
  quarter : li B=li L+increment L (B-L)
  pointwise (a : ZMod m) (unit : IsUnit a) (z : ℕ) (lo : X≤z) (hi : z≤B) :
    |((through m a.val z).card:ℝ)-li z/m.totient|≤ehpError m z

private theorem mem_tail' {a : ZMod m} {p z : ℕ} : p∈tail B z a ↔
    z<p ∧ p≤B ∧ p.Prime ∧ p%m=a.val := by
  simp only [tail,ResiduePairMultiplicity.mem_primes,Nat.lt_succ_iff,Nat.succ_le_iff]

private theorem equivalent (a : ZMod m) {z : ℕ} (hi : z≤B) :
    tail B z a=inBand m a.val z (B-z) := by
  ext p
  rw [mem_tail',mem_band,Nat.add_sub_of_le hi]
  tauto

private theorem modulus_bounds : 3≤m ∧ m≤2^33 := by
  rw [show m=7239457225 from FiveSquareGuessRanks.modulus_value]
  decide

/-- All real x and integer moduli in the estimates are in the paper's range. -/
theorem source_domain {z : ℕ} (lo : X≤z) : 3≤m ∧ m≤z :=
  ⟨modulus_bounds.1,modulus_bounds.2.trans ((by decide +kernel : 2^33≤X).trans lo)⟩

private theorem err {li : ℕ→ℝ} (h : Endpoints li) (a : ZMod m) (unit : IsUnit a)
    {z : ℕ} (lo : X≤z) (hi : z≤B) :
    |((through m a.val z).card:ℝ)-li z/m.totient|≤13200*(2:ℝ)^512 :=
  (h.pointwise a unit z lo hi).trans (error_cap modulus_bounds.1 ((source_domain lo).2.trans hi)
    (by exact_mod_cast lo) (by exact_mod_cast hi))

private theorem suffix {li : ℕ→ℝ} (h : Endpoints li) (a b : ZMod m)
    (ua : IsUnit a) (ub : IsUnit b) {z : ℕ} (lo : X≤z) (hi : z≤B) :
    (tail B z a).card≤(tail B z b).card+D := by
  have add (c : ZMod m) : ((tail B z c).card:ℝ)+(through m c.val z).card=(through m c.val B).card := by
    rw [equivalent c hi]
    exact_mod_cast (Nat.add_sub_of_le hi ▸ PrimeFactors.WideResiduePrimeSupply.count_add m c.val z (B-z))
  have xB : X≤B := by decide +kernel
  have bd : (D:ℝ)=4*(13200*(2:ℝ)^512) := by norm_num [D]
  have combine {atop alow btop blow ast bst mcB mcz e d : ℝ}
      (aa : ast+alow=atop) (bb : bst+blow=btop) (ds : d=4*e)
      (a₁ : atop-mcB≤e) (a₂ : -e≤alow-mcz) (b₁ : -e≤btop-mcB) (b₂ : blow-mcz≤e) :
      ast≤bst+d := by linarith
  have bound := combine (add a) (add b) bd (abs_le.mp (err h a ua xB le_rfl)).2
    (abs_le.mp (err h a ua lo hi)).1 (abs_le.mp (err h b ub xB le_rfl)).1 (abs_le.mp (err h b ub lo hi)).2
  exact_mod_cast bound

private theorem quarter_lower {li : ℕ→ℝ} (h : Endpoints li) (a : ZMod m) (ua : IsUnit a) :
    M≤(tail B L a).card := by
  have xl : X≤L := by decide +kernel
  have lb : L≤B := by decide +kernel
  have stop : L+(B-L)=B := Nat.add_sub_of_le lb
  have z : BandEndpoints m a.val L (B-L) (li L) := by
    refine ⟨h.pointwise a ua L xl lb,?_⟩
    rw [stop,←h.quarter]
    exact h.pointwise a ua B (xl.trans lb) le_rfl
  have main := band_lower modulus_bounds.1 (source_domain xl).2 xl stop.le z
  have ph : m.totient≤2^33 := (Nat.totient_le m).trans modulus_bounds.2
  have pp : (0:ℝ)<m.totient := by exact_mod_cast Nat.totient_pos.mpr ((by decide : 0<3).trans_le modulus_bounds.1)
  have denominator : 710*(m.totient:ℝ)≤710*(2:ℝ)^33 := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast ph) (by norm_num)
  have lower := div_le_div_of_nonneg_left (Nat.cast_nonneg (B-L) : 0≤((B-L:ℕ):ℝ))
    (mul_pos (by norm_num : (0:ℝ)<710) pp) denominator
  have room : (M:ℝ)+26400*(2:ℝ)^512≤((B-L:ℕ):ℝ)/(710*(2:ℝ)^33) := by norm_num [M,B,L]
  rw [equivalent a lb]
  have combine {m e a b c : ℝ} (bound : b-e≤c) (lo : a≤b) (fit : m+e≤a) : m≤c := by linarith
  exact_mod_cast combine main lower room

private theorem upper (a : ZMod m) : (tail B X a).card≤B := by
  have sub : tail B X a ⊆ Ioc X B := fun p hp => mem_Ioc.mpr ⟨(mem_tail'.mp hp).1,(mem_tail'.mp hp).2.1⟩
  exact (card_le_card sub).trans ((Nat.card_Ioc X B).le.trans (Nat.sub_le ..))

private theorem slice (a : ZMod m) {p : ℕ} (lo : X<p) (hi : p≤B) :
    (tail B X a).filter (fun q => K<p*q)=tail B (K/p) a := by
  have pos : 0<p := (by decide +kernel : 0<X).trans lo
  have left := (PrimeFactors.PrimeProductRegion.cutoff lo hi).1
  ext q
  rw [mem_filter,mem_tail',mem_tail']
  have eq : K<p*q ↔ K/p<q := by rw [Nat.div_lt_iff_lt_mul pos,Nat.mul_comm q p]
  rw [eq]
  exact ⟨fun ⟨⟨_,qh,P,r⟩,t⟩ => ⟨t,qh,P,r⟩,fun ⟨t,qh,P,r⟩ => ⟨⟨left.trans_lt t,qh,P,r⟩,t⟩⟩

theorem spread {li : ℕ→ℝ} (h : Endpoints li) {v w : ZMod m × ZMod m}
    (ua : IsUnit v.1) (ub : IsUnit v.2) (uc : IsUnit w.1) (ue : IsUnit w.2) :
    cell X B K v≤cell X B K w+(2*D*B+B) := by
  apply ThresholdPairCount.spread _ _ _ _ (upper _) (upper _) (upper _)
  · intro p hp
    obtain ⟨lo,hi,_,_⟩ := mem_tail'.mp hp
    rw [slice _ lo hi,slice _ lo hi]
    exact suffix h _ _ ub ue (PrimeFactors.PrimeProductRegion.cutoff lo hi).1 (PrimeFactors.PrimeProductRegion.cutoff lo hi).2
  · intro p hp
    obtain ⟨lo,hi,_,_⟩ := mem_tail'.mp hp
    rw [slice _ lo hi,slice _ lo hi]
    exact suffix h _ _ ua uc (PrimeFactors.PrimeProductRegion.cutoff lo hi).1 (PrimeFactors.PrimeProductRegion.cutoff lo hi).2

theorem lower {li : ℕ→ℝ} (h : Endpoints li) {v : ZMod m × ZMod m}
    (ua : IsUnit v.1) (ub : IsUnit v.2) : M*(M-1)≤cell X B K v := by
  have sub (a : ZMod m) : tail B L a ⊆ tail B X a := by
    intro p hp
    obtain ⟨lo,hi,P,r⟩ := mem_tail'.mp hp
    exact mem_tail'.mpr ⟨(by decide +kernel : X≤L).trans_lt lo,hi,P,r⟩
  apply ThresholdPairCount.lower (quarter_lower h _ ua) (quarter_lower h _ ub) (sub _) (sub _)
  intro p hp q hq
  exact (by decide +kernel : K<L*L).trans_le (Nat.mul_le_mul (mem_tail'.mp hp).1.le (mem_tail'.mp hq).1.le)

attribute [local irreducible] cell tail

private theorem finite_bounds {α : Type*} [Fintype α] (z : α) (c : α→ℕ) (e : ℕ)
    (pos : ∀ a, 0<c a) (small : ∀ a, F*e≤c a) (spread : ∀ a b, c a≤c b+e) :
    ∃ l u : ℕ, 0<l ∧ F*u≤(F+1)*l ∧ ∀ a : α, l≤c a ∧ c a≤u := by
  obtain ⟨v,_,least⟩ := Finset.univ.exists_min_image c ⟨z,mem_univ z⟩
  refine ⟨c v,c v+e,pos v,?_,fun a => ⟨least a (mem_univ a),spread a v⟩⟩
  rw [Nat.mul_add,Nat.add_mul,one_mul]
  exact Nat.add_le_add_left (small v) _

/-- Every product-one residue cell occurs, and the largest has at most
1+2⁻³⁸⁰ times the population of the smallest. -/
theorem cell_bounds {li : ℕ→ℝ} (h : Endpoints li) : ∃ l u : ℕ, 0<l ∧ F*u≤(F+1)*l ∧
    ∀ v : Pairs 1 m, l≤cell X B K v.val ∧ cell X B K v.val≤u := by
  let z : Pairs 1 m := ⟨(1,1),by simp⟩
  have unit (a : Pairs 1 m) : IsUnit a.val.1 ∧ IsUnit a.val.2 :=
    (Commute.all _ _).isUnit_mul_iff.mp (by rw [a.property]; simp)
  have each (v : Pairs 1 m) : M*(M-1)≤cell X B K v.val := lower h (v:=v.val) (unit v).1 (unit v).2
  have fit : F*(2*D*B+B)≤M*(M-1) := by decide +kernel
  exact finite_bounds z (fun v => cell X B K v.val) (2*D*B+B)
    (fun a => (by decide +kernel : 0<M*(M-1)).trans_le (each a))
    (fun a => fit.trans (each a))
    (fun a v => spread h (v:=a.val) (w:=v.val) (unit a).1 (unit a).2 (unit v).1 (unit v).2)

end PrimeFactors.FiveSquarePrimeSupply
