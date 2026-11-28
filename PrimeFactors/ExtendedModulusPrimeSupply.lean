import PrimeFactors.PrimeResidueRankTransfer
import PrimeFactors.PrimeProductRegion

/-! Conditional counts of ordered distinct 1024-bit prime pairs above the
2048-bit product threshold in prescribed unit classes, for general moduli.
The endpoint estimates are explicit inputs from Ernvall-Hytönen and
Palojärvi, Corollary 2 under Dirichlet GRH. -/
namespace PrimeFactors.ExtendedModulusPrimeSupply

open Finset WideResiduePrimeSupply PrimeResidueRankTransfer
open FullRangeResidueEstimates (X)
open PrimeProductRegion (K)
open private PrimeFactors.WideResiduePrimeSupply.count_add from PrimeFactors.WideResiduePrimeSupply
open private PrimeFactors.PrimeProductRegion.cutoff from PrimeFactors.PrimeProductRegion
open scoped Classical
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

abbrev D := 52800*2^512

/-- One common logarithmic integral and the explicit prime-count estimate
at each endpoint and each unit residue for the specified modulus. -/
structure Endpoints (m : ℕ) (li : ℕ→ℝ) : Prop where
  quarter : li B=li L+increment L (B-L)
  pointwise (a : ZMod m) (unit : IsUnit a) (z : ℕ) (lo : X≤z) (hi : z≤B) :
    |((through m a.val z).card:ℝ)-li z/m.totient|≤ehpError m z

variable {m : ℕ}

private theorem mem_tail' {a : ZMod m} {p z : ℕ} : p∈tail B z a ↔
    z<p ∧ p≤B ∧ p.Prime ∧ p%m=a.val := by
  simp only [tail,ResiduePairMultiplicity.mem_primes,Nat.lt_succ_iff,Nat.succ_le_iff]

private theorem equivalent (a : ZMod m) {z : ℕ} (hi : z≤B) :
    tail B z a=inBand m a.val z (B-z) := by
  ext p
  rw [mem_tail',mem_band,Nat.add_sub_of_le hi]
  tauto

private theorem err (low : 3≤m) (domain : m≤X) {li : ℕ→ℝ} (h : Endpoints m li) (a : ZMod m) (unit : IsUnit a)
    {z : ℕ} (lo : X≤z) (hi : z≤B) :
    |((through m a.val z).card:ℝ)-li z/m.totient|≤13200*(2:ℝ)^512 :=
  (h.pointwise a unit z lo hi).trans (error_cap low ((domain.trans lo).trans hi)
    (by exact_mod_cast lo) (by exact_mod_cast hi))

private theorem suffix (low : 3≤m) (domain : m≤X) {li : ℕ→ℝ} (h : Endpoints m li) (a b : ZMod m)
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
  have bound := combine (add a) (add b) bd (abs_le.mp (err low domain h a ua xB le_rfl)).2
    (abs_le.mp (err low domain h a ua lo hi)).1 (abs_le.mp (err low domain h b ub xB le_rfl)).1 (abs_le.mp (err low domain h b ub lo hi)).2
  exact_mod_cast bound

private theorem quarter_lower {Q A : ℕ} (low : 3≤m) (cap : m≤Q) (domain : Q≤X)
    (room : (A:ℝ)+26400*(2:ℝ)^512≤((B-L:ℕ):ℝ)/(710*(Q:ℝ)))
    {li : ℕ→ℝ} (h : Endpoints m li) (a : ZMod m) (ua : IsUnit a) :
    A≤(tail B L a).card := by
  have xl : X≤L := by decide +kernel
  have lb : L≤B := by decide +kernel
  have stop : L+(B-L)=B := Nat.add_sub_of_le lb
  have z : BandEndpoints m a.val L (B-L) (li L) := by
    refine ⟨h.pointwise a ua L xl lb,?_⟩
    rw [stop,←h.quarter]
    exact h.pointwise a ua B (xl.trans lb) le_rfl
  have main := band_lower low ((cap.trans domain).trans xl) xl stop.le z
  have ph : m.totient≤Q := (Nat.totient_le m).trans cap
  have pp : (0:ℝ)<m.totient := by exact_mod_cast Nat.totient_pos.mpr ((by decide : 0<3).trans_le low)
  have denominator : 710*(m.totient:ℝ)≤710*(Q:ℝ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast ph) (by norm_num)
  have lower := div_le_div_of_nonneg_left (Nat.cast_nonneg (B-L) : 0≤((B-L:ℕ):ℝ))
    (mul_pos (by norm_num : (0:ℝ)<710) pp) denominator
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

/-- Uniform additive spread between any two unit-coordinate cells. -/
theorem spread (low : 3≤m) (domain : m≤X) {li : ℕ→ℝ} (h : Endpoints m li) {v w : ZMod m × ZMod m}
    (ua : IsUnit v.1) (ub : IsUnit v.2) (uc : IsUnit w.1) (ue : IsUnit w.2) :
    cell X B K v≤cell X B K w+(2*D*B+B) := by
  apply ThresholdPairCount.spread _ _ _ _ (upper _) (upper _) (upper _)
  · intro p hp
    obtain ⟨lo,hi,_,_⟩ := mem_tail'.mp hp
    rw [slice _ lo hi,slice _ lo hi]
    exact suffix low domain h _ _ ub ue (PrimeFactors.PrimeProductRegion.cutoff lo hi).1 (PrimeFactors.PrimeProductRegion.cutoff lo hi).2
  · intro p hp
    obtain ⟨lo,hi,_,_⟩ := mem_tail'.mp hp
    rw [slice _ lo hi,slice _ lo hi]
    exact suffix low domain h _ _ ua uc (PrimeFactors.PrimeProductRegion.cutoff lo hi).1 (PrimeFactors.PrimeProductRegion.cutoff lo hi).2

/-- A quarter-band count lower bound for both coordinates supplies
A*(A−1) ordered pairs, even when their residue classes coincide. -/
theorem lower_of_cap {Q A : ℕ} (low : 3≤m) (cap : m≤Q) (domain : Q≤X)
    (room : (A:ℝ)+26400*(2:ℝ)^512≤((B-L:ℕ):ℝ)/(710*(Q:ℝ)))
    {li : ℕ→ℝ} (h : Endpoints m li) {v : ZMod m × ZMod m}
    (ua : IsUnit v.1) (ub : IsUnit v.2) : A*(A-1)≤cell X B K v := by
  have sub (a : ZMod m) : tail B L a ⊆ tail B X a := by
    intro p hp
    obtain ⟨lo,hi,P,r⟩ := mem_tail'.mp hp
    exact mem_tail'.mpr ⟨(by decide +kernel : X≤L).trans_lt lo,hi,P,r⟩
  apply ThresholdPairCount.lower (quarter_lower low cap domain room h _ ua) (quarter_lower low cap domain room h _ ub) (sub _) (sub _)
  intro p hp q hq
  exact (by decide +kernel : K<L*L).trans_le (Nat.mul_le_mul (mem_tail'.mp hp).1.le (mem_tail'.mp hq).1.le)

attribute [local irreducible] cell tail

private theorem finite_bounds {F : ℕ} {α : Type*} [Fintype α] (z : α) (c : α→ℕ) (e : ℕ)
    (pos : ∀ a, 0<c a) (small : ∀ a, F*e≤c a) (spread : ∀ a b, c a≤c b+e) :
    ∃ l u : ℕ, 0<l ∧ F*u≤(F+1)*l ∧ ∀ a : α, l≤c a ∧ c a≤u := by
  obtain ⟨v,_,least⟩ := Finset.univ.exists_min_image c ⟨z,mem_univ z⟩
  refine ⟨c v,c v+e,pos v,?_,fun a => ⟨least a (mem_univ a),spread a v⟩⟩
  rw [Nat.mul_add,Nat.add_mul,one_mul]
  exact Nat.add_le_add_left (small v) _


/-- Common relative spread at any scale F for which the additive
endpoint error fits into the established cell-count lower bound. -/
theorem bounds_of_stages [NeZero m] {Q A F : ℕ} (low : 3≤m) (cap : m≤Q) (domain : Q≤X)
    (room : (A:ℝ)+26400*(2:ℝ)^512≤((B-L:ℕ):ℝ)/(710*(Q:ℝ)))
    (positive : 0<A*(A-1)) (accurate : F*(2*D*B+B)≤A*(A-1))
    {li : ℕ→ℝ} (h : Endpoints m li) :
    ∃ l u : ℕ, 0<l ∧ F*u≤(F+1)*l ∧
      ∀ v : (ZMod m)ˣ×(ZMod m)ˣ, l≤cell X B K (v.1.val,v.2.val) ∧ cell X B K (v.1.val,v.2.val)≤u := by
  let c (v : (ZMod m)ˣ×(ZMod m)ˣ) := cell X B K (v.1.val,v.2.val)
  have each (v : (ZMod m)ˣ×(ZMod m)ˣ) : A*(A-1)≤c v :=
    lower_of_cap low cap domain room h (v:=⟨v.1.val,v.2.val⟩) v.1.isUnit v.2.isUnit
  exact finite_bounds (1,1) c (2*D*B+B) (fun v => positive.trans_le (each v))
    (fun v => accurate.trans (each v)) (fun v w => spread low (cap.trans domain) h
      (v:=⟨v.1.val,v.2.val⟩) (w:=⟨w.1.val,w.2.val⟩) v.1.isUnit v.2.isUnit w.1.isUnit w.2.isUnit)

private theorem room_161 :
    ((2^850:ℕ):ℝ)+26400*(2:ℝ)^512 ≤ ((B-L:ℕ):ℝ)/(710*((2^161:ℕ):ℝ)) := by norm_num [B,L]

/-- Each unit residue has at least 2^850 prime representatives in the
upper quarter of the 1024-bit range, under the endpoint estimates. -/
theorem quarter_bound {d : ℕ} (low : 3≤d) (cap : d≤2^161)
    {li : ℕ→ℝ} (h : Endpoints d li) (a : ZMod d) (unit : IsUnit a) :
    2^850≤(tail B L a).card :=
  quarter_lower low cap (by decide +kernel) room_161 h a unit

/-- The bound at every unit-coordinate pair holds for the entire
product-size region, with modulus up to 2^161. -/
theorem cell_bounds {d : ℕ} [NeZero d] (low : 3≤d) (cap : d≤2^161) {li : ℕ→ℝ}
    (h : Endpoints d li) : ∃ l u : ℕ, 0<l ∧ 2^146*u≤(2^146+1)*l ∧
      ∀ v : (ZMod d)ˣ×(ZMod d)ˣ, l≤cell X B K (v.1.val,v.2.val) ∧ cell X B K (v.1.val,v.2.val)≤u := by
  exact bounds_of_stages (A:=2^850) low cap (by decide +kernel) room_161 (by decide +kernel) (by decide +kernel) h

end PrimeFactors.ExtendedModulusPrimeSupply
