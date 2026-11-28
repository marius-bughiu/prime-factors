import PrimeFactors.CyclotomicRootEnergy
import PrimeFactors.ExtendedProductCosts
import PrimeFactors.PrimeGridMass
import PrimeFactors.FiniteBinCollisionPopulation

/-! Frequency of the energy value 6 on canonical full-width prime pairs,
conditioned on any prescribed nonzero product residue modulo seven. -/
namespace PrimeFactors.CyclotomicEnergySevenPopulation

open Finset WideResiduePrimeSupply PrimeResidueRankTransfer
open FullRangeResidueEstimates (X)
open PrimeProductRegion (K)
open MixedPrefixSample (eligible)
open CyclotomicRootEnergy (energy)
attribute [local irreducible] MixedPrefixSample.eligible PrimeResidueRankTransfer.cell
open private PrimeFactors.ExtendedProductCosts.unit_of_prime from PrimeFactors.ExtendedProductCosts
open private PrimeFactors.FullPopulationFavoredSums.mem_eligible from PrimeFactors.FullPopulationFavoredSums
open private PrimeFactors.PrimeGridMass.interval_error PrimeFactors.PrimeGridMass.increment_upper
  from PrimeFactors.PrimeGridMass
open private PrimeFactors.ExtendedModulusPrimeSupply.equivalent PrimeFactors.ExtendedModulusPrimeSupply.slice
  PrimeFactors.ExtendedModulusPrimeSupply.finite_bounds from PrimeFactors.ExtendedModulusPrimeSupply
open private PrimeFactors.PrimeProductRegion.cutoff from PrimeFactors.PrimeProductRegion
open private PrimeFactors.UnconditionalPrimePairSumFrequency.endpoint_cap from PrimeFactors.UnconditionalPrimePairSumFrequency
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

abbrev Unit7 := (ZMod 7)ˣ

def bit (a b : ZMod 7) : Bool := decide (a=b ∨ a+b=0)

noncomputable def cells (r : Unit7) (hit : Bool) :=
  (univ : Finset (Unit7×Unit7)).filter fun v => v.1*v.2=r ∧ bit v.1 v.2=hit

theorem census : ∀ r : Unit7, (cells r true).card=2 ∧ (cells r false).card=4 := by decide +kernel

noncomputable def population (r : Unit7) := eligible.filter fun v => ((v.1*v.2:ℕ):ZMod 7)=r.val

noncomputable def hits (r : Unit7) := (population r).filter fun v => energy (v.1*v.2) 7=6

private theorem not_seven {p : ℕ} (prime : p.Prime) (lo : X≤p) : ¬7∣p := by
  intro dvd
  have h := (Nat.dvd_prime prime).mp dvd
  have bound : 7<X := by decide +kernel
  omega

theorem energy_iff {p q : ℕ} (member : (p,q)∈eligible) : energy (p*q) 7=6 ↔ bit p q=true := by
  obtain ⟨lo,lt,_,pp,qp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp member
  have np := not_seven pp lo
  have nq := not_seven qp (lo.trans lt.le)
  have gap : 7∣q-p ↔ (p:ZMod 7)=q :=
    (Nat.modEq_iff_dvd' lt.le).symm.trans (ZMod.natCast_eq_natCast_iff ..).symm
  have total : 7∣p+q ↔ (p:ZMod 7)+q=0 := by
    rw [←Nat.cast_add,ZMod.natCast_zmod_eq_zero_iff_dvd]
  have never : ∀ a b : ZMod 7, a≠0 → a=b → a+b≠0 := by decide +kernel
  have dis := never p q (fun z => np ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp z))
  simp only [CyclotomicRootEnergy.alias_formula pp qp lt,if_neg np,if_neg nq,total,gap]
  have arith (a b : ZMod 7) (d : a=b → a+b≠0) :
      4-4*(0:ℝ)-4*0+2*(if a+b=0 then 1 else 0)+2*(if a=b then 1 else 0)=6 ↔ bit a b=true := by
    by_cases g : a=b <;> by_cases s : a+b=0 <;> simp_all [bit] <;> norm_num
  exact arith _ _ dis

private noncomputable def group (r : Unit7) (h : Bool) := (population r).filter fun v => bit v.1 v.2=h

private theorem split (r : Unit7) : (group r true).card+(group r false).card=(population r).card := by
  simp only [group,←Bool.not_eq_true]
  exact filter_card_add_filter_neg_card_eq_card _

private theorem hit_group (r : Unit7) : hits r=group r true := by
  unfold hits group
  apply filter_congr
  intro v hv
  rw [population] at hv
  exact energy_iff (p:=v.1) (q:=v.2) (mem_filter.mp hv).1

attribute [local irreducible] population group hits cells tail

private theorem bounds (r : Unit7) (h : Bool) {l u : ℕ}
    (ws : ∀ v : Unit7×Unit7, l≤cell X B K (v.1.val,v.2.val) ∧ cell X B K (v.1.val,v.2.val)≤u) :
    l*(cells r h).card ≤ 2*(group r h).card ∧ 2*(group r h).card ≤ u*(cells r h).card := by
  let f (a b : ZMod 7) := if a*b=r.val ∧ bit a b=h then 1 else 0
  have sym (a b : ZMod 7) : f a b=f b a := by simp only [f,bit,mul_comm b a,add_comm b a,@eq_comm _ b a]
  have sum := FiveSquareAllPrimeRanks.twice_cost f sym (PrimeFactors.ExtendedProductCosts.unit_of_prime (by decide))
  have sum_eq (S : Finset (ℕ×ℕ)) : (∑ z∈S,f z.1 z.2)=(S.filter (fun v => (v.1:ZMod 7)*v.2=r.val ∧ bit v.1 v.2=h)).card := by simp only [f,sum_boole,Nat.cast_id]
  rw [sum_eq] at sum
  have eq : 2*(group r h).card=∑ v∈cells r h,cell X B K (v.1.val,v.2.val) := by
    rw [group,population,filter_filter]
    simpa only [Nat.cast_mul,f,cells,←Units.val_mul,←Units.ext_iff,mul_ite,mul_one,mul_zero,
      sum_filter,sum_boole,Nat.cast_id] using sum
  rw [eq]
  have a := sum_le_sum (s:=cells r h) (fun v _ => (ws v).1)
  have b := sum_le_sum (s:=cells r h) (fun v _ => (ws v).2)
  simpa only [sum_const,nsmul_eq_mul,Nat.cast_id,mul_comm l,mul_comm u] using And.intro a b

/-- The two selected cells and four complementary cells share the same
pointwise weight bounds. Their common conditioning denominator is positive. -/
theorem transfer (r : Unit7) {l u F : ℕ} (lp : 0<l) (fp : 0<F) (scale : F*u≤(F+1)*l)
    (ws : ∀ v : Unit7×Unit7, l≤cell X B K (v.1.val,v.2.val) ∧ cell X B K (v.1.val,v.2.val)≤u) :
    0<(population r).card ∧ |((hits r).card:ℝ)/(population r).card-1/3|≤2/(9*(F:ℝ)) := by
  obtain ⟨al,au⟩ := bounds r true ws
  obtain ⟨cl,cu⟩ := bounds r false ws
  rw [(census r).1] at al au
  rw [(census r).2] at cl cu
  rw [hit_group]
  have algebra {a c s l u F : ℕ} (total : a+c=s) (lp : 0<l) (fp : 0<F)
      (ratio : F*u≤(F+1)*l) (al : l*2≤2*a) (au : 2*a≤u*2) (cl : l*4≤2*c) (cu : 2*c≤u*4) :
      0<s ∧ |(a:ℝ)/s-1/3|≤2/(9*(F:ℝ)) := by
    have lo : l≤a := by omega
    have hi : a≤u := by omega
    have below : 2*l≤c := by omega
    have above : c≤2*u := by omega
    have sp : 0<s := by omega
    refine ⟨sp,?_⟩
    have difference₁ : 3*F*a≤F*s+2*l := by
      nlinarith only [Nat.mul_le_mul_left F hi,Nat.mul_le_mul_left F below,ratio,congrArg (F*·) total]
    have difference₂ : F*s≤3*F*a+2*l := by
      nlinarith only [Nat.mul_le_mul_left F lo,Nat.mul_le_mul_left F above,ratio,congrArg (F*·) total]
    have v₁ : 3*(F:ℝ)*a≤F*s+2*l := by exact_mod_cast difference₁
    have v₂ : (F:ℝ)*s≤3*F*a+2*l := by exact_mod_cast difference₂
    have size : 3*(l:ℝ)≤s := by exact_mod_cast (show 3*l≤s by omega)
    have ss : (0:ℝ)<s := by exact_mod_cast sp
    have ff : (0:ℝ)<F := by exact_mod_cast fp
    have qq : (a:ℝ)/s-1/3=(3*a-s)/(3*s) := by field_simp; ring
    rw [qq,abs_le,←neg_div,div_le_div_iff₀ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    constructor <;> nlinarith only [v₁,v₂,size]
  exact algebra (split r) lp fp scale al au cl cu

/-- The common logarithmic integral and the named pointwise estimate in
each of the six prime progressions are explicit assumptions. -/
structure Endpoints (error li : ℕ→ℝ) : Prop where
  integral (z : ℕ) (lo : X≤z) (hi : z≤B) : li B=li z+increment z (B-z)
  pointwise (a : ZMod 7) (unit : IsUnit a) (z : ℕ) (lo : X≤z) (hi : z≤B) :
    |((through 7 a.val z).card:ℝ)-li z/6|≤error z

private abbrev U := B/8500
private abbrev M := B/17050
private noncomputable abbrev e₀ := (B:ℝ)/(840*700^2)

private theorem from_endpoints {li err : ℕ→ℝ} (h : Endpoints err li) {e : ℝ} {D F : ℕ}
    (cap : ∀ z, X≤z → z≤B → err z≤e) (small : e≤e₀) (round : 4*e<(D:ℝ)+1)
    (precise : F*(2*D*U+U)≤M*(M-1)) :
    ∃ l u : ℕ, 0<l ∧ F*u≤(F+1)*l ∧
    ∀ v : Unit7×Unit7, l≤cell X B K (v.1.val,v.2.val) ∧ cell X B K (v.1.val,v.2.val)≤u := by
  have center (a : Unit7) {z : ℕ} (lo : X≤z) (hi : z≤B) :
      |((tail B z a.val).card:ℝ)-increment z (B-z)/6|≤2*e := by
    have step := PrimeFactors.PrimeGridMass.interval_error (A:=z) (W:=B-z) lo (Nat.add_sub_of_le hi).le
      h.integral (h.pointwise a.val a.isUnit)
    rw [Nat.add_sub_of_le hi] at step
    rw [PrimeFactors.ExtendedModulusPrimeSupply.equivalent a.val hi,two_mul]
    exact step.trans (add_le_add (cap z lo hi) (cap B (lo.trans hi) le_rfl))
  have comp {x y t e d : ℝ} (high : x-t≤2*e) (low : -(2*e)≤y-t) (round : 4*e<d+1) :
      x<y+d+1 := by linarith
  have top {v t w e u : ℝ} (high : v-t/6≤2*e) (intgr : t≤w/709) (margin : w/709/6+2*e≤u) :
      v≤u := by linarith
  have bot {v t w e m : ℝ} (low : -(2*e)≤v-t/6) (intgr : w/710≤t) (margin : m≤w/710/6-2*e) :
      m≤v := by linarith
  have shift (a b : Unit7) {z : ℕ} (lo : X≤z) (hi : z≤B) : (tail B z a.val).card≤(tail B z b.val).card+D := by
    have bound := abs_le.mp (center a lo hi)
    have bound' := abs_le.mp (center b lo hi)
    have close : ((tail B z a.val).card:ℝ)<(tail B z b.val).card+D+1 := comp bound.2 bound'.1 round
    exact Nat.le_of_lt_succ (by exact_mod_cast close)
  have upper (a : Unit7) : (tail B X a.val).card≤U := by
    have b := (abs_le.mp (center a (z:=X) le_rfl (by decide))).2
    have i := PrimeFactors.PrimeGridMass.increment_upper X (B-X) le_rfl
    have n : ((B-X:ℕ):ℝ)/709/6+2*e₀≤(U:ℝ) := by norm_num [U,X,B,e₀]
    exact_mod_cast top b i ((add_le_add_left (mul_le_mul_of_nonneg_left small (by norm_num : (0:ℝ)≤2)) _).trans n)
  have lower (a : Unit7) : M≤(tail B L a.val).card := by
    have b := (abs_le.mp (center a (z:=L) (by decide) (by decide))).1
    have i := increment_lower (A:=L) (W:=B-L) (by decide) (by decide)
    have n : (M:ℝ)≤((B-L:ℕ):ℝ)/710/6-2*e₀ := by norm_num [M,L,B,e₀]
    exact_mod_cast bot b i (n.trans (sub_le_sub_left (mul_le_mul_of_nonneg_left small (by norm_num : (0:ℝ)≤2)) _))
  have floor (v : Unit7×Unit7) : M*(M-1)≤cell X B K (v.1.val,v.2.val) := by
    have sub (a : ZMod 7) : tail B L a⊆tail B X a := by
      intro p hp
      obtain ⟨lo,hi,pr,rem⟩ := mem_tail.mp hp
      exact mem_tail.mpr ⟨(by decide : X≤L).trans_lt lo,hi,pr,rem⟩
    unfold cell
    apply ThresholdPairCount.lower (lower v.1) (lower v.2) (sub _) (sub _)
    intro p hp q hq
    exact
      (by decide +kernel : K<L*L).trans_le (Nat.mul_le_mul (mem_tail.mp hp).1.le (mem_tail.mp hq).1.le)
  apply PrimeFactors.ExtendedModulusPrimeSupply.finite_bounds (1,1) _ (2*D*U+U)
    (fun v => (by decide +kernel : 0<M*(M-1)).trans_le (floor v)) (fun v => precise.trans (floor v))
  intro v w
  unfold cell
  apply ThresholdPairCount.spread _ _ _ _ (upper v.1) (upper w.2) (upper w.1)
  all_goals
    intro p hp
    obtain ⟨lo,hi,_,_⟩ := mem_tail.mp hp
    rw [PrimeFactors.ExtendedModulusPrimeSupply.slice _ lo hi,PrimeFactors.ExtendedModulusPrimeSupply.slice _ lo hi]
    exact shift _ _ (PrimeFactors.PrimeProductRegion.cutoff lo hi).1 (PrimeFactors.PrimeProductRegion.cutoff lo hi).2

/-- Bennett–Martin–O'Bryant–Rechnitzer's unconditional prime-count estimate
places each of the six actual frequencies within 1/6750 of one third. -/
theorem bmor {li : ℕ→ℝ} (h : Endpoints (fun z => (z:ℝ)/(840*(Real.log z)^2)) li) (r : Unit7) :
    0<(population r).card ∧ |((hits r).card:ℝ)/(population r).card-1/3|≤1/6750 := by
  obtain ⟨l,u,lp,ratio,ws⟩ := from_endpoints (F:=1500) (D:=FullRangeResidueEstimates.bmorD) (e:=e₀) h
    (fun z low high => (PrimeFactors.UnconditionalPrimePairSumFrequency.endpoint_cap low).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast high) (by norm_num))) le_rfl
    (by norm_num [FullRangeResidueEstimates.bmorD,e₀,B]) (by decide +kernel)
  obtain ⟨pos,frac⟩ := transfer r lp (by decide : 0<1500) ratio ws
  exact ⟨pos,frac.trans (by norm_num)⟩

/-- Ernvall-Hytönen–Palojärvi's Dirichlet-GRH endpoint bounds give
absolute error at most 2/(9·2^480) in every nonzero product class. -/
theorem ehp {li : ℕ→ℝ} (h : Endpoints (fun z => ehpError 7 z) li) (r : Unit7) :
    0<(population r).card ∧ |((hits r).card:ℝ)/(population r).card-1/3|≤2/(9*(2:ℝ)^480) := by
  obtain ⟨l,u,lp,ratio,ws⟩ := from_endpoints (F:=2^480) (D:=ExtendedModulusPrimeSupply.D)
    (e:=13200*(2:ℝ)^512) h
    (fun z lo hi => error_cap (by decide) ((by decide : 7≤X).trans (lo.trans hi))
      (by exact_mod_cast lo) (by exact_mod_cast hi))
    (by norm_num [e₀,B]) (by norm_num [ExtendedModulusPrimeSupply.D]) (by decide +kernel)
  obtain ⟨pos,frac⟩ := transfer r lp (by decide +kernel : 0<2^480) ratio ws
  exact ⟨pos,by exact_mod_cast frac⟩

/-- The q=7 row of BMOR Table 1 gives cπ=0.0004857 from x=1,765,715,753.
See https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=6. -/
noncomputable def bmorSevenError (z : ℕ) : ℝ := 4857*z/(10000000*(Real.log z)^2)

theorem bmor_seven_domain {z : ℕ} (lo : X≤z) : 1765715753≤z :=
  (by decide +kernel : 1765715753≤X).trans lo

theorem bmor_seven {li : ℕ→ℝ} (h : Endpoints bmorSevenError li) (r : Unit7) :
    0<(population r).card ∧ |((hits r).card:ℝ)/(population r).card-1/3|≤1/17010 := by
  let e : ℝ := 4857*B/(10000000*709^2)
  let D : ℕ := 4*4857*B/(10000000*709^2)
  have cap (z : ℕ) (lo : X≤z) (hi : z≤B) : bmorSevenError z≤e := by
    have bound := Real.log_le_log (by positivity : 0<(2:ℝ)^1023) (by exact_mod_cast lo : (2:ℝ)^1023≤z)
    rw [Real.log_pow] at bound
    norm_num only [Nat.cast_ofNat] at bound
    have lg : (709:ℝ)≤Real.log z := by linarith only [bound,Real.log_two_gt_d9]
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hi) (by norm_num))
      (by norm_num) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) lg 2) (by norm_num))
  obtain ⟨l,u,lp,ratio,ws⟩ := from_endpoints (F:=3780) (D:=D) h cap (by norm_num [e,e₀,B])
    (by norm_num [D,e,B]) (by decide +kernel)
  obtain ⟨pos,frac⟩ := transfer r lp (by decide : 0<3780) ratio ws
  exact ⟨pos,frac.trans (by norm_num)⟩

/-- Count the energy-six pairs over all eligible products, without conditioning
on an observed product class. -/
noncomputable def allHits := eligible.filter fun v => energy (v.1*v.2) 7=6

/-- Finite pigeonholing alone puts more than one in 36 eligible products
in the energy-six class. This theorem has no analytic endpoint input. -/
theorem unconditional_floor : eligible.card<36*allHits.card := by
  let bucket (a : ZMod 7) := min a.val (7-a.val)-1
  have table : (∀ a : ZMod 7, bucket a<3) ∧
      (∀ a b : ZMod 7, a≠0 → b≠0 → bucket a=bucket b → bit a b=true) := by decide +kernel
  have result := FiniteBinCollisionPopulation.band_fraction_bins (range 3) (fun p => bucket p) (by decide)
    (fun p _ => mem_range.mpr (table.1 p)) allHits (by
      intro p hp q hq order same
      have ok := FiniteBinCollisionPopulation.band_pair_eligible hp hq order
      obtain ⟨lo,_,_,pp,qp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp ok
      have nonzero {a : ℕ} (ap : a.Prime) (above : X≤a) : (a:ZMod 7)≠0 :=
        fun z => not_seven ap above ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp z)
      exact mem_filter.mpr ⟨ok,(energy_iff ok).mpr (table.2 p q (nonzero pp lo)
        (nonzero qp (lo.trans order.le)) same)⟩)
  simpa only [card_range,show 12*3=36 by decide] using result

end PrimeFactors.CyclotomicEnergySevenPopulation
