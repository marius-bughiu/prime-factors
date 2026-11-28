import PrimeFactors.DyadicClueMeanPopulation
import PrimeFactors.FixedProductClueTails
import PrimeFactors.FactorClueWidthProfile
import PrimeFactors.SingularDyadicClueSuffixes

/-! Conditional gain from a supplied low factor suffix on actual full-width
prime pairs sharing one specified product suffix. Each odd first-coordinate
residue has exactly one partner in the modular product fiber. -/
namespace PrimeFactors.FixedProductCluePopulation

open Finset DyadicFactorClueGain
open DyadicClueMeanPopulation (period Unit)
open MixedPrefixSample (eligible)
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open PrimeProductRegion (K)
open PrimeResidueRankTransfer (cell)
open private PrimeFactors.DyadicClueMeanPopulation.cost PrimeFactors.DyadicClueMeanPopulation.cost_sym
  PrimeFactors.DyadicClueMeanPopulation.canonical PrimeFactors.DyadicClueMeanPopulation.factor_congr
  PrimeFactors.DyadicClueMeanPopulation.unit_odd PrimeFactors.DyadicClueMeanPopulation.sum_units
  from PrimeFactors.DyadicClueMeanPopulation
open private PrimeFactors.FullPopulationFavoredSums.mem_eligible from PrimeFactors.FullPopulationFavoredSums
open private PrimeFactors.ExtendedProductCosts.unit_of_prime from PrimeFactors.ExtendedProductCosts
open private PrimeFactors.QuarticLocalPopulation.relative from PrimeFactors.QuarticLocalPopulation
open private PrimeFactors.FiveSquareAllPrimeRanks.average_eq from PrimeFactors.FiveSquareAllPrimeRanks
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

/-- Every sorted, distinct full-width prime pair in the fixed product class. -/
noncomputable def population {k : ℕ} (r : Unit k) : Finset (ℕ×ℕ) :=
  eligible.filter (fun v => ((v.1*v.2:ℕ):ZMod (period k))=r.val)

private abbrev gain (k : ℕ) (v : ℕ×ℕ) := extra k (v.1%2^k) (v.1*v.2)

/-- Mean of a nonnegative function of the true factor-clue gain in the class. -/
noncomputable def actual {k : ℕ} (r : Unit k) (f : ℕ→ℕ) : ℝ :=
  ((∑ v∈population r,f (gain k v):ℕ):ℝ)/(population r).card

private noncomputable abbrev wt {k : ℕ} (r a : Unit k) :=
  cell X B K (a.val,(a⁻¹*r).val)

attribute [local irreducible] eligible cell

private theorem cost_at {k : ℕ} (kp : 1≤k) (p q : ℕ) (po : Odd p) (qo : Odd q) :
    PrimeFactors.DyadicClueMeanPopulation.cost k p q=gain k (p,q) := by
  have om (n : ℕ) (o : Odd n) : Odd (n%period k) := by
    apply Nat.odd_iff.mpr
    rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (Nat.succ_ne_zero k))]
    exact Nat.odd_iff.mp o
  have both : Odd (p%period k) ∧ Odd (q%period k) := ⟨om p po,om q qo⟩
  simp only [PrimeFactors.DyadicClueMeanPopulation.cost,ZMod.val_natCast,if_pos both,gain,
    PrimeFactors.DyadicClueMeanPopulation.canonical po]
  exact (extra_product_congr kp _ ((Nat.mod_modEq p _).mul (Nat.mod_modEq q _))).trans
    (PrimeFactors.DyadicClueMeanPopulation.factor_congr kp _ (Nat.mod_modEq p _))

/-- The fixed-product cell count with any gain weight, before normalization.
The factor of two converts unordered distinct prime pairs into ordered ones. -/
private theorem twice {k : ℕ} (kp : 1≤k) (limit : k≤160) (r : Unit k) (f : ℕ→ℕ) :
    2*(∑ v∈population r,f (gain k v))=
      ∑ a : Unit k, wt r a*f (extra k (a.val.val%2^k) r.val.val) := by
  let cost (x y : ZMod (period k)) := if x*y=r.val then f (PrimeFactors.DyadicClueMeanPopulation.cost k x y) else 0
  have sym (a b) : cost a b=cost b a := by
    simp only [cost,mul_comm a b,PrimeFactors.DyadicClueMeanPopulation.cost_sym kp a b]
  have cap : period k≤2^161 := Nat.pow_le_pow_right (by decide) (by omega)
  have split := FiveSquareAllPrimeRanks.twice_cost cost sym (PrimeFactors.ExtendedProductCosts.unit_of_prime cap)
  have left : (∑ v∈population r,f (gain k v))=∑ v∈eligible,cost v.1 v.2 := by
    rw [population,sum_filter]
    apply sum_congr rfl
    rintro ⟨p,q⟩ good
    obtain ⟨lo,ord,_,pp,qp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp good
    have two : 2<X := by decide
    simp only [cost,Nat.cast_mul,cost_at kp p q (pp.odd_of_ne_two (two.trans_le lo).ne')
      (qp.odd_of_ne_two ((two.trans_le lo).trans ord).ne')]
  rw [left,split,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  have partner (b : Unit k) : a.val*b.val=r.val ↔ b=a⁻¹*r := by
    change (↑(a*b) : ZMod (period k))=↑r ↔ _
    rw [←Units.ext_iff]
    exact eq_inv_mul_iff_mul_eq.symm
  have same : a.val.val*(a⁻¹*r).val.val ≡ r.val.val [MOD period k] := by
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    simp only [Nat.cast_mul,ZMod.natCast_zmod_val]
    exact (partner _).mpr rfl
  simp only [cost,partner,mul_ite,mul_zero,sum_ite_eq',mem_univ,if_true]
  apply congrArg (_ * ·)
  apply congrArg f
  rw [PrimeFactors.DyadicClueMeanPopulation.cost,if_pos ⟨PrimeFactors.DyadicClueMeanPopulation.unit_odd a,
    PrimeFactors.DyadicClueMeanPopulation.unit_odd _⟩]
  exact ((PrimeFactors.DyadicClueMeanPopulation.canonical (PrimeFactors.DyadicClueMeanPopulation.unit_odd a)).symm).trans
    (extra_product_congr kp _ same)

private noncomputable abbrev suffixes := FixedProductClueTails.suffixes

private theorem sum_lifts {k : ℕ} (kp : 1≤k) (f : ℕ→ℕ) :
    (∑ a : Unit k,f (a.val.val%2^k))=2*∑ n∈suffixes k,f n := by
  rw [PrimeFactors.DyadicClueMeanPopulation.sum_units k (fun a => f (a%2^k)),products,suffixes,FixedProductClueTails.suffixes,sum_filter,sum_filter,
    pow_succ,Nat.mul_two,sum_range_add,two_mul]
  apply congrArg₂ (·+·) <;> apply sum_congr rfl <;> intro i hi
  · rw [Nat.mod_eq_of_lt (mem_range.mp hi)]
    exact if_congr Nat.odd_iff.symm rfl rfl
  · have even : 2∣(2:ℕ)^k := dvd_pow_self 2 (by omega)
    rw [Nat.add_mod (2^k) i 2,Nat.mod_eq_zero_of_dvd even,zero_add,Nat.mod_mod,
      Nat.add_mod_left,Nat.mod_eq_of_lt (mem_range.mp hi)]
    exact if_congr Nat.odd_iff.symm rfl rfl

private theorem unit_card (k : ℕ) : Fintype.card (Unit k)=2^k := by
  simp [DyadicClueMeanPopulation.Unit,period,ZMod.card_units_eq_totient,Nat.totient_prime_pow_succ Nat.prime_two]

/-- The exact conditional mean on uniform unit-coordinate pairs, before
transferring their weights to the actual prime population. -/
private noncomputable def uniform {k : ℕ} (r : Unit k) (f : ℕ→ℕ) : ℝ :=
  ((2*∑ a∈suffixes k,f (extra k a r.val.val):ℕ):ℝ)/(2:ℝ)^k

private theorem uniform_eq {k : ℕ} (kp : 1≤k) (r : Unit k) (f : ℕ→ℕ) :
    uniform r f=(∑ a : Unit k,(f (extra k (a.val.val%2^k) r.val.val):ℝ))/Fintype.card (Unit k) := by
  rw [uniform,←sum_lifts kp (fun a => f (extra k a r.val.val)),←Nat.cast_sum,unit_card]
  push_cast
  rfl

private theorem conditional {k : ℕ} (kp : 1≤k) (limit : k≤160) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints (period k) li) (r : Unit k) (f : ℕ→ℕ) :
    0<(population r).card ∧ |actual r f-uniform r f|≤uniform r f/(2:ℝ)^146 := by
  have lo : 3≤period k := (show 3≤2^2 by decide).trans (Nat.pow_le_pow_right (by decide) (by omega : 2≤k+1))
  have cap : period k≤2^161 := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨l,u,lp,scale,cells⟩ := ExtendedModulusPrimeSupply.cell_bounds lo cap h
  have weights (a : Unit k) : l≤wt r a ∧ wt r a≤u := cells (a,a⁻¹*r)
  have denominator : 2*(population r).card=∑ a : Unit k, wt r a := by simpa using twice kp limit r (fun _ => 1)
  have pos : 0<(population r).card := by
    have wd : wt r 1≤∑ a : Unit k,wt r a := single_le_sum (fun a _ => Nat.zero_le (wt r a)) (mem_univ 1)
    rw [←denominator] at wd
    have := lp.trans_le ((weights 1).1.trans wd)
    omega
  refine ⟨pos,?_⟩
  rw [actual,PrimeFactors.FiveSquareAllPrimeRanks.average_eq _ _ _ _ (twice kp limit r f) denominator,uniform_eq kp]
  apply PrimeFactors.QuarticLocalPopulation.relative _ _ (l:=(l:ℝ)) (u:=(u:ℝ))
    (by exact_mod_cast lp) (by positivity) (by exact_mod_cast scale)
  · exact fun a => ⟨Nat.cast_le.mpr (weights a).1,Nat.cast_le.mpr (weights a).2⟩
  · exact fun _ => Nat.cast_nonneg _

/-- Prime pairs in the fixed class whose true factor suffix supplies the
maximum possible k+1 extra bits, equivalently pinning 2k+1 sum bits. -/
noncomputable def hits {k : ℕ} (r : Unit k) := (population r).filter
  (fun v => FactorClueSumPrecision.greatest (v.1*v.2) (v.1%2^k) (2^k)=2^(2*k+1))

private theorem max_gain {k : ℕ} (kp : 1≤k) (a N : ℕ) :
    extra k a N=k+1 ↔ FactorClueSumPrecision.greatest N a (2^k)=2^(2*k+1) := by
  rw [greatest_eq kp,Nat.pow_right_inj (by decide : 1<(2:ℕ))]
  omega

private theorem hit_mean {k : ℕ} (kp : 1≤k) (r : Unit k) :
    actual r (fun j => if j=k+1 then 1 else 0)=((hits r).card:ℝ)/(population r).card := by
  have count (S : Finset (ℕ×ℕ)) :
      (∑ v∈S,if gain k v=k+1 then 1 else 0 : ℕ)=
        (S.filter (fun v => FactorClueSumPrecision.greatest (v.1*v.2) (v.1%2^k) (2^k)=2^(2*k+1))).card := by
    simp only [gain,max_gain kp,sum_boole,Nat.cast_id]
  exact congrArg (fun z : ℕ => (z:ℝ)/(population r).card) (count (population r))

private theorem uniform_hit {k : ℕ} (kp : 3≤k) (r : Unit k) (good : r.val.val%8=1) :
    uniform r (fun j => if j=k+1 then 1 else 0)=4/(2:ℝ)^k := by
  have pos : 1≤k := by omega
  have odd := PrimeFactors.DyadicClueMeanPopulation.unit_odd r
  have selected : (suffixes k).filter (fun a => extra k a r.val.val=k+1)=TwoMaximalClueSuffixes.menu k r.val.val := by
    ext a
    simp only [suffixes,FixedProductClueTails.suffixes,mem_filter,mem_range,max_gain pos,TwoMaximalClueSuffixes.mem_maximum pos odd,and_assoc]
  rw [uniform,sum_boole,Nat.cast_id,selected,TwoMaximalClueSuffixes.card_menu kp odd,if_pos good]
  norm_num

/-- Within each admissible fixed product class, the chance that the true
factor suffix supplies the maximum gain has relative error at most 2⁻¹⁴⁶. -/
theorem maximum {k : ℕ} (kp : 3≤k) (limit : k≤160) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints (period k) li) (r : Unit k) (good : r.val.val%8=1) :
    0<(population r).card ∧ |((hits r).card:ℝ)/(population r).card-4/(2:ℝ)^k|≤(4/(2:ℝ)^k)/(2:ℝ)^146 := by
  simpa only [hit_mean (by omega : 1≤k),uniform_hit kp r good] using
    conditional (by omega : 1≤k) limit h r (fun j => if j=k+1 then 1 else 0)

theorem maximum_160 {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints (2^161) li)
    (r : Unit 160) (good : r.val.val%8=1) : 0<(population r).card ∧
    |((hits r).card:ℝ)/(population r).card-1/(2:ℝ)^158|≤1/(2:ℝ)^304 := by
  simpa only [show (4:ℝ)/2^160=1/2^158 by norm_num,show ((1:ℝ)/2^158)/2^146=1/2^304 by norm_num] using
    maximum (by decide : 3≤160) (by decide) h r good

private theorem uniform_mean {k : ℕ} (kp : 3≤k) (r : Unit k) (good : r.val.val%8=1) :
    uniform r id=4-4/(2:ℝ)^k := by
  have room : 2≤(2:ℕ)^(k+1) := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega : 1≤k+1)
  simp only [uniform,id_eq,suffixes,FixedProductClueTails.total_one_mod_eight kp good,Nat.cast_mul,
    Nat.cast_sub room,Nat.cast_pow,Nat.cast_ofNat]
  rw [pow_succ]
  field_simp
  ring

/-- Mean additional pinned sum bits at each retained fixed product suffix.
The explicit prime-count estimates affect only the transfer to actual primes. -/
theorem mean {k : ℕ} (kp : 3≤k) (limit : k≤160) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints (period k) li) (r : Unit k) (good : r.val.val%8=1) :
    0<(population r).card ∧ |actual r id-(4-4/(2:ℝ)^k)|≤(4-4/(2:ℝ)^k)/(2:ℝ)^146 := by
  simpa only [uniform_mean kp r good] using conditional (by omega : 1≤k) limit h r id

theorem mean_160 {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints (2^161) li)
    (r : Unit 160) (good : r.val.val%8=1) :
    |actual r id-(4-1/(2:ℝ)^158)|<1/(2:ℝ)^144 := by
  have estimate := (mean (by decide : 3≤160) (by decide) h r good).2
  rw [show (4:ℝ)/2^160=1/2^158 by norm_num] at estimate
  exact estimate.trans_lt (by norm_num)

open private PrimeFactors.FactorClueWidthProfile.half_ne PrimeFactors.FactorClueWidthProfile.shift_zero
  from PrimeFactors.FactorClueWidthProfile

/-- The two factors agree through k+1 low bits. -/
noncomputable def singularHits {k : ℕ} (r : Unit k) := (population r).filter
  (fun v => v.1 ≡ v.2 [MOD 2^(k+1)])

private theorem odd_first {k p q : ℕ} {r : Unit k} (mem : (p,q)∈population r) :
    Odd p ∧ p<q := by
  obtain ⟨lo,ord,_,pp,_,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp (mem_filter.mp mem).1
  exact ⟨pp.odd_of_ne_two ((by decide : 2<X).trans_le lo).ne',ord⟩

/-- The singular event is precisely membership of the true supplied factor
suffix in the publicly defined singular menu. -/
theorem mem_singularHits {k p q : ℕ} (hk : 1≤k) (r : Unit k) :
    (p,q)∈singularHits r ↔ (p,q)∈population r ∧
      p%2^k ∈ SingularDyadicClueSuffixes.menu k (p*q) := by
  rw [singularHits,mem_filter]
  exact and_congr_right fun mem => (SingularDyadicClueSuffixes.true_suffix hk (odd_first mem).1).symm

private theorem singular_gain {k p q : ℕ} (hk : 1≤k) (po : Odd p) (ord : p<q) :
    gain k (p,q)=k ↔ p ≡ q [MOD 2^(k+1)] := by
  obtain ⟨t,gap⟩ := FactorClueWidthProfile.exists_gap ord
  change FactorClueWidthProfile.gain k p q=k ↔ _
  rw [FactorClueWidthProfile.profile hk po gap]
  change q ≡ p+2^t [MOD 2^(t+1)] at gap
  by_cases lt : k<t
  · have equal : q ≡ p [MOD 2^(k+1)] :=
      (gap.of_dvd (pow_dvd_pow 2 (by omega : k+1≤t+1))).trans
        (PrimeFactors.FactorClueWidthProfile.shift_zero p lt)
    simp [lt.ne,min_eq_left lt.le,equal.symm]
  · have different : ¬p ≡ q [MOD 2^(k+1)] := fun eq =>
      PrimeFactors.FactorClueWidthProfile.half_ne p t
        (((eq.of_dvd (pow_dvd_pow 2 (by omega : t+1≤k+1))).trans gap).symm)
    simp only [different,iff_false]
    split_ifs <;> omega

private theorem singular_mean {k : ℕ} (hk : 1≤k) (r : Unit k) :
    actual r (fun j => if j=k then 1 else 0)=((singularHits r).card:ℝ)/(population r).card := by
  unfold actual
  apply congrArg (fun z : ℕ => (z:ℝ)/(population r).card)
  rw [sum_boole,Nat.cast_id,singularHits]
  congr 1
  apply filter_congr
  rintro ⟨p,q⟩ mem
  exact singular_gain hk (odd_first mem).1 (odd_first mem).2

/-- Among every admissible fixed product suffix, the singular event has
the same modular frequency as maximum gain, with separately bounded
prime-population transfer error. -/
theorem singular {k : ℕ} (hk : 3≤k) (limit : k≤160) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints (period k) li) (r : Unit k) (good : r.val.val%8=1) :
    0<(population r).card ∧
    |((singularHits r).card:ℝ)/(population r).card-4/(2:ℝ)^k|≤(4/(2:ℝ)^k)/(2:ℝ)^146 := by
  have val : uniform r (fun j => if j=k then 1 else 0)=4/(2:ℝ)^k := by
    rw [uniform,sum_boole,Nat.cast_id,suffixes,FixedProductClueTails.exact_one_mod_eight hk good hk le_rfl]
    simp [show k+1-k=1 by omega]
  simpa only [singular_mean (by omega : 1≤k),val] using
    conditional (by omega : 1≤k) limit h r (fun j => if j=k then 1 else 0)

theorem singular_160 {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints (2^161) li)
    (r : Unit 160) (good : r.val.val%8=1) : 0<(population r).card ∧
    |((singularHits r).card:ℝ)/(population r).card-1/(2:ℝ)^158|≤1/(2:ℝ)^304 := by
  simpa only [show (4:ℝ)/2^160=1/2^158 by norm_num,show ((1:ℝ)/2^158)/2^146=1/2^304 by norm_num] using
    singular (by decide : 3≤160) (by decide) h r good

end PrimeFactors.FixedProductCluePopulation
