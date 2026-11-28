import PrimeFactors.FixedProductCluePopulation
import PrimeFactors.FiveSquareOneSumGuess
import PrimeFactors.QuantileResidueBins
import PrimeFactors.ChebyshevPrimeSample

/-! One sum-remainder guess made from a fixed product remainder. Compare the
uniform modular fiber with actual sorted full-width prime pairs in that class. -/
namespace PrimeFactors.DyadicSumGuessPopulation

open Finset PrimeSquareSumWeights
open MixedPrefixSample (eligible)
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open PrimeProductRegion (K)
open PrimeResidueRankTransfer (cell)
open private PrimeFactors.FiveSquarePolicy.fiber from PrimeFactors.FiveSquarePolicy
open private PrimeFactors.FiveSquareOneSumGuess.indicator_mass from PrimeFactors.FiveSquareOneSumGuess
open private PrimeFactors.ExtendedProductCosts.unit_of_prime from PrimeFactors.ExtendedProductCosts
open private PrimeFactors.FiveSquareAllPrimeRanks.average_eq from PrimeFactors.FiveSquareAllPrimeRanks
open private PrimeFactors.QuarticLocalPopulation.relative from PrimeFactors.QuarticLocalPopulation
open private PrimeFactors.FullPopulationFavoredSums.mem_eligible from PrimeFactors.FullPopulationFavoredSums
open scoped Classical
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

variable {m : ℕ} [NeZero m]

/-- All sorted distinct 1,024-bit prime pairs with a 2,048-bit product in the
given class. A predictor receiving only that class must make one common guess. -/
noncomputable def population (r : (ZMod m)ˣ) := eligible.filter
  (fun v => ((v.1*v.2:ℕ):ZMod m)=r.val)

theorem dyadic_population {k : ℕ} (r : DyadicClueMeanPopulation.Unit k) :
    population r=FixedProductCluePopulation.population r := rfl

noncomputable def actual (r : (ZMod m)ˣ) (s : ZMod m) : ℝ :=
  (((population r).filter (fun v => ((v.1+v.2:ℕ):ZMod m)=s)).card:ℝ)/(population r).card

noncomputable def uniform (r : (ZMod m)ˣ) (s : ZMod m) : ℝ :=
  (weight r.val.val s:ℝ)/m.totient

private noncomputable abbrev w (r a : (ZMod m)ˣ) := cell X B K (a.val,(a⁻¹*r).val)

attribute [local irreducible] eligible cell

private theorem twice (limit : m≤2^161) (r : (ZMod m)ˣ) (f : ZMod m→ℕ) :
    2*(∑ v∈population r,f ((v.1+v.2:ℕ):ZMod m))=
      ∑ a : (ZMod m)ˣ,w r a*f (a.val+(a⁻¹*r).val) := by
  let cost (a b : ZMod m) := if a*b=r.val then f (a+b) else 0
  have symmetric (a b) : cost a b=cost b a := by simp [cost,mul_comm,add_comm]
  rw [population,sum_filter]
  simp only [Nat.cast_add,Nat.cast_mul]
  change 2*(∑ v∈eligible,cost v.1 v.2)=_
  rw [FiveSquareAllPrimeRanks.twice_cost cost symmetric
    (PrimeFactors.ExtendedProductCosts.unit_of_prime limit),Fintype.sum_prod_type]
  change (∑ a : (ZMod m)ˣ,∑ b : (ZMod m)ˣ,cell X B K (a.val,b.val)*cost a.val b.val)=_
  simp only [cost,←Units.val_mul,←Units.ext_iff,mul_ite,mul_zero]
  exact QuantileResidueBins.fiber_sum r (fun a b => cell X B K (a.val,b.val)*f (a.val+b.val))

/-- Choosing the first unit determines the other coordinate. -/
theorem count (r : (ZMod m)ˣ) (s : ZMod m) :
    (∑ a : (ZMod m)ˣ,if a.val+(a⁻¹*r).val=s then 1 else 0)=weight r.val.val s := by
  let f (v : Pairs r.val.val m) : ℕ := if sumOf v=s then 1 else 0
  exact ((PrimeFactors.FiveSquarePolicy.fiber r).sum_comp f).trans
    (PrimeFactors.FiveSquareOneSumGuess.indicator_mass (fun v : Pairs r.val.val m => sumOf v=s))

private theorem of_cells (limit : m≤2^161) (r : (ZMod m)ˣ)
    {l u F : ℕ} (lp : 0<l) (fp : 0<F) (scale : F*u≤(F+1)*l)
    (weights : ∀ a : (ZMod m)ˣ,l≤w r a ∧ w r a≤u) : 0<(population r).card ∧
    ∀ s : ZMod m, |actual r s-uniform r s|≤uniform r s/F := by
  have den : 2*(population r).card=∑ a : (ZMod m)ˣ,w r a := by
    simpa using twice limit r (fun _ => 1)
  have pos : 0<(population r).card := by
    have term := (weights 1).1.trans (single_le_sum (fun a _ => Nat.zero_le (w r a)) (mem_univ 1))
    rw [←den] at term
    omega
  refine ⟨pos,?_⟩
  intro s
  let f (x : ZMod m) : ℕ := if x=s then 1 else 0
  let c (a : (ZMod m)ˣ) := f (a.val+(a⁻¹*r).val)
  have localMean : (∑ a : (ZMod m)ˣ,(c a:ℝ))/Fintype.card (ZMod m)ˣ=uniform r s := by
    rw [←Nat.cast_sum,show (∑ a : (ZMod m)ˣ,c a)=weight r.val.val s from count r s,
      ZMod.card_units_eq_totient,uniform]
  have popMean := PrimeFactors.FiveSquareAllPrimeRanks.average_eq (population r)
    (fun v => f ((v.1+v.2:ℕ):ZMod m)) (w r) c (twice limit r f) den
  have hits (S : Finset (ℕ×ℕ)) :
      (∑ v∈S,f ((v.1+v.2:ℕ):ZMod m))=(S.filter (fun v => ((v.1+v.2:ℕ):ZMod m)=s)).card := by
    simp [f]
  rw [actual,←hits,popMean,←localMean]
  apply PrimeFactors.QuarticLocalPopulation.relative _ _ (l:=(l:ℝ)) (u:=(u:ℝ))
    (by exact_mod_cast lp) (by exact_mod_cast fp) (by exact_mod_cast scale)
  · exact fun a => ⟨Nat.cast_le.mpr (weights a).1,Nat.cast_le.mpr (weights a).2⟩
  · exact fun a => Nat.cast_nonneg _

/-- Every guess, simultaneously within the chosen product class. The
prime-count estimates are needed only at the observed modulus. -/
theorem conditional (low : 3≤m) (limit : m≤2^161) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints m li) (r : (ZMod m)ˣ) :
    0<(population r).card ∧ ∀ s : ZMod m,
      |actual r s-uniform r s|≤uniform r s/(2:ℝ)^146 := by
  obtain ⟨l,u,lp,scale,cells⟩ := ExtendedModulusPrimeSupply.cell_bounds low limit h
  exact_mod_cast of_cells limit r lp (by decide : 0<2^146) scale (fun a => cells (a,a⁻¹*r))

/-- One fixed guess suffices to attain the best conditional success rate. -/
noncomputable def best {α : Type*} [LinearOrder α] (f : ZMod m→α) :=
  (univ.image f).max' (univ_nonempty.image f)

theorem best_spec {α : Type*} [LinearOrder α] (f : ZMod m→α) :
    IsGreatest (Set.range f) (best f) := by
  constructor
  · obtain ⟨s,_,eq⟩ := mem_image.mp (max'_mem (univ.image f) (univ_nonempty.image f))
    exact ⟨s,eq⟩
  · rintro _ ⟨s,rfl⟩
    exact le_max' _ _ (mem_image.mpr ⟨s,mem_univ _,rfl⟩)

/-- Optimizing over all guesses preserves the relative error bound even
if equal modular weights acquire slightly different prime populations. -/
theorem optimum (low : 3≤m) (limit : m≤2^161) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints m li) (r : (ZMod m)ˣ) :
    let W := ((best (m:=m) (weight r.val.val) : ℕ):ℝ)/m.totient
    |best (actual r)-W|≤W/(2:ℝ)^146 := by
  let W := ((best (m:=m) (weight r.val.val) : ℕ):ℝ)/m.totient
  change |best (actual r)-W|≤W/(2:ℝ)^146
  have cap (s : ZMod m) : uniform r s≤W := div_le_div_of_nonneg_right
    (Nat.cast_le.mpr ((best_spec (m:=m) (weight r.val.val)).2 ⟨s,rfl⟩)) (Nat.cast_nonneg _)
  obtain ⟨a,ha⟩ := (best_spec (actual r)).1
  obtain ⟨b,hb⟩ := (best_spec (m:=m) (weight r.val.val)).1
  have wb : uniform r b=W := by unfold uniform W; rw [hb]
  have err := (conditional low limit h r).2
  have left := (abs_le.mp (err b)).1
  rw [wb] at left
  have near := (best_spec (actual r)).2 ⟨b,rfl⟩
  have right := (abs_le.mp (err a)).2
  have slide := div_le_div_of_nonneg_right (cap a) (show (0:ℝ)≤2^146 by positivity)
  apply abs_le.mpr
  constructor
  · linarith only [left,near]
  · linarith only [right,ha,cap a,slide]

/-- Unequal modular weights retain their strict ordering among actual prime
pairs whenever twice the larger weight fits within the inverse relative error. -/
theorem strict_order (low : 3≤m) (limit : m≤2^161) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints m li) (r : (ZMod m)ˣ) {a b : ZMod m}
    (less : weight r.val.val a<weight r.val.val b) (small : 2*weight r.val.val b≤2^146) :
    actual r a<actual r b := by
  let A : ℝ := weight r.val.val a
  let B' : ℝ := weight r.val.val b
  let T : ℝ := m.totient
  let F : ℝ := 2^146
  have one : A+1≤B' := by dsimp [A,B']; exact_mod_cast Nat.succ_le.mpr less
  have room : 2*B'≤F := by dsimp [B',F]; exact_mod_cast small
  have tp : 0<T := by dsimp [T]; exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  have fp : 0<F := by dsimp [F]; positivity
  have eps : A/F+B'/F<1 := by rw [←add_div,div_lt_one fp]; linarith only [room,one]
  have err := (conditional low limit h r).2
  have l : actual r a≤(A+A/F)/T := by
    have eq : (A+A/F)/T=A/T+(A/T)/F := by ring
    rw [eq]
    linarith only [(abs_le.mp (err a)).2,show uniform r a=A/T by rfl]
  have u : (B'-B'/F)/T≤actual r b := by
    have eq : (B'-B'/F)/T=B'/T-(B'/T)/F := by ring
    rw [eq]
    linarith only [(abs_le.mp (err b)).1,show uniform r b=B'/T by rfl]
  exact l.trans_lt ((div_lt_div_of_pos_right (by linarith only [eps,one]) tp).trans_le u)

/-- Each guess attaining the actual optimum must be among the modular
maximizers under the stated bound. Ties within that set may split. -/
theorem maximizer (low : 3≤m) (limit : m≤2^161) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints m li) (r : (ZMod m)ˣ) {s : ZMod m}
    (small : 2*best (m:=m) (weight r.val.val)≤2^146) (win : actual r s=best (actual r)) :
    weight r.val.val s=best (m:=m) (weight r.val.val) := by
  obtain ⟨a,ha⟩ := (best_spec (m:=m) (weight r.val.val)).1
  by_contra ne
  have lt := lt_of_le_of_ne ((best_spec (m:=m) (weight r.val.val)).2 ⟨s,rfl⟩) ne
  rw [←ha] at lt small
  have better := strict_order low limit h r lt small
  rw [win] at better
  exact (not_lt_of_ge ((best_spec (actual r)).2 ⟨a,rfl⟩)) better

/-- At zero or one observed bit all eligible products are in a single unit
class and the true sum is always zero modulo the observed modulus. -/
theorem tiny (small : m≤2) (r : (ZMod m)ˣ) (s : ZMod m) :
    population r=eligible ∧ actual r s=(if s=0 then 1 else 0) ∧ uniform r s=actual r s := by
  have nz := NeZero.ne m
  have cases' : m=1 ∨ m=2 := by omega
  have dm : m∣2 := by rcases cases' with h|h <;> simp [h]
  have tot : m.totient=1 := by rcases cases' with h|h <;> simp [h]
  letI : Subsingleton (ZMod m)ˣ := Fintype.card_le_one_iff_subsingleton.mp
    ((ZMod.card_units_eq_totient m).trans tot).le
  have rone : r.val=1 := congrArg Units.val (Subsingleton.elim r 1)
  have add : (1:ZMod m)+1=0 := by
    rw [show (1:ZMod m)+1=(2:ℕ) by norm_num,ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact dm
  have odd_one {p : ℕ} (o : Odd p) : (p:ZMod m)=1 := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff p 1 m).mpr ((show p ≡ 1 [MOD 2] from Nat.odd_iff.mp o).of_dvd dm)
  have ones {p q : ℕ} (ok : (p,q)∈eligible) : (p:ZMod m)=1 ∧ (q:ZMod m)=1 := by
    obtain ⟨lo,lt,_,pp,qp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp ok
    have two := (by decide : 2<X).trans_le lo
    exact ⟨odd_one (pp.odd_of_ne_two two.ne'),odd_one (qp.odd_of_ne_two (two.trans lt).ne')⟩
  have whole : population r=eligible := by
    apply filter_true_of_mem
    rintro ⟨p,q⟩ ok
    simpa [Nat.cast_mul,(ones ok).1,(ones ok).2] using rone.symm
  have hits : (eligible.filter (fun v => ((v.1+v.2:ℕ):ZMod m)=s))=
      eligible.filter (fun _ => s=0) := by
    apply filter_congr
    rintro ⟨p,q⟩ ok
    simp only [Nat.cast_add,(ones ok).1,(ones ok).2,add,eq_comm]
  have pp := MixedPrefixSample.denominator ChebyshevPrimeSample.prime_count
  have ep : (eligible.card:ℝ)≠0 := by exact_mod_cast (by omega : eligible.card≠0)
  have act : actual r s=(if s=0 then 1 else 0) := by
    rw [actual,whole,hits]
    by_cases zero : s=0 <;> simp [zero,ep]
  refine ⟨whole,act,?_⟩
  rw [act,uniform,tot,←count,Fintype.sum_subsingleton _ (1:(ZMod m)ˣ)]
  simp [rone,add,eq_comm]

/-- All dyadic depths from zero to 161, with no analytic input at the
two degenerate moduli. The modular denominator is the count of odd residues. -/
theorem dyadic {e : ℕ} (limit : e≤161) {li : ℕ→ℝ}
    (h : 2≤e → ExtendedModulusPrimeSupply.Endpoints (2^e) li) (r : (ZMod (2^e))ˣ) :
    0<(population r).card ∧ ∀ s : ZMod (2^e),
      |actual r s-uniform r s|≤uniform r s/(2:ℝ)^146 := by
  by_cases lo : 2≤e
  · exact conditional ((by decide : 3≤2^2).trans (Nat.pow_le_pow_right (by decide) lo))
      (Nat.pow_le_pow_right (by decide) limit) (h lo) r
  · have sm : 2^e≤2 := by interval_cases e <;> decide
    have pp := MixedPrefixSample.denominator ChebyshevPrimeSample.prime_count
    refine ⟨by rw [(tiny sm r 0).1]; omega,?_⟩
    intro s
    rw [(tiny sm r s).2.2,sub_self,abs_zero,(tiny sm r s).2.1]
    split <;> positivity

end PrimeFactors.DyadicSumGuessPopulation
