import PrimeFactors.QuarticLocalPopulation
import PrimeFactors.FactorClueSumGap

/-! The population of full-width prime pairs differing by exactly half a
period modulo 2^(k+1). The count of residue cells is exact. Transferring
their weights to prime pairs uses the explicit EHP endpoint hypotheses. -/
namespace PrimeFactors.MaximalFactorCluePopulation

open Finset
open MixedPrefixSample (eligible)
open PrimeResidueRankTransfer (cell)
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open PrimeProductRegion (K)
open private PrimeFactors.QuarticLocalPopulation.relative from PrimeFactors.QuarticLocalPopulation
open private PrimeFactors.ExtendedProductCosts.unit_of_prime from PrimeFactors.ExtendedProductCosts
open private PrimeFactors.FiveSquareAllPrimeRanks.actual_weighted from PrimeFactors.FiveSquareAllPrimeRanks
open private PrimeFactors.FullPopulationFavoredSums.mem_eligible from PrimeFactors.FullPopulationFavoredSums
open scoped Classical

set_option exponentiation.threshold 4096
attribute [local irreducible] eligible cell

abbrev modulus (k : ℕ) := 2^(k+1)
abbrev Unit (k : ℕ) := (ZMod (modulus k))ˣ
noncomputable abbrev delta (k : ℕ) : ZMod (modulus k) := ((2^k:ℕ):ZMod (modulus k))

noncomputable def locus (k : ℕ) := eligible.filter (fun v => v.1 ≡ v.2+2^k [MOD modulus k])

theorem mem_locus {p q k : ℕ} : (p,q)∈locus k ↔
    (p,q)∈eligible ∧ p ≡ q+2^k [MOD 2^(k+1)] := mem_filter

private theorem twice_delta (k : ℕ) : delta k+delta k=0 := by
  rw [←Nat.cast_add,show 2^k+2^k=modulus k by simp [modulus,pow_succ,Nat.mul_two]]
  exact ZMod.natCast_self _

private theorem flip {k : ℕ} {a b : ZMod (modulus k)} (h : a=b+delta k) : b=a+delta k := by
  rw [h,add_assoc,twice_delta,add_zero]

private theorem unit_shift {k : ℕ} (kp : 0<k) (a : Unit k) : IsUnit ((a:ZMod _)+delta k) := by
  have odd := Nat.coprime_two_right.mp ((ZMod.val_coe_unit_coprime a).of_dvd_right
    (dvd_pow_self 2 (Nat.succ_ne_zero k)))
  have still := odd.add_even ((by decide : Even (2:ℕ)).pow_of_ne_zero kp.ne')
  have unit := (ZMod.isUnit_iff_coprime (a.val.val+2^k) (modulus k)).mpr
    (still.coprime_two_right.pow_right (k+1))
  simpa only [Nat.cast_add,ZMod.natCast_zmod_val] using unit

noncomputable def mark (k : ℕ) (a b : ZMod (modulus k)) : ℕ :=
  if a=b+delta k then 1 else 0

private theorem mark_sym (k : ℕ) (a b : ZMod (modulus k)) : mark k a b=mark k b a :=
  if_congr ⟨flip,flip⟩ rfl rfl

theorem unit_count (k : ℕ) : Fintype.card (Unit k)=2^k := by
  simp [Unit,modulus,ZMod.card_units_eq_totient,Nat.totient_prime_pow_succ Nat.prime_two]

/-- Each odd class has exactly one partner after shifting by half the period.
Thus 2^k ordered cells qualify out of 2^(2k). -/
theorem graph_count {k : ℕ} (kp : 0<k) :
    (∑ v : Unit k × Unit k,mark k v.1 v.2)=2^k := by
  have row (a : Unit k) : (∑ b : Unit k,mark k a b)=1 := by
    obtain ⟨u,hu⟩ := unit_shift kp a
    calc
      _ = ∑ b : Unit k, if b=u then 1 else 0 := by
        apply sum_congr rfl
        intro b _
        rw [mark_sym,mark,←hu]
        exact if_congr Units.ext_iff.symm rfl rfl
      _ = 1 := by simp
  rw [Fintype.sum_prod_type]
  simpa only [row,sum_const,card_univ,nsmul_eq_mul,mul_one] using unit_count k

private theorem count_selected (k : ℕ) (s : Finset (ℕ×ℕ)) :
    (∑ v∈s,mark k v.1 v.2)=(s.filter (fun v => v.1 ≡ v.2+2^k [MOD modulus k])).card := by
  have change_mark (a b : ℕ) : mark k a b=if a ≡ b+2^k [MOD modulus k] then 1 else 0 := by
    simp only [mark,delta,←Nat.cast_add,ZMod.natCast_eq_natCast_iff]
  simp [change_mark]

private theorem share_eq (k : ℕ) : FiveSquareAllPrimeRanks.actual (mark k)=
    ((locus k).card:ℝ)/eligible.card := by
  unfold FiveSquareAllPrimeRanks.actual
  rw [count_selected]
  rfl

/-- Relative error at most 2^-146 throughout the established modulus range.
The denominator counts sorted distinct 1,024-bit primes with a 2,048-bit product. -/
theorem close {k : ℕ} (kp : 1≤k) (limit : k≤160) {li : ℕ→ℝ}
    (ehp : ExtendedModulusPrimeSupply.Endpoints (2^(k+1)) li) :
    |((locus k).card:ℝ)/eligible.card-1/(2:ℝ)^k| ≤ (1/(2:ℝ)^k)/(2:ℝ)^146 := by
  have low : 3≤modulus k := (show 3≤2^2 by decide).trans
    (Nat.pow_le_pow_right (by decide) (by omega : 2≤k+1))
  have cap : modulus k≤2^161 := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨l,u,lp,scale,cells⟩ := ExtendedModulusPrimeSupply.cell_bounds low cap ehp
  let w (v : Unit k × Unit k) : ℝ := cell X B K (v.1.val,v.2.val)
  let c (v : Unit k × Unit k) : ℝ := mark k v.1 v.2
  have mean : (∑ v,c v)/Fintype.card (Unit k × Unit k)=1/(2:ℝ)^k := by
    simp only [c,←Nat.cast_sum,graph_count kp,Fintype.card_prod,unit_count,Nat.cast_mul,
      Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  rw [←share_eq,PrimeFactors.FiveSquareAllPrimeRanks.actual_weighted (mark k) (mark_sym k)
    (PrimeFactors.ExtendedProductCosts.unit_of_prime cap),←mean]
  apply PrimeFactors.QuarticLocalPopulation.relative w c (l:=(l:ℝ)) (u:=(u:ℝ))
    (by exact_mod_cast lp) (by positivity) (by exact_mod_cast scale)
  · exact fun v => ⟨Nat.cast_le.mpr (cells v).1,Nat.cast_le.mpr (cells v).2⟩
  · exact fun _ => Nat.cast_nonneg _

/-- Giving p modulo 2^k fixes one sum class at the largest possible
precision precisely on the previously counted pairs. -/
noncomputable def precisionLocus (k : ℕ) := eligible.filter (fun v =>
  FactorClueSumPrecision.greatest (v.1*v.2) (v.1%2^k) (2^k)=2^(2*k+1))

theorem precision_eq {k : ℕ} (kp : 0<k) : precisionLocus k=locus k := by
  apply filter_congr
  rintro ⟨p,q⟩ ok
  obtain ⟨pl,_,_,pp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp ok
  have p2 := (by decide +kernel : 2<X).trans_le pl
  exact FactorClueSumGap.dyadic_maximum kp
    (Nat.odd_iff.mpr (pp.eq_two_or_odd.resolve_left (ne_of_gt p2)))

theorem precision_close {k : ℕ} (kp : 1≤k) (limit : k≤160) {li : ℕ→ℝ}
    (ehp : ExtendedModulusPrimeSupply.Endpoints (2^(k+1)) li) :
    |((precisionLocus k).card:ℝ)/eligible.card-1/(2:ℝ)^k| ≤ (1/(2:ℝ)^k)/(2:ℝ)^146 := by
  rw [precision_eq kp]
  exact close kp limit ehp

/-- At 160 supplied bits, the maximum 321 fixed sum bits occur with
frequency 2^-160 to absolute error at most 2^-306. -/
theorem precision_160 {li : ℕ→ℝ} (ehp : ExtendedModulusPrimeSupply.Endpoints (2^161) li) :
    |((eligible.filter (fun v => FactorClueSumPrecision.greatest (v.1*v.2)
        (v.1%2^160) (2^160)=2^321)).card:ℝ)/eligible.card-1/(2:ℝ)^160| ≤ 1/(2:ℝ)^306 := by
  exact (precision_close (k:=160) (by decide) (by decide) ehp).trans (by norm_num)

end PrimeFactors.MaximalFactorCluePopulation
