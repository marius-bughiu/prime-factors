import PrimeFactors.DyadicFactorClueGain
import PrimeFactors.FactorClueSumGap
import PrimeFactors.QuarticLocalPopulation

/-! Average extra sum precision when the low k bits of one factor are supplied.
The population consists of all sorted distinct 1,024-bit primes with 2,048-bit
product. The prime-count estimates are explicit analytic hypotheses. -/
namespace PrimeFactors.DyadicClueMeanPopulation

open Finset DyadicFactorClueGain
open MixedPrefixSample (eligible)
open WideResiduePrimeSupply (B)
open FullRangeResidueEstimates (X)
open PrimeProductRegion (K)
open PrimeResidueRankTransfer (cell)
open private PrimeFactors.FullPopulationFavoredSums.mem_eligible from PrimeFactors.FullPopulationFavoredSums
open private PrimeFactors.QuarticLocalPopulation.relative from PrimeFactors.QuarticLocalPopulation
open private PrimeFactors.FiveSquareAllPrimeRanks.actual_weighted from PrimeFactors.FiveSquareAllPrimeRanks
open private PrimeFactors.ExtendedProductCosts.unit_of_prime from PrimeFactors.ExtendedProductCosts

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
abbrev period (k : ℕ) := 2^(k+1)
abbrev Unit (k : ℕ) := (ZMod (period k))ˣ

/-- Arithmetic mean of the number of additional bits in the greatest pinned
modulus, using exactly the canonical k-bit clue of the smaller factor. -/
noncomputable def meanGain (k : ℕ) : ℝ :=
  ((∑ v∈eligible,extra k (v.1%2^k) (v.1*v.2) : ℕ):ℝ)/eligible.card

private theorem factor_congr {k a b : ℕ} (kp : 1≤k) (N : ℕ) (same : a ≡ b [MOD period k]) :
    extra k a N=extra k b N := by
  have change {u v : ℕ} (eq : u ≡ v [MOD period k]) : extra k u N≤extra k v N := by
    have ⟨cap,h⟩ := (extra_iff kp u N _).mp (le_refl _)
    exact (extra_iff kp v N _).mpr ⟨cap,h.trans (((eq.pow 2).add (eq.mul_right (2^k))).of_dvd (pow_dvd_pow 2 cap))⟩
  exact Nat.le_antisymm (change same) (change same.symm)

private theorem canonical {k p q : ℕ} (po : Odd p) :
    extra k (p%2^k) (p*q)=extra k p (p*q) := by
  have cop := po.coprime_two_right.pow_right k
  have small : (p%2^k).Coprime (2^k) := by
    change (p%2^k).gcd (2^k)=1
    rw [←Nat.gcd_rec]
    exact cop.symm
  rw [extra,extra,FactorClueSumGap.gap_formula small ⟨p/2^k,(Nat.mod_add_div ..).symm⟩,
    FactorClueSumGap.gap_formula cop ⟨0,by simp⟩]

private theorem swap {k p q : ℕ} (kp : 1≤k) (po : Odd p) (qo : Odd q) :
    extra k p (p*q)=extra k q (q*p) := by
  have even : 2∣(2:ℕ)^k := by simpa using pow_dvd_pow 2 kp
  rw [extra,extra,FactorClueSumGap.gap_formula (po.coprime_two_right.pow_right k) ⟨0,by simp⟩,
    FactorClueSumGap.gap_formula (qo.coprime_two_right.pow_right k) ⟨0,by simp⟩,if_pos even]
  have turn : (p:ℤ)-q+(2^k:ℕ) ≡ -((q:ℤ)-p+(2^k:ℕ)) [ZMOD ((2*2^k:ℕ):ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-1,by push_cast; ring⟩
  have eq := FactorClueSumPrecision.gcd_of_congruent turn
  have g : Int.gcd ((p:ℤ)-q+(2^k:ℕ)) ((2*2^k:ℕ):ℤ)=Int.gcd ((q:ℤ)-p+(2^k:ℕ)) ((2*2^k:ℕ):ℤ) := by
    simpa only [Int.gcd,Int.natAbs_neg] using eq
  simp only [Nat.cast_mul,Nat.cast_ofNat] at g
  simp only [if_pos even,g]

/-- The statistic agrees whichever odd factor supplies its low bits. -/
theorem either_factor {k p q : ℕ} (kp : 1≤k) (po : Odd p) (qo : Odd q) :
    extra k (p%2^k) (p*q)=extra k (q%2^k) (p*q) := by
  calc
    _ = extra k q (q*p) := (canonical po).trans (swap kp po qo)
    _ = extra k (q%2^k) (q*p) := (canonical qo).symm
    _ = _ := by rw [Nat.mul_comm q p]

private noncomputable def cost (k : ℕ) (a b : ZMod (period k)) : ℕ :=
  if Odd a.val ∧ Odd b.val then extra k a.val (a.val*b.val) else 0

private theorem cost_sym {k : ℕ} (kp : 1≤k) (a b : ZMod (period k)) : cost k a b=cost k b a := by
  by_cases x : Odd a.val <;> by_cases y : Odd b.val <;> simp [cost,x,y,swap kp]

private theorem unit_odd {k : ℕ} (u : Unit k) : Odd u.val.val :=
  Nat.coprime_two_right.mp ((ZMod.val_coe_unit_coprime u).of_dvd_right (dvd_pow_self 2 (Nat.succ_ne_zero k)))

private theorem sum_units (k : ℕ) (f : ℕ→ℕ) :
    (∑ u : Unit k,f u.val.val)=∑ n∈products k,f n := by
  apply sum_bij (fun u _ => u.val.val)
  · intro u _
    exact mem_filter.mpr ⟨mem_range.mpr u.val.val_lt,Nat.odd_iff.mp (unit_odd u)⟩
  · intro a _ b _ eq
    exact Units.ext (ZMod.val_injective _ eq)
  · intro n hn
    obtain ⟨size,odd⟩ := mem_filter.mp hn
    let u := ZMod.unitOfCoprime n ((Nat.odd_iff.mpr odd).coprime_two_right.pow_right (k+1))
    exact ⟨u,mem_univ _,by rw [show u.val=(n:ZMod (period k)) from ZMod.coe_unitOfCoprime ..,ZMod.val_natCast,Nat.mod_eq_of_lt (mem_range.mp size)]⟩
  · intros; rfl

/-- Multiplication by the first unit permutes the possible product residues,
so each row has the same total, even though the factor clue varies over rows. -/
private theorem row {k : ℕ} (kp : 1≤k) (a : Unit k) :
    (∑ b : Unit k,cost k a.val b.val)=2^(k+1)-1 := by
  calc
    _ = ∑ b : Unit k,extra k a.val.val (a*b).val.val := by
      apply sum_congr rfl
      intro b _
      rw [cost,if_pos ⟨unit_odd a,unit_odd b⟩,Units.val_mul,ZMod.val_mul]
      exact extra_product_congr kp _ (Nat.mod_modEq ..).symm
    _ = ∑ b : Unit k,extra k a.val.val b.val.val := Equiv.sum_comp (Equiv.mulLeft a) (fun b : Unit k => extra k a.val.val b.val.val)
    _ = _ := (sum_units k (extra k a.val.val)).trans (total kp (unit_odd a))

private theorem uniform {k : ℕ} (kp : 1≤k) :
    (∑ v : Unit k × Unit k,(cost k v.1.val v.2.val:ℝ))/Fintype.card (Unit k × Unit k)=
      2-1/(2:ℝ)^k := by
  have card : Fintype.card (Unit k)=2^k := by simp [Unit,period,ZMod.card_units_eq_totient,Nat.totient_prime_pow_succ Nat.prime_two]
  have sums : (∑ v : Unit k × Unit k,cost k v.1.val v.2.val)=2^k*(2^(k+1)-1) := by
    rw [Fintype.sum_prod_type]
    simp only [row kp,sum_const,card_univ,card,nsmul_eq_mul,Nat.cast_id]
  rw [←Nat.cast_sum,sums,Fintype.card_prod,card]
  push_cast [Nat.one_le_two_pow]
  rw [pow_succ]
  field_simp
  ring

attribute [local irreducible] eligible cell

private theorem actual_eq {k : ℕ} (kp : 1≤k) : FiveSquareAllPrimeRanks.actual (cost k)=meanGain k := by
  have localCost (p q : ℕ) (po : Odd p) (qo : Odd q) :
      cost k p q=extra k (p%2^k) (p*q) := by
    have om (n : ℕ) (o : Odd n) : Odd (n%period k) := by
      apply Nat.odd_iff.mpr
      rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (Nat.succ_ne_zero k))]
      exact Nat.odd_iff.mp o
    have both : Odd (p%period k) ∧ Odd (q%period k) := ⟨om p po,om q qo⟩
    simp only [cost,ZMod.val_natCast,if_pos both,canonical po]
    exact (extra_product_congr kp _ ((Nat.mod_modEq p _).mul (Nat.mod_modEq q _))).trans
      (factor_congr kp _ (Nat.mod_modEq p _))
  unfold FiveSquareAllPrimeRanks.actual meanGain
  congr 2
  apply sum_congr rfl
  rintro ⟨p,q⟩ h
  obtain ⟨lo,lt,_,pp,qp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp h
  have two : 2<X := by decide
  exact localCost p q (pp.odd_of_ne_two (two.trans_le lo).ne') (qp.odd_of_ne_two ((two.trans_le lo).trans lt).ne')

/-- EHP Corollary 2 under Dirichlet GRH, at the single modulus 2^(k+1),
controls the mean additional guaranteed bits over the entire prime population. -/
theorem close {k : ℕ} (kp : 1≤k) (limit : k≤160) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints (period k) li) :
    |meanGain k-(2-1/(2:ℝ)^k)|≤(2-1/(2:ℝ)^k)/(2:ℝ)^146 := by
  have low : 3≤period k := (show 3≤2^2 by decide).trans (Nat.pow_le_pow_right (by decide) (by omega : 2≤k+1))
  have cap : period k≤2^161 := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨l,u,lp,scale,cells⟩ := ExtendedModulusPrimeSupply.cell_bounds low cap h
  rw [←actual_eq kp,PrimeFactors.FiveSquareAllPrimeRanks.actual_weighted (cost k) (cost_sym kp)
    (PrimeFactors.ExtendedProductCosts.unit_of_prime cap),←uniform kp]
  apply PrimeFactors.QuarticLocalPopulation.relative _ _ (l:=(l:ℝ)) (u:=(u:ℝ))
    (by exact_mod_cast lp) (by positivity) (by exact_mod_cast scale)
  · exact fun v => ⟨Nat.cast_le.mpr (cells v).1,Nat.cast_le.mpr (cells v).2⟩
  · exact fun _ => Nat.cast_nonneg _

theorem at_160 {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints (2^161) li) :
    |meanGain 160-(2-1/(2:ℝ)^160)|<1/(2:ℝ)^145 :=
  (close (by decide : 1≤160) (by decide) h).trans_lt (by norm_num)

end PrimeFactors.DyadicClueMeanPopulation
