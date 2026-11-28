import PrimeFactors.ExactDyadicSumMenu
import PrimeFactors.ShiftedSquareSumCoverage

/-! An unconditional all-products bound for a menu chosen from the low
161 bits of the product. Count prime lifts of each residue using the five
odd primes dividing 15015 and normalize against the full prime population. -/
namespace PrimeFactors.UnconditionalSumMenuPopulation

open Finset DyadicSumMenuBudget
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open PrimeProductRegion (K)
open PrimeResidueRankTransfer (tail cell mem_tail)
open MixedPrefixSample (eligible primes)
open private PrimeFactors.ShiftedSquareSumCoverage.stripe from PrimeFactors.ShiftedSquareSumCoverage
open private PrimeFactors.MixedPrefixSample.mem_primes from PrimeFactors.MixedPrefixSample
open private PrimeFactors.ExtendedProductCosts.unit_of_prime from PrimeFactors.ExtendedProductCosts
open private PrimeFactors.DyadicFactorClueGain.one_class from PrimeFactors.DyadicFactorClueGain
open scoped Classical
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

abbrev R := ZMod (2^161)
abbrev Menu := R → Finset R

/-- Each sorted full-width prime pair is counted once. All pairs with the
same product suffix receive exactly the same menu. -/
noncomputable def hits (menu : Menu) := eligible.filter fun v =>
  ((v.1+v.2:ℕ):R) ∈ menu ((v.1*v.2:ℕ):R)

private abbrev slots := ((X-1)/(2^161*15015)+1)*5760
private abbrev peak := 5010795177*2^66

private theorem tail_cap (a : R) : (tail B X a).card≤slots := by
  apply (card_le_card (t:=primes.filter (fun q => q ≡ a.val [MOD 2^161])) ?_).trans
    (PrimeFactors.ShiftedSquareSumCoverage.stripe (by decide) (by decide : (2^161).Coprime 15015))
  intro q h
  obtain ⟨lo,hi,pr,eq⟩ := mem_tail.mp h
  have lt : q<B := lt_of_le_of_ne hi (fun same =>
    (Nat.Prime.not_prime_pow (by decide : 2≤1024) (x:=2)) ((congrArg Nat.Prime same).mp pr))
  refine mem_filter.mpr ⟨PrimeFactors.MixedPrefixSample.mem_primes.mpr ⟨⟨lo.le,lt⟩,pr⟩,?_⟩
  exact (ZMod.natCast_eq_natCast_iff ..).mp (eq.trans (ZMod.natCast_zmod_val a).symm)

private theorem cell_cap (v : R×R) : cell X B K v≤slots^2 := by
  unfold cell ThresholdPairCount.distinctRegion ThresholdPairCount.region
  apply (card_filter_le ..).trans ((card_filter_le ..).trans ?_)
  rw [card_product,pow_two]
  exact Nat.mul_le_mul (tail_cap _) (tail_cap _)

private theorem unit_count : Fintype.card (U 161)=2^160 := by
  rw [ZMod.card_units_eq_totient,Nat.totient_prime_pow_succ Nat.prime_two]
  norm_num

private theorem square_classes {e : ℕ} (le : 3≤e) : (univ.filter (fun r : U e => r.val.val%8=1)).card≤2^(e-3) := by
  have count := PrimeFactors.DyadicFactorClueGain.one_class (e:=e) (j:=3) le 1
  rw [←count]
  apply card_le_card_of_injOn (fun r : U e => r.val.val)
  · intro r hr
    have cl : r.val.val%8=1 := (mem_filter.mp hr).2
    apply mem_filter.mpr
    exact ⟨mem_range.mpr r.val.val_lt,show r.val.val%8=1 from cl⟩
  · intro a _ b _ eq
    exact Units.ext (ZMod.val_injective _ eq)

private theorem sum_caps {α : Type*} [Fintype α] (P : α→Prop) [DecidablePred P]
    (f : α→ℕ) {A C D H : ℕ} (bound : ∀ r,f r≤(if P r then A else 0)+C)
    (classes : (univ.filter P).card≤D) (total : Fintype.card α=H) :
    (∑ r,f r)≤D*A+H*C := by
  apply (sum_le_sum (fun r _ => bound r)).trans
  rw [sum_add_distrib,←sum_filter,sum_const,sum_const,card_univ,total]
  simpa only [nsmul_eq_mul,Nat.cast_id] using Nat.add_le_add_right
    (Nat.mul_le_mul_right A classes) (H*C)

private theorem masses (menu : Menu) (size : ∀ r : U 161,(menu r.val).card≤2^32) :
    (∑ r : U 161,mass r (menu r.val))≤2^158*peak + 2^160*2^35 := by
  have bound (r : U 161) : mass r (menu r.val)≤(if r.val.val%8=1 then peak else 0)+2^35 := by
    by_cases good : r.val.val%8=1
    · rw [if_pos good]
      exact ((ExactDyadicSumMenu.at_161 good).2 ⟨_,size r,rfl⟩).trans (Nat.le_add_right ..)
    · have flat := budget (T:=3) (by decide) (by decide : 3≤161) r (menu r.val)
      rw [if_neg good,zero_add] at flat ⊢
      exact flat.trans ((Nat.mul_le_mul_right 8 (size r)).trans_eq (by decide))
  exact sum_caps _ _ bound (square_classes (by decide : 3≤161)) unit_count

private theorem modular_count {e : ℕ} (menu : ZMod (2^e) → Finset (ZMod (2^e))) :
    (∑ v : U e × U e,if v.1.val+v.2.val∈menu (v.1*v.2).val then 1 else 0)=
      ∑ r : U e,mass r (menu r.val) := by
  let f (r a : U e) : ℕ := if a.val+(a⁻¹*r).val∈menu r.val then 1 else 0
  have regroup (a : U e) : (∑ b : U e,if a.val+b.val∈menu (a*b).val then 1 else 0)=
      ∑ r : U e,f r a := by
    calc
      _ = ∑ b : U e,f (a*b) a := by simp only [f,inv_mul_cancel_left]
      _ = _ := Equiv.sum_comp (Equiv.mulLeft a) (fun r : U e => f r a)
  rw [Fintype.sum_prod_type]
  simp_rw [regroup]
  rw [sum_comm]
  apply sum_congr rfl
  intro r _
  have row (s : ZMod (2^e)) : (univ.filter (fun a : U e => a.val+(a⁻¹*r).val=s)).card=
      PrimeSquareSumWeights.weight r.val.val s := by
    simpa only [sum_boole,Nat.cast_id] using DyadicSumGuessPopulation.count r s
  rw [mass]
  simp only [f,sum_boole,Nat.cast_id]
  rw [←sum_card_fiberwise_eq_card_filter univ (menu r.val) (fun a : U e => a.val+(a⁻¹*r).val)]
  simp only [row]

attribute [local irreducible] eligible cell hits

private theorem lift_menus {e : ℕ} (cap : 2^e≤2^161)
    (menu : ZMod (2^e) → Finset (ZMod (2^e))) (C : ℕ)
    (cells : ∀ v : ZMod (2^e) × ZMod (2^e),cell X B K v≤C) :
    2*(eligible.filter fun v => ((v.1+v.2:ℕ):ZMod (2^e))∈menu ((v.1*v.2:ℕ):ZMod (2^e))).card
      ≤ C*(∑ r : U e,mass r (menu r.val)) := by
  let cost (a b : ZMod (2^e)) : ℕ := if a+b∈menu (a*b) then 1 else 0
  have sym (a b : ZMod (2^e)) : cost a b=cost b a := by simp only [cost,add_comm a b,mul_comm a b]
  have twice := FiveSquareAllPrimeRanks.twice_cost cost sym (PrimeFactors.ExtendedProductCosts.unit_of_prime cap)
  have hit_eq (S : Finset (ℕ×ℕ)) : (∑ v∈S,cost v.1 v.2)=
      (S.filter fun v => ((v.1+v.2:ℕ):ZMod (2^e))∈menu ((v.1*v.2:ℕ):ZMod (2^e))).card := by
    simp only [cost,Nat.cast_mul,Nat.cast_add,sum_boole,Nat.cast_id]
  have mass_eq : (∑ v : U e × U e,cost v.1.val v.2.val)=∑ r : U e,mass r (menu r.val) :=
    modular_count menu
  rw [←hit_eq,twice,←mass_eq,mul_sum]
  exact sum_le_sum (fun v _ => Nat.mul_le_mul_right _ (cells _))

/-- Fewer than one in 2^45 eligible products has its true sum ending in
the menu. The budget applies separately to every odd product residue. -/
theorem rare (menu : Menu) (size : ∀ r : U 161,(menu r.val).card≤2^32) :
    2^45*(hits menu).card<eligible.card := by
  have pair_count : 2*(hits menu).card≤slots^2*(2^158*peak+2^160*2^35) := by
    rw [hits]
    exact (lift_menus (le_refl (2^161)) menu _ cell_cap).trans
      (Nat.mul_le_mul_left _ (masses menu size))
  have room : 2^45*21000000*(slots^2*(2^158*peak+2^160*2^35))≤2*2^2046 := by decide +kernel
  have scaled := Nat.mul_le_mul_left (2^45*21000000) pair_count
  have den := ChebyshevPrimeSample.eligible_count
  omega

end PrimeFactors.UnconditionalSumMenuPopulation
