import PrimeFactors.DyadicSumGuessPopulation
import PrimeFactors.DyadicSumPeak
import PrimeFactors.DyadicPairSumWeight

/-! The total mass of a menu of sum guesses for a fixed odd dyadic
product. Count long factor-gap agreement once across the entire menu. -/
namespace PrimeFactors.DyadicSumMenuBudget

open Finset PrimeSquareSumWeights
open private PrimeFactors.FixedProductClueTails.criterion from PrimeFactors.FixedProductClueTails
open private PrimeFactors.DyadicClueMeanPopulation.sum_units from PrimeFactors.DyadicClueMeanPopulation
open scoped Classical
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

abbrev U (e : ℕ) := (ZMod (2^e))ˣ
private abbrev label {e : ℕ} (r a : U e) := a.val+(a⁻¹*r).val
private abbrev deep {e : ℕ} (r : U e) (T : ℕ) (a : U e) := a.val.val^2 ≡ r.val.val [MOD 2^T]

/-- The long-gap event consists of the roots of the product at the cutoff.
There are four roots modulo 2^T on the square branch and none elsewhere. -/
theorem deep_count {e T : ℕ} (low : 3≤T) (enough : T≤e) (r : U e) :
    (univ.filter (deep r T)).card=if r.val.val%8=1 then 4*2^(e-T) else 0 := by
  let N := r.val.val
  let f (x : ℕ) := if x^2 ≡ N [MOD 2^T] then 1 else 0
  have link : (univ.filter (deep r T)).card=∑ a : U e,f a.val.val := by
    simp [f,deep,N]
  rw [link]
  have table : (∑ a : U e,f a.val.val)=∑ x∈FixedProductClueTails.suffixes e,f x := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e≠0)
    rw [PrimeFactors.DyadicClueMeanPopulation.sum_units k f]
    apply sum_congr _ (fun _ _ => rfl)
    ext x
    simp [DyadicFactorClueGain.products,FixedProductClueTails.suffixes,Nat.odd_iff]
  rw [table]
  have eq : ((FixedProductClueTails.suffixes e).filter (fun x => x^2 ≡ N [MOD 2^T]))=
      FixedProductClueTails.tail e N T := by
    apply filter_congr
    intro a ha
    have ao := (mem_filter.mp ha).2
    have vanish : (2:ℕ)^e ≡ 0 [MOD 2^T] := Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 enough)
    rw [PrimeFactors.FixedProductClueTails.criterion (by omega : 1≤e) (by omega : T≤e+1) ao]
    exact ⟨fun h => h.symm.trans (by simpa using (vanish.symm.add_left (a^2))),
      fun h => ((by simpa using (vanish.symm.add_left (a^2))) : a^2 ≡ a^2+2^e [MOD 2^T]).trans h.symm⟩
  simp only [f,sum_boole,Nat.cast_id,eq]
  by_cases good : N%8=1
  · rw [if_pos good,FixedProductClueTails.tail_one_mod_eight (by omega) good low (by omega),
      show e+2-T=2+(e-T) by omega,pow_add]
    rfl
  · rw [if_neg good]
    apply card_eq_zero.mpr
    apply eq_empty_of_forall_not_mem
    intro a ha
    obtain ⟨aIn,reaches⟩ := mem_filter.mp ha
    have o := (mem_filter.mp aIn).2
    have obs := PrimeFactors.FixedProductClueTails.criterion (k:=e) (N:=N) (j:=3)
      (by omega) (by omega) o
    have n1 := obs.mp (low.trans reaches)
    have div : 8∣2^e := pow_dvd_pow 2 (by omega : 3≤e)
    obtain ⟨v,eqv⟩ := o
    have sq : a^2%8=1 := by
      rw [eqv]; rcases Nat.even_or_odd v with ⟨b,rfl⟩ | ⟨b,rfl⟩ <;> ring_nf <;> omega
    exact good (by simpa [Nat.ModEq,Nat.add_mod,sq,Nat.mod_eq_zero_of_dvd div] using n1)

private theorem split_count {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α→β) (P : α→Prop) [DecidablePred P] (A : Finset β) (d : ℕ)
    (cap : ∀ a, ¬P a → (univ.filter (fun x => f x=f a)).card≤d) :
    (univ.filter (fun x => f x∈A)).card≤(univ.filter P).card+A.card*d := by
  classical
  let L := univ.filter fun x => ¬P x
  have cover : univ.filter (fun x => f x∈A) ⊆ univ.filter P ∪ L.filter (fun x => f x∈A) := by
    intro x hx
    by_cases h : P x
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,h⟩,(mem_filter.mp hx).2⟩)
  have small (s : β) : (L.filter (fun x => f x=s)).card≤d := by
    by_cases occupied : (L.filter (fun x => f x=s)).Nonempty
    · obtain ⟨x,hx⟩ := occupied
      obtain ⟨lx,eq⟩ := mem_filter.mp hx
      rw [←eq]
      exact (card_le_card (filter_subset_filter _ (subset_univ L))).trans (cap x (mem_filter.mp lx).2)
    · simp [not_nonempty_iff_eq_empty.mp occupied]
  apply ((card_le_card cover).trans (card_union_le ..)).trans
  apply Nat.add_le_add_left
  rw [←sum_card_fiberwise_eq_card_filter L A f]
  simpa using sum_le_sum (fun s (_ : s∈A) => small s)

private theorem pair_product {e : ℕ} (r a : U e) :
    a.val*(a⁻¹*r).val=(r.val.val : ZMod (2^e)) := by
  rw [←Units.val_mul,mul_inv_cancel_left,ZMod.natCast_zmod_val]

private theorem deep_of_gap {e T : ℕ} (enough : T≤e) (r a : U e)
    (same : 2^T ∣ (a.val-(a⁻¹*r).val).val) : deep r T a := by
  let b := (a⁻¹*r).val
  let red := ZMod.castHom (pow_dvd_pow 2 enough) (ZMod (2^T))
  have equal : red a.val=red b := by
    apply sub_eq_zero.mp
    rw [←map_sub,←ZMod.natCast_zmod_val (a.val-b),map_natCast,ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact same
  have prod := congrArg red (pair_product r a)
  change red (a.val*b)=_ at prod
  rw [map_mul,←equal,map_natCast] at prod
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  rw [Nat.cast_pow,pow_two,←show red a.val=(a.val.val:ZMod (2^T)) by
    rw [←map_natCast red,ZMod.natCast_zmod_val]]
  exact prod

/-- Number of ordered unit-coordinate pairs covered by a fixed set of sum guesses. -/
noncomputable def mass {e : ℕ} (r : U e) (A : Finset (ZMod (2^e))) : ℕ :=
  ∑ s∈A,weight r.val.val s

private theorem row {e : ℕ} (r : U e) (s : ZMod (2^e)) :
    (univ.filter (fun x => label r x=s)).card=weight r.val.val s := by
  simpa [label,sum_boole] using DyadicSumGuessPopulation.count r s

private theorem budget_of_gap {e T : ℕ} (low : 3≤T) (enough : T≤e)
    (r : U e) (A : Finset (ZMod (2^e)))
    (cap : ∀ a : U e, ¬2^T ∣ (a.val-(a⁻¹*r).val).val → weight r.val.val (label r a)≤2^T) :
    mass r A≤(if r.val.val%8=1 then 4*2^(e-T) else 0)+A.card*2^T := by
  have sum := sum_card_fiberwise_eq_card_filter (univ : Finset (U e)) A (label r)
  simp only [row] at sum
  rw [mass,sum,←deep_count low enough]
  apply split_count
  intro a miss
  rw [row]
  exact cap a (fun same => miss (deep_of_gap enough r a same))

/-- Every sum realized by a short gap contributes at most 2^T starting
units. All long-gap units together are charged once across the entire menu. -/
theorem budget {e T : ℕ} (low : 3≤T) (enough : T≤e)
    (r : U e) (A : Finset (ZMod (2^e))) :
    mass r A≤(if r.val.val%8=1 then 4*2^(e-T) else 0)+A.card*2^T := by
  have odd := Nat.coprime_two_right.mp ((ZMod.val_coe_unit_coprime r).of_dvd_right
    (dvd_pow_self 2 (by omega : e≠0)))
  exact budget_of_gap low enough r A (fun a miss => DyadicPairSumWeight.weight_le_of_gap
    enough odd (pair_product r a) miss)

open DyadicSumGuessPopulation (population)

/-- Actual conditional success fraction for a menu fixed once the product
remainder is known. Each sorted full-size prime pair is counted once. -/
noncomputable def actualShare {e : ℕ} (r : U e) (A : Finset (ZMod (2^e))) : ℝ :=
  (((population r).filter (fun v => ((v.1+v.2:ℕ):ZMod (2^e))∈A)).card:ℝ)/(population r).card

/-- Modular probability for a uniform first unit and the partner determined
by the fixed product. -/
noncomputable def modularShare {e : ℕ} (r : U e) (A : Finset (ZMod (2^e))) : ℝ :=
  (mass r A:ℝ)/(2^e:ℕ).totient

private theorem actual_sum {e : ℕ} (r : U e) (A : Finset (ZMod (2^e))) :
    actualShare r A=∑ s∈A,DyadicSumGuessPopulation.actual r s := by
  rw [actualShare,←sum_card_fiberwise_eq_card_filter (population r) A
    (fun v => ((v.1+v.2:ℕ):ZMod (2^e))),Nat.cast_sum,sum_div]
  rfl

private theorem modular_sum {e : ℕ} (r : U e) (A : Finset (ZMod (2^e))) :
    modularShare r A=∑ s∈A,DyadicSumGuessPopulation.uniform r s := by
  simp only [modularShare,mass,Nat.cast_sum,sum_div,DyadicSumGuessPopulation.uniform]

/-- The actual probability of hitting any of the guesses incurs the same
relative error as a single guess. The sum events are disjoint. -/
theorem transfer {e : ℕ} (cap : e≤161) {li : ℕ→ℝ}
    (endpoints : 2≤e → ExtendedModulusPrimeSupply.Endpoints (2^e) li)
    (r : U e) (A : Finset (ZMod (2^e))) :
    |actualShare r A-modularShare r A|≤modularShare r A/(2:ℝ)^146 := by
  rw [actual_sum,modular_sum,←sum_sub_distrib,sum_div]
  exact (abs_sum_le_sum_abs ..).trans (sum_le_sum fun s _ =>
    (DyadicSumGuessPopulation.dyadic cap endpoints r).2 s)

/-- At 161 bits with 2^32 guesses, both 65 and 66 minimize the elementary
two-term bound on the square product class. -/
theorem optimal_cutoff (T : ℕ) : 3*2^97≤4*2^(161-T)+(2:ℕ)^32*2^T ∧
    (4*2^(161-T)+(2:ℕ)^32*2^T=3*2^97 ↔ T=65 ∨ T=66) := by
  by_cases early : T≤64
  · have pow := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega : 97≤161-T)
    omega
  by_cases late : 67≤T
  · have pow := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) late
    omega
  interval_cases T <;> decide

theorem modular_161 (r : U 161) (A : Finset (ZMod (2^161))) (size : A.card≤2^32) :
    modularShare r A≤3/(2:ℝ)^63 := by
  have bnd := budget (T:=65) (by decide) (by decide : 65≤161) r A
  have cap : mass r A ≤ 3*2^97 := by
    split at bnd <;> omega
  rw [modularShare,Nat.totient_prime_pow_succ Nat.prime_two]
  norm_num
  exact (div_le_div_of_nonneg_right (by exact_mod_cast cap : (mass r A:ℝ)≤3*2^97)
    (by positivity)).trans_eq (by norm_num)

/-- Conditional on the prime-count estimates, every fixed menu of at most
2^32 guesses in a given 161-bit product class has this success ceiling
among distinct 1,024-bit prime pairs with 2,048-bit product. -/
theorem actual_161 {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints (2^161) li)
    (r : U 161) (A : Finset (ZMod (2^161))) (size : A.card≤2^32) :
    actualShare r A≤(3/(2:ℝ)^63)*(1+1/(2:ℝ)^146) := by
  have maxShare := modular_161 r A size
  have delta := (abs_le.mp (transfer (by decide : 161≤161) (fun _ => h) r A)).2
  have eps := div_le_div_of_nonneg_right maxShare (show (0:ℝ)≤2^146 by positivity)
  rw [mul_add,mul_one,mul_one_div]
  linarith only [maxShare,delta,eps]

end PrimeFactors.DyadicSumMenuBudget
