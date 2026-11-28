import PrimeFactors.GuessModulusBudget

/-! A budget on the product of the distinct odd primes themselves. This
also covers first-power factors of the chosen modulus. -/
namespace PrimeFactors.GuessRadicalBudget

open Finset GuessModulusBudget
open private PrimeFactors.GuessModulusBudget.mem_primes PrimeFactors.GuessModulusBudget.penalty_anti
  PrimeFactors.GuessModulusBudget.penalty_ge_one PrimeFactors.GuessModulusBudget.ratio_eq
  from PrimeFactors.GuessModulusBudget

set_option exponentiation.threshold 4096
set_option maxRecDepth 16384

noncomputable def radical (S : Finset ℕ) := ∏ p∈S,p

private noncomputable def trial (n : ℕ) : Bool :=
  decide (2≤n) && (List.range 39).all (fun d => decide (d<2 ∨ n≤d ∨ n%d≠0))

/-- Checking all trial divisors below 39 is complete over the finite prefix. -/
private theorem trial_ok {n : ℕ} (small : n≤1481) : trial n=true ↔ n.Prime := by
  simp only [trial,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range]
  constructor
  · rintro ⟨large,checks⟩
    by_contra composite
    have sq := Nat.minFac_sq_le_self (by omega : 0<n) composite
    have short : n.minFac<39 := by
      by_contra! big
      have x := Nat.pow_le_pow_left big 2
      omega
    have test := checks _ short
    have positive := (Nat.minFac_prime (by omega : n≠1)).two_le
    have proper := (Nat.not_prime_iff_minFac_lt large).mp composite
    have divides := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n)
    omega
  · intro pp
    refine ⟨pp.two_le,fun d _ => ?_⟩
    by_contra! h
    have sides := (Nat.dvd_prime pp).mp (Nat.dvd_of_mod_eq_zero h.2.2)
    omega

private theorem evaluated (k : ℕ) (small : k≤1481) :
    primes k=(range (k+1)).filter (fun p => trial p=true ∧ 5≤p) := by
  ext p
  rw [PrimeFactors.GuessModulusBudget.mem_primes,mem_filter,mem_range,Nat.lt_succ_iff]
  exact ⟨fun h => ⟨h.2.2,(trial_ok (h.2.2.trans small)).mpr h.1,h.2.1⟩,
    fun h => ⟨(trial_ok (h.1.trans small)).mp h.2.1,h.2.2,h.1⟩⟩

private def certificate (s t : Finset ℕ) : Prop :=
  s.card=231 ∧ t.card=232 ∧ 2^2043≤radical s ∧ radical s<2^2044 ∧
    2^2048<radical t ∧ 16*numeratorProduct s>pairProduct s

private noncomputable instance (s t : Finset ℕ) : Decidable (certificate s t) := by unfold certificate; infer_instance

set_option maxHeartbeats 9000000 in
private theorem checked : certificate (primes 1471) (primes 1481) := by
  rw [evaluated 1471 (by decide),evaluated 1481 le_rfl]
  decide +kernel

/-- At most 231 distinct primes at least five fit the product budget. -/
theorem count (S : Finset ℕ) (hs : ∀ p∈S,p.Prime ∧ 5≤p) (limit : radical S≤2^2048) : S.card≤231 := by
  by_contra! many
  have ex := quotientBudget_product_exchange (s:=primes 1481) (t:=S) (fun p => p) (cut:=1481)
    (by decide) (by have := checked.2.1; omega) (by simp)
    (fun p h => (PrimeFactors.GuessModulusBudget.mem_primes.mp (mem_sdiff.mp h).1).2.2)
    (by
      intro p h
      obtain ⟨ins,missing⟩ := mem_sdiff.mp h
      obtain ⟨pp,large⟩ := hs p ins
      exact le_of_not_gt (fun lo => missing (PrimeFactors.GuessModulusBudget.mem_primes.mpr ⟨pp,large,lo.le⟩)))
  exact (not_lt_of_ge (ex.trans limit)) checked.2.2.2.2.1

private theorem bound (S : Finset ℕ) (hs : ∀ p∈S,p.Prime ∧ 5≤p) (limit : radical S≤2^2048) :
    (∏ p∈S,penalty p) ≤ ∏ p∈primes 1471,penalty p := by
  have pp : Nat.Prime 1471 := by norm_num
  apply quotientBudget_product_exchange (cut:=penalty 1471) _
    (PrimeFactors.GuessModulusBudget.penalty_ge_one pp (by decide)) ((count S hs limit).trans_eq checked.1.symm)
    (fun p hp => by unfold penalty; positivity)
  · intro p h
    obtain ⟨ins,missing⟩ := mem_sdiff.mp h
    obtain ⟨prime,large⟩ := hs p ins
    exact PrimeFactors.GuessModulusBudget.penalty_anti pp prime (by decide)
      (le_of_not_gt (fun lo => missing (PrimeFactors.GuessModulusBudget.mem_primes.mpr ⟨prime,large,lo.le⟩)))
  · intro p h
    obtain ⟨prime,large,lo⟩ := PrimeFactors.GuessModulusBudget.mem_primes.mp (mem_sdiff.mp h).1
    exact PrimeFactors.GuessModulusBudget.penalty_anti prime pp large lo

/-- The product of the local factors exceeds 1/16 even if the modulus
budget charges each distinct prime just once. -/
theorem sixteenth (S : Finset ℕ) (hs : ∀ p∈S,p.Prime ∧ p≠2) (limit : radical S≤2^2048) :
    (1:ℝ)/16 < ∏ p∈S,ratio p := by
  let T := S.erase 3
  have members (p) (h : p∈T) : p.Prime ∧ 5≤p := by
    obtain ⟨ne,ins⟩ := mem_erase.mp h
    obtain ⟨pp,odd⟩ := hs p ins
    have := pp.two_le
    have p4 : p≠4 := fun eq => (by decide : ¬Nat.Prime 4) (eq ▸ pp)
    exact ⟨pp,by omega⟩
  have l : radical T≤radical S := by
    by_cases h : 3∈S
    · have z := mul_prod_erase S id h
      change 3*radical T=radical S at z
      omega
    · exact (congrArg radical (erase_eq_of_not_mem h)).le
  have eq : (∏p∈T,ratio p)=∏p∈S,ratio p := by
    by_cases h : 3∈S
    · simpa only [show ratio 3=1 by norm_num [ratio,PrimeSquareUniformFloor.numerator,PrimeSquareExpectedRank.pairs],
        one_mul,T] using mul_prod_erase S ratio h
    · rw [show T=S from erase_eq_of_not_mem h]
  have positive : 0<∏p∈T,penalty p := prod_pos fun p h => zero_lt_one.trans_le
    (PrimeFactors.GuessModulusBudget.penalty_ge_one (members p h).1 (members p h).2)
  have inv (V : Finset ℕ) : (∏p∈V,penalty p)⁻¹=∏p∈V,ratio p := by
    simp only [←prod_inv_distrib,penalty,inv_div,ratio]
  have order := inv_anti₀ positive (bound T members (l.trans limit))
  rw [inv,inv,eq] at order
  apply lt_of_lt_of_le _ order
  rw [PrimeFactors.GuessModulusBudget.ratio_eq]
  have pos : 0<(pairProduct (primes 1471):ℝ) := by
    apply Nat.cast_pos.mpr
    exact prod_pos (fun p h => Nat.mul_pos (PrimeFactors.GuessModulusBudget.mem_primes.mp h).1.pos
      (by have := (PrimeFactors.GuessModulusBudget.mem_primes.mp h).2.1; omega))
  apply (div_lt_div_iff₀ (by norm_num : (0:ℝ)<16) pos).mpr
  rw [one_mul,mul_comm _ (16:ℝ)]
  exact_mod_cast checked.2.2.2.2.2

end PrimeFactors.GuessRadicalBudget
