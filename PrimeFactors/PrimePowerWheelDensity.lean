import PrimeFactors.PrimePowerDensityRatio
import PrimeFactors.Certificate

/-! Bounding the aggregate gain from deeper digits in any finite collection
of odd-prime factor-sum tests. This measures complete-period density. -/
namespace PrimeFactors.PrimePowerWheelDensity

open PrimePowerDensityRatio (density density_pos density_nonneg local_bound)
open PrimePowerRatioProduct (ratio)

private theorem density_one (n : ℕ) : density n 1 = 1 := by
  have one : Subsingleton {s : ZMod 1 // AdmissibleSum (n : ZMod 1) s} := inferInstance
  haveI : Nonempty {s : ZMod 1 // AdmissibleSum (n : ZMod 1) s} :=
    ⟨⟨1+n,1,n,one_mul _,rfl⟩⟩
  simp [density,LocalSumMenu.count,Nat.card_eq_one_iff_unique]

theorem density_crt {a b : ℕ} (cop : a.Coprime b) (n : ℕ) :
    density n (a*b) = density n a * density n b := by
  have c : LocalSumMenu.count n (a*b) = LocalSumMenu.count n a*LocalSumMenu.count n b :=
    card_admissibleSum_crt cop n
  simp only [density,c,Nat.cast_mul,div_mul_div_comm]

/-- The local fractions multiply exactly even when the primes use different depths. -/
theorem density_product (n : ℕ) (S : Finset ℕ) (depth : ℕ → ℕ) (prime : ∀p∈S, p.Prime) :
    density n (∏ p ∈ S, p^(depth p)) = ∏ p ∈ S, density n (p^(depth p)) := by
  induction S using Finset.induction_on with
  | empty => simp [density_one]
  | @insert p S skip ih =>
    have hp := prime p (Finset.mem_insert_self ..)
    have rest := fun q (hq : q∈S) => prime q (Finset.mem_insert_of_mem hq)
    have cop : (p^(depth p)).Coprime (∏ q ∈ S, q^(depth q)) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (((Nat.coprime_primes hp (rest q hq)).mpr (fun h => skip (h ▸ hq))).pow_left _).pow_right _
    rw [Finset.prod_insert skip,Finset.prod_insert skip,density_crt cop,ih rest]

/-- Increasing all odd-prime precisions beyond two buys less than a factor
of four in complete-period density, independently of the number of primes. -/
theorem less_than_four (n : ℕ) (S : Finset ℕ) (depth : ℕ → ℕ)
    (eligible : ∀ p∈S, p.Prime ∧ p≠2 ∧ ¬p∣n ∧ 2≤depth p) :
    density n (∏ p ∈ S, p^2) < 4*density n (∏ p ∈ S, p^(depth p)) := by
  have prime := fun p (hp : p∈S) => (eligible p hp).1
  rw [density_product n S (fun _ => 2) prime, density_product n S depth prime]
  have bound (p : ℕ) (hp : p∈S) : density n (p^2) ≤ ratio p*density n (p^(depth p)) := by
    obtain ⟨pp,odd,unitN,deep⟩ := eligible p hp
    letI : Fact p.Prime := ⟨pp⟩
    exact local_bound odd unitN deep
  have prod := Finset.prod_le_prod (fun p (_ : p∈S) => density_nonneg n (p^2)) bound
  rw [Finset.prod_mul_distrib] at prod
  exact prod.trans_lt (mul_lt_mul_of_pos_right
    (PrimePowerRatioProduct.product_lt_four S (fun p hp => ⟨prime p hp,(eligible p hp).2.1⟩))
    (Finset.prod_pos (fun p hp => density_pos n (pow_pos (prime p hp).pos _))))

end PrimeFactors.PrimePowerWheelDensity
