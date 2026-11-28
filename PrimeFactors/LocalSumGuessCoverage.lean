import PrimeFactors.PrimePowerSumCollisions
import Mathlib.Algebra.Order.Chebyshev

/-! List coverage and independent guesses in the finite population of ordered
residue pairs with a fixed product. -/

namespace PrimeFactors.LocalSumGuessCoverage

open Finset PrimeSquareSumWeights PrimePowerSumCollisions
open scoped Classical

/-- Number of ordered local pairs whose sum is on the list. -/
noncomputable def covered {m : ℕ} [NeZero m] (n : ℕ) (S : Finset (ZMod m)) :=
  (univ.filter (fun v : Pairs n m => sumOf v ∈ S)).card

theorem covered_eq_sum {m : ℕ} [NeZero m] (n : ℕ) (S : Finset (ZMod m)) :
    covered n S = ∑ s ∈ S, weight n s := by
  rw [covered,←sum_card_fiberwise_eq_card_filter]
  apply sum_congr rfl
  intro s _
  rw [weight,Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem covered_univ {m : ℕ} [NeZero m] (n : ℕ) :
    covered n (univ : Finset (ZMod m)) = Nat.card (Pairs n m) := by
  simp [covered,Nat.card_eq_fintype_card]

/-- Cauchy–Schwarz applies to every list of distinct proposed residues. -/
theorem covered_sq {m : ℕ} [NeZero m] (n : ℕ) (S : Finset (ZMod m)) :
    (covered n S)^2 ≤ S.card * collisions n m := by
  rw [covered_eq_sum]
  calc
    _ ≤ S.card * (∑ s ∈ S, weight n s ^ 2) := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := Nat.mul_le_mul_left _ (sum_le_sum_of_subset (subset_univ S))

/-- A necessary list size to cover at least half of the population, valid
at any nonzero modulus and for any product. -/
theorem half_bound {m n : ℕ} [NeZero m] (S : Finset (ZMod m))
    (half : Nat.card (Pairs n m) ≤ 2*covered n S) :
    (Nat.card (Pairs n m))^2 ≤ 4*S.card*collisions n m := by
  have bound := Nat.pow_le_pow_left half 2
  have cauchy := Nat.mul_le_mul_left 4 (covered_sq n S)
  nlinarith only [bound,cauchy]

/-- Match probability when both the guess and the target are the sums of
independent uniform ordered draws. -/
noncomputable def matchProbability (n m : ℕ) [NeZero m] : ℚ :=
  (Nat.card {v : Pairs n m × Pairs n m // sumOf v.1 = sumOf v.2} : ℚ) /
    Nat.card (Pairs n m × Pairs n m)

theorem match_as_collision (n m : ℕ) [NeZero m] :
    matchProbability n m = (collisions n m : ℚ)/Nat.card (Pairs n m)/Nat.card (Pairs n m) := by
  rw [matchProbability,count_equal_sums,Nat.card_prod,Nat.cast_mul,div_div]

variable {p : ℕ} [Fact p.Prime]

private theorem prime_power_total {e n : ℕ} (ep : 0<e) (unit : ¬p∣n) :
    Nat.card (Pairs n (p^e)) = p^(e-1)*(p-1) := by
  have prime := (Fact.out : p.Prime)
  rw [total ((ZMod.isUnit_iff_coprime n _).mpr ((prime.coprime_iff_not_dvd.mpr unit).symm.pow_right _)),
    Nat.totient_prime_pow prime ep]

/-- The explicit Cauchy–Schwarz half-coverage bound with the common
prime-power factor cancelled. -/
theorem square_half_bound {e n : ℕ} (ep : 0<e) (odd : p≠2) (unit : ¬p∣n)
    (sq : IsSquare (n : ZMod p)) (S : Finset (ZMod (p^e)))
    (half : Nat.card (Pairs n (p^e)) ≤ 2*covered n S) :
    p^(e-1)*(p-1)^2 ≤ 4*S.card*(2*e*(p-1)-2) := by
  have h := half_bound S half
  rw [prime_power_total ep unit,second_moment ep odd unit sq] at h
  exact Nat.le_of_mul_le_mul_left (c:=p^(e-1))
    (by simpa only [mul_pow,pow_two,mul_assoc,mul_left_comm,mul_comm] using h)
    (pow_pos (Fact.out : p.Prime).pos _)

theorem square_match {e n : ℕ} (ep : 0<e) (odd : p≠2) (unit : ¬p∣n)
    (sq : IsSquare (n : ZMod p)) :
    matchProbability n (p^e) = (2*(e:ℚ)-2/((p:ℚ)-1)) / (p^(e-1)*(p-1) : ℕ) := by
  rw [match_as_collision,expected_weight ep odd unit sq,prime_power_total ep unit]

/-- The ceiling of the second-moment lower bound at precision 100 for
product one and p=5. -/
theorem five_half_bound (S : Finset (ZMod (5^100)))
    (half : Nat.card (Pairs 1 (5^100)) ≤ 2*covered 1 S) :
    (2*5^99+398)/399 ≤ S.card ∧ 2^222 < S.card := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h := square_half_bound (p:=5) (e:=100) (n:=1) (by decide) (by decide)
    (by decide) (by norm_num) S half
  norm_num at h ⊢
  omega

theorem five_match : matchProbability 1 (5^100) = 399/(8*5^99 : ℚ) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [square_match (p:=5) (e:=100) (n:=1) (by decide) (by decide) (by decide) (by norm_num)]
  norm_num

/-- A nonsquare product in the residue field forces the two coordinates to
have different first digits. Every attainable sum then has weight two. -/
theorem nonsquare_weight {n e : ℕ} (ep : 0<e) (odd : p≠2) (nsq : ¬IsSquare (n : ZMod p))
    (s : ZMod (p^e)) :
    weight n s = if AdmissibleSum (n : ZMod (p^e)) s then 2 else 0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ep.ne'
  split_ifs with pass
  · obtain ⟨x,y,prod,rfl⟩ := pass
    let f := firstPrimeDigit p k
    have miss : ¬p^1 ∣ (x-y).val := by
      intro hit
      have zero : f (x-y)=0 := by
        rw [←ZMod.natCast_zmod_val (x-y),map_natCast,ZMod.natCast_zmod_eq_zero_iff_dvd]
        simpa only [pow_one] using hit
      have eq : f x=f y := sub_eq_zero.mp ((map_sub f x y).symm.trans zero)
      apply nsq
      exact ⟨f y,by rw [←map_natCast f n,←prod,map_mul,eq]⟩
    simpa only [pow_zero,mul_one] using PrimePowerPairWeight.weight_of_shell (t:=0)
      odd prod (by simp) miss (by omega)
  · apply Nat.card_eq_zero.mpr
    exact Or.inl ⟨fun v => pass ⟨v.val.val.1,v.val.val.2,v.val.property,v.property⟩⟩

theorem nonsquare_coverage {n e : ℕ} (ep : 0<e) (odd : p≠2) (nsq : ¬IsSquare (n : ZMod p))
    (S : Finset (ZMod (p^e))) :
    covered n S = 2*(S.filter (AdmissibleSum (n : ZMod (p^e)))).card := by
  rw [covered_eq_sum]
  simp only [nonsquare_weight ep odd nsq,sum_ite,not_false_eq_true,sum_const_zero,add_zero,
    sum_const,nsmul_eq_mul,Nat.mul_comm,Nat.cast_id]

theorem nonsquare_match {n e : ℕ} (ep : 0<e) (odd : p≠2) (nsq : ¬IsSquare (n : ZMod p)) :
    matchProbability n (p^e) = 2 / (p^(e-1)*(p-1) : ℕ) := by
  have unit : ¬p∣n := fun div => nsq (by
    rw [(ZMod.natCast_zmod_eq_zero_iff_dvd n p).mpr div]; exact IsSquare.zero)
  have moment : collisions n (p^e) = 2*Nat.card (Pairs n (p^e)) := by
    calc
      _ = ∑ s : ZMod (p^e), 2*weight n s := by
        apply sum_congr rfl
        intro s _
        rw [nonsquare_weight ep odd nsq]
        split_ifs <;> decide
      _ = _ := by rw [←mul_sum,←covered_eq_sum,covered_univ]
  rw [match_as_collision,moment,prime_power_total ep unit,Nat.cast_mul,Nat.cast_ofNat]
  have pos : 0 < p^(e-1)*(p-1) := Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos _)
    (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
  have nz : ((p^(e-1)*(p-1) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast pos.ne'
  push_cast at nz ⊢
  field_simp [nz]

end PrimeFactors.LocalSumGuessCoverage
