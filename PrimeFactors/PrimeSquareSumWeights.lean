import PrimeFactors.StableDiscriminantClasses
import Mathlib.Data.Nat.Totient

/-! Multiplicities of factor sums for a fixed unit product modulo an odd
prime square. The sample space consists of equally weighted ordered pairs
of local factors. -/

open private PrimeFactors.digit_card from PrimeFactors.PrimePowerCount

namespace PrimeFactors.PrimeSquareSumWeights

open scoped Classical

abbrev Pairs (n m : ℕ) := {v : ZMod m × ZMod m // v.1*v.2=(n : ZMod m)}

def sumOf {n m : ℕ} (v : Pairs n m) := v.val.1+v.val.2

/-- Number of ordered local factor pairs with this particular sum. -/
noncomputable def weight {m : ℕ} (n : ℕ) (s : ZMod m) :=
  Nat.card {v : Pairs n m // sumOf v = s}

/-- Choosing the first unit determines the ordered pair. -/
theorem total {m n : ℕ} [NeZero m] (unit : IsUnit (n : ZMod m)) :
    Nat.card (Pairs n m) = m.totient := by
  let lift (v : Pairs n m) : IsUnit v.val.1 :=
    ((Commute.all _ _).isUnit_mul_iff.mp (v.property ▸ unit)).1
  let e : (ZMod m)ˣ ≃ Pairs n m := {
    toFun := fun u => ⟨(u,(↑u⁻¹ : ZMod m)*n),by simp [←mul_assoc]⟩
    invFun := fun v => (lift v).unit
    left_inv := fun u => Units.ext (IsUnit.unit_spec _)
    right_inv := fun v => by
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · exact (lift v).unit_spec
      · change (↑((lift v).unit)⁻¹ : ZMod m)*n=v.val.2
        calc
          _ = (↑((lift v).unit)⁻¹ : ZMod m)*(v.val.1*v.val.2) := congrArg _ v.property.symm
          _ = _ := by
            have inv : (↑((lift v).unit)⁻¹ : ZMod m)*v.val.1=1 := by
              simpa only [(lift v).unit_spec] using (lift v).unit.inv_mul
            rw [←mul_assoc,inv,one_mul] }
  rw [←Nat.card_congr e,Nat.card_eq_fintype_card,ZMod.card_units_eq_totient]

/-- For each sum, the difference of the ordered factors ranges over exactly
the square roots of its discriminant. Division by two recovers the pair. -/
theorem weight_roots {m : ℕ} (two : IsUnit (2 : ZMod m)) (n : ℕ) (s : ZMod m) :
    weight n s = Nat.card {d : ZMod m // d^2=s^2-4*n} := by
  let f (v : {z : Pairs n m // sumOf z=s}) : {d : ZMod m // d^2=s^2-4*n} :=
    ⟨v.val.val.1-v.val.val.2,by
      calc
        _ = (sumOf v.val)^2 - 4*(v.val.val.1*v.val.val.2) := by unfold sumOf; ring
        _ = _ := by rw [v.property,v.val.property]⟩
  apply Nat.card_congr (Equiv.ofBijective f ?_)
  constructor
  · intro v w eq
    have dif : v.val.val.1-v.val.val.2 = w.val.val.1-w.val.val.2 := congrArg Subtype.val eq
    have sums : v.val.val.1+v.val.val.2 = w.val.val.1+w.val.val.2 :=
      v.property.trans w.property.symm
    apply Subtype.ext ∘ Subtype.ext
    apply Prod.ext
    · apply two.mul_left_cancel
      linear_combination sums+dif
    · apply two.mul_left_cancel
      linear_combination sums-dif
  · rintro ⟨d,square⟩
    let half := (↑two.unit⁻¹ : ZMod m)
    have inverse : 2*half=1 := by rw [←two.unit_spec]; exact two.unit.mul_inv
    have prod : ((s+d)*half)*((s-d)*half) = n := by
      calc
        _ = (s^2-d^2)*half^2 := by ring
        _ = n*(2*half)^2 := by rw [square]; ring
        _ = _ := by rw [inverse]; ring
    have sum : (s+d)*half+(s-d)*half = s := by linear_combination s*inverse
    refine ⟨⟨⟨((s+d)*half,(s-d)*half),prod⟩,sum⟩,Subtype.ext ?_⟩
    change (s+d)*half-(s-d)*half=d
    linear_combination d*inverse

variable {p : ℕ} [Fact p.Prime]

private theorem two_unit (odd : p ≠ 2) : IsUnit (2 : ZMod (p^2)) :=
  (ZMod.isUnit_iff_coprime 2 _).mpr
    ((Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two Fact.out).mpr odd.symm)))

private theorem zero_square (x : ZMod (p^2)) :
    x^2=0 ↔ firstPrimeDigit p 1 x=0 := by
  obtain ⟨a,rfl⟩ := ZMod.natCast_zmod_surjective x
  rw [map_natCast,←Nat.cast_pow,ZMod.natCast_zmod_eq_zero_iff_dvd,
    ZMod.natCast_zmod_eq_zero_iff_dvd]
  exact Nat.pow_dvd_pow_iff (by decide : 2≠0)

/-- Each singular sum with zero discriminant has one pair for each possible
multiple of p that can serve as the difference. -/
theorem zero_weight (odd : p ≠ 2) (n : ℕ) {s : ZMod (p^2)} (zero : s^2-4*(n : ZMod (p^2))=0) :
    weight n s=p := by
  rw [weight_roots (two_unit odd),zero,Nat.card_congr (Equiv.subtypeEquivRight zero_square),
    PrimeFactors.digit_card,pow_one]

/-- Every admissible sum with nonzero discriminant occurs exactly twice. -/
theorem regular_weight (odd : p ≠ 2) (n : ℕ) {s : ZMod (p^2)}
    (nz : s^2-4*(n : ZMod (p^2))≠0) (pass : AdmissibleSum (n : ZMod (p^2)) s) : weight n s=2 := by
  let D := s^2-4*(n : ZMod (p^2))
  have square : IsSquare D := (admissibleSum_iff_isSquare_of_two_unit (two_unit odd) _ _).mp pass
  obtain ⟨d,rep⟩ := ZMod.intCast_surjective D
  have dz : (d : ZMod (p^2)) ≠ 0 := rep ▸ nz
  have ds : IsSquare (d : ZMod (p^2)) := rep ▸ square
  have unit : (d : ZMod p) ≠ 0 := by
    intro z
    have div := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp z
    have hit := (isSquare_prime_sq_iff_of_dvd d div).mp ds
    exact dz ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (by simpa only [Nat.cast_pow] using hit))
  have sq := (isSquare_primePow_iff_of_unit odd d unit 1).mp ds
  rw [weight_roots (two_unit odd)]
  change Nat.card {x : ZMod (p^2) // x^2=D}=2
  rw [←rep,primitiveNorm_odd_root_count odd d unit 1,if_pos sq]

/-- Complete distribution of multiplicities over all sum residues. -/
theorem weight_formula (odd : p ≠ 2) (n : ℕ) (s : ZMod (p^2)) :
    weight n s = if s^2-4*(n : ZMod (p^2))=0 then p else if AdmissibleSum (n : ZMod (p^2)) s then 2 else 0 := by
  classical
  split_ifs with z yes
  · exact zero_weight odd n z
  · exact regular_weight odd n z yes
  · apply Nat.card_eq_zero.mpr
    left
    exact ⟨fun v => yes ⟨v.val.val.1,v.val.val.2,v.val.property,v.property⟩⟩

/-- Total weight of the distinct sum residues with zero discriminant. -/
noncomputable def singularMass (p n : ℕ) [NeZero p] :=
  ∑ s : {s : ZMod (p^2) // s^2-4*(n : ZMod (p^2))=0}, weight n s.val

theorem singular_mass (odd : p ≠ 2) {n : ℕ} (unit : ¬p ∣ n) :
    singularMass p n = if IsSquare (n : ZMod p) then 2*p else 0 := by
  classical
  have card := StableDiscriminantClasses.zero_count odd unit 1
  rw [Nat.card_eq_fintype_card] at card
  unfold singularMass
  simp only [fun s : {s : ZMod (p^2) // s^2-4*(n : ZMod (p^2))=0} => zero_weight odd n s.property,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card]
  split_ifs <;> simp

/-- Under the square-unit hypothesis the two zero-discriminant sums collect
at least as much mass as any choice of at most two local sum residues. -/
theorem two_class_optimal (odd : p ≠ 2) {n : ℕ} (unit : ¬p ∣ n) (sq : IsSquare (n : ZMod p))
    (S : Finset (ZMod (p^2))) (budget : S.card ≤ 2) :
    (∑ s ∈ S, weight n s) ≤ singularMass p n := by
  classical
  rw [singular_mass odd unit,if_pos sq]
  calc
    _ ≤ ∑ _s ∈ S, p := by
      apply Finset.sum_le_sum
      intro s _
      rw [weight_formula odd n s]
      split_ifs <;> first | exact le_rfl | exact (Fact.out : p.Prime).two_le | exact Nat.zero_le _
    _ = S.card*p := by simp
    _ ≤ _ := Nat.mul_le_mul_right p budget

/-- Probability of a zero-discriminant sum under uniform sampling of ordered
local pairs with fixed square unit product. -/
theorem square_probability (odd : p ≠ 2) {n : ℕ} (unit : ¬p ∣ n) (sq : IsSquare (n : ZMod p)) :
    (singularMass p n : ℚ)/Nat.card (Pairs n (p^2)) = 2/(p-1 : ℚ) := by
  have prime := (Fact.out : p.Prime)
  have cop := (prime.coprime_iff_not_dvd.mpr unit).symm
  have up : IsUnit (n : ZMod (p^2)) := (ZMod.isUnit_iff_coprime _ _).mpr (cop.pow_right 2)
  rw [singular_mass odd unit,if_pos sq,total up,Nat.totient_prime_pow_succ prime 1,pow_one]
  have pp : (0 : ℚ) < p := by exact_mod_cast prime.pos
  rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_sub prime.one_le]
  have one : (1 : ℚ) < p := by exact_mod_cast prime.one_lt
  field_simp [pp.ne',(sub_pos.mpr one).ne']
  ring

/-- Modulo 25 with product one, sums 2 and 23 each occur five times;
the twenty ordered pairs put half their mass on these two classes. -/
theorem control25 :
    weight 1 (2 : ZMod 25)=5 ∧ weight 1 (23 : ZMod 25)=5 ∧
      (singularMass 5 1 : ℚ)/Nat.card (Pairs 1 25)=1/2 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine ⟨zero_weight (p:=5) (by decide) 1 (by decide),zero_weight (p:=5) (by decide) 1 (by decide),?_⟩
  convert square_probability (p:=5) (n:=1) (by decide) (by decide) (by norm_num) using 1
  norm_num

end PrimeFactors.PrimeSquareSumWeights
