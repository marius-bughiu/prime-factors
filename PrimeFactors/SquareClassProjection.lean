import PrimeFactors.ReciprocalDivisorClasses
import PrimeFactors.CharacterDivisorColumn
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness

/-! Public square roots of signed relations can be multiplied and any common
invertible square removed. The remaining signed integer gives a Jacobi wheel if
its absolute value is small. The linear algebra below describes exactly which
small-prime sign assignments are compatible with the supplied parity equations.
Its cardinality concerns assignments of signs. -/

namespace PrimeFactors.SquareClassProjection

open scoped BigOperators

/-- A combination is certified by its public roots, one integer product
identity and a gcd with the input. The displayed left side is the new root. -/
theorem projected_root {ι : Type*} {N s : ℕ} {δ : ℤ} (rows : Finset ι)
    (value : ι → ℤ) (root : ι → ZMod N)
    (roots : ∀ i ∈ rows, root i ^ 2 = (value i : ZMod N))
    (product : ∏ i ∈ rows, value i = δ * (s : ℤ)^2) (cop : s.Coprime N) :
    ((∏ i ∈ rows, root i) * (↑(ZMod.unitOfCoprime s cop)⁻¹ : ZMod N))^2 =
      (δ : ZMod N) := by
  let u := ZMod.unitOfCoprime s cop
  have hprod : (∏ i ∈ rows, (value i : ZMod N)) = (δ : ZMod N) * (u : ZMod N)^2 := by
    rw [show (u : ZMod N) = (s : ZMod N) from ZMod.coe_unitOfCoprime s cop]
    exact_mod_cast congrArg (Int.castRingHom (ZMod N)) product
  change ((∏ i ∈ rows, root i) * (↑u⁻¹ : ZMod N))^2 = _
  rw [mul_pow, ← Finset.prod_pow, Finset.prod_congr rfl roots, hprod, mul_assoc,
    ← mul_pow, Units.mul_inv, one_pow, mul_one]

/-- A signed square remainder has positive symbol at every divisor coprime
to it. There is no primality, parity or sign assumption on the divisor here. -/
theorem signed_divisor {N d : ℕ} {D : ℤ} (dv : d ∣ N) (cop : D.natAbs.Coprime N)
    (sq : IsSquare (D : ZMod N)) : jacobiSym D d = 1 := by
  have localSquare : IsSquare (D : ZMod d) := by
    simpa only [map_intCast] using IsSquare.map (ZMod.castHom dv (ZMod d)) sq
  obtain ⟨z, hz⟩ := localSquare
  have hcast : (D : ZMod d) = ((z.valMinAbs^2 : ℤ) : ZMod d) := by
    push_cast
    simpa only [pow_two] using hz
  have pos : 0 ≤ jacobiSym D d := by
    rw [jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' _ _ _).mp hcast),
      jacobiSym.pow_left]
    exact sq_nonneg _
  have choices := jacobiSym.eq_one_or_neg_one
    (a := D) (b := d) (by rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]; exact cop.of_dvd_right dv)
  omega

/-- Positive remainders congruent to one modulo four also give the reversed
Jacobi test with fixed denominator. -/
theorem positive_divisor {N D d : ℕ} (one : D % 4 = 1) (odd : Odd d)
    (dv : d ∣ N) (cop : D.Coprime N) (sq : IsSquare (D : ZMod N)) :
    jacobiSym (d : ℤ) D = 1 := by
  rw [jacobiSym.quadratic_reciprocity_one_mod_four' odd one]
  exact signed_divisor (D := (D : ℤ)) dv cop (by simpa using sq)

/-- A table of odd residues common to any finite collection of signed tests. -/
noncomputable def wheel (M : ℕ) (D : Finset ℤ) : Finset ℕ :=
  (Finset.range M).filter fun a => a%2 = 1 ∧ ∀ δ ∈ D, jacobiSym δ a = 1

/-- Every odd divisor lies in the table once the roots and periods have
been verified using the input alone. -/
theorem wheel_contains {N d M : ℕ} (D : Finset ℤ) (dv : d ∣ N) (odd : Odd d)
    (pos : 0 < M) (even : 2 ∣ M) (periods : ∀ δ ∈ D, 4*δ.natAbs ∣ M)
    (cop : ∀ δ ∈ D, δ.natAbs.Coprime N) (sq : ∀ δ ∈ D, IsSquare (δ : ZMod N)) :
    d % M ∈ wheel M D := by
  have parity : d%M%2 = 1 := (Nat.mod_mod_of_dvd _ even).trans (Nat.odd_iff.mp odd)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ pos), parity, ?_⟩
  intro δ hδ
  exact (CharacterDivisorColumn.periodic (Nat.odd_iff.mpr parity) odd δ
    (Nat.mod_mod_of_dvd _ (periods δ hδ))).trans (signed_divisor dv (cop δ hδ) (sq δ hδ))

/-- The same large cofactor in two negative rows cancels from their product,
even when that cofactor has no known prime factorization. -/
theorem shared_cofactor {N L a b : ℕ} (cop : L.Coprime N) {u v : ZMod N}
    (first : u^2 = -(a : ZMod N)*L) (second : v^2 = -(b : ZMod N)*L) :
    (u*v*(↑(ZMod.unitOfCoprime L cop)⁻¹ : ZMod N))^2 = (a : ZMod N)*b := by
  let f := ZMod.unitOfCoprime L cop
  have hf : (L : ZMod N) = f := (ZMod.coe_unitOfCoprime L cop).symm
  change (u*v*(↑f⁻¹ : ZMod N))^2 = _
  rw [mul_pow, mul_pow, first, second, hf]
  calc
    _ = (a : ZMod N)*b*((f : ZMod N)*(↑f⁻¹ : ZMod N))^2 := by ring
    _ = _ := by rw [Units.mul_inv, one_pow, mul_one]

/-- A pairwise gcd certificate suffices to rule out every nonempty square
dependency among nonsquare residual cofactors. The cofactors can be composite. -/
theorem no_square_product {ι : Type*} (s : Finset ι) (r : ι → ℕ)
    (nonempty : s.Nonempty) (nonsquare : ∀ i ∈ s, ¬ IsSquare (r i))
    (disjoint : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (r i).Coprime (r j)) :
    ¬ IsSquare (∏ i ∈ s, r i) := by
  classical
  obtain ⟨i, hi⟩ := nonempty
  rintro ⟨z, hz⟩
  have cop : (r i).Coprime (∏ j ∈ s.erase i, r j) := by
    apply Nat.Coprime.prod_right
    intro j hj
    exact disjoint i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm
  have hprod : r i * (∏ j ∈ s.erase i, r j) = z^2 := by
    rw [Finset.mul_prod_erase _ _ hi, pow_two, hz]
  obtain ⟨w, hw⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr cop.gcd_eq_one) hprod
  exact nonsquare i hi ⟨w, by simpa only [pow_two] using hw⟩

/-- Three roots obtained by eliminating large cofactors from the first 512
continued-fraction steps on this input. The numeric receipt needs only N. -/
theorem three_roots :
    (130477127726457 : ZMod 246180296426219)^2 = (-11 : ℤ) ∧
    (228876284726978 : ZMod 246180296426219)^2 = (14 : ℤ) ∧
    (230840503340143 : ZMod 246180296426219)^2 = (22 : ℤ) := by decide

/-- All three projected characters may be tabulated modulo 616. -/
theorem three_root_wheel {d : ℕ} (dv : d ∣ 246180296426219) (odd : Odd d) :
    d%616 ∈ wheel 616 {-11, 14, 22} := by
  apply wheel_contains _ dv odd (by decide) (by decide)
  · intro δ h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl <;> decide
  · intro δ h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl <;> decide
  · intro δ h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨130477127726457, by simpa only [pow_two] using three_roots.1.symm⟩
    · exact ⟨228876284726978, by simpa only [pow_two] using three_roots.2.1.symm⟩
    · exact ⟨230840503340143, by simpa only [pow_two] using three_roots.2.2.symm⟩

/-- Multiplying the first and third signed values and dividing by 11²
gives −2. Combining −2 and 14 and dividing by 2² then gives −7. -/
theorem reduced_roots :
    (114937651990559 : ZMod 246180296426219)^2 = (-2 : ℤ) ∧
    (22031118570831 : ZMod 246180296426219)^2 = (-7 : ℤ) := by decide

/-- A directly enumerable period for the three small conductors. -/
noncomputable def reducedWheel : Finset ℕ :=
  (Finset.range 616).filter fun a => a%8 ∈ ({1,3} : Finset ℕ) ∧
    a%7 ∈ ({1,2,4} : Finset ℕ) ∧ a%11 ∈ ({1,3,4,5,9} : Finset ℕ)

private theorem neg_two_residue {r : ℕ} (hr : r < 8) (odd : r%2=1)
    (h : jacobiSym (-2) r = 1) : r ∈ ({1,3} : Finset ℕ) := by
  interval_cases r <;> norm_num at *

private theorem seven_residue {r : ℕ} (hr : r < 7) (h : jacobiSym (r : ℤ) 7 = 1) :
    r ∈ ({1,2,4} : Finset ℕ) := by
  interval_cases r <;> norm_num at *

private theorem eleven_residue {r : ℕ} (hr : r < 11) (h : jacobiSym (r : ℤ) 11 = 1) :
    r ∈ ({1,3,4,5,9} : Finset ℕ) := by
  interval_cases r <;> norm_num at *

/-- Every odd divisor of the input lies in a directly generated set of thirty
residues modulo 616. Only residues modulo 8, 7 and 11 enter the table. -/
theorem reduced_wheel_contains {d : ℕ} (dv : d ∣ 246180296426219) (odd : Odd d) :
    d % 616 ∈ reducedWheel := by
  have minusTwo := signed_divisor (D := -2) dv (by decide)
    ⟨114937651990559, by simpa only [pow_two] using reduced_roots.1.symm⟩
  have minusSeven := ReciprocalDivisorClasses.divisor (N := 246180296426219) (D := 7)
    (by decide) odd dv ((show Nat.Coprime 7 246180296426219 by decide).of_dvd_right dv)
    ⟨22031118570831, by simpa using reduced_roots.2.symm⟩
  have minusEleven := ReciprocalDivisorClasses.divisor (N := 246180296426219) (D := 11)
    (by decide) odd dv ((show Nat.Coprime 11 246180296426219 by decide).of_dvd_right dv)
    ⟨130477127726457, by simpa using three_roots.1.symm⟩
  have oddEight : d%8%2=1 := (Nat.mod_mod_of_dvd d (by decide : 2 ∣ 8)).trans (Nat.odd_iff.mp odd)
  have residue (k : ℕ) : jacobiSym ((d%k : ℕ) : ℤ) k = jacobiSym (d : ℤ) k := by
    simpa only [Int.natCast_mod] using (jacobiSym.mod_left (d : ℤ) k).symm
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by decide)), ?_⟩
  simp only [Nat.mod_mod_of_dvd d (by decide : 8 ∣ 616),
    Nat.mod_mod_of_dvd d (by decide : 7 ∣ 616), Nat.mod_mod_of_dvd d (by decide : 11 ∣ 616)]
  refine ⟨neg_two_residue (Nat.mod_lt _ (by decide)) oddEight ?_,
    seven_residue (Nat.mod_lt _ (by decide)) ((residue 7).trans minusSeven),
    eleven_residue (Nat.mod_lt _ (by decide)) ((residue 11).trans minusEleven)⟩
  exact (CharacterDivisorColumn.periodic (Nat.odd_iff.mpr oddEight) odd (-2)
    (Nat.mod_mod_of_dvd _ (by decide : 4*(-2 : ℤ).natAbs ∣ 8))).trans minusTwo

set_option maxRecDepth 4000 in
theorem reduced_wheel_card : reducedWheel.card = 30 := by decide

section Projection

variable {S L R : Type*} [AddCommGroup S] [Module (ZMod 2) S]
  [AddCommGroup L] [Module (ZMod 2) L] [AddCommGroup R] [Module (ZMod 2) R]
  (A : S →ₗ[ZMod 2] R) (B : L →ₗ[ZMod 2] R)

/-- One equation per input relation, with separate columns for the small
prime signs and all remaining signs. -/
def Extends (x : S) : Prop := ∃ y, A x + B y = 0

theorem extends_iff_range (x : S) : Extends A B x ↔ A x ∈ LinearMap.range B := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨-y, by rw [map_neg]; exact (eq_neg_of_add_eq_zero_left hy).symm⟩
  · rintro ⟨y, e⟩
    exact ⟨-y, by rw [map_neg, e, add_neg_cancel]⟩

/-- Exactly the row combinations cancelling the large columns constrain the
small signs. This equivalence also covers the case of no such restrictions. -/
theorem extends_iff_row_combinations (x : S) : Extends A B x ↔
    ∀ f : R →ₗ[ZMod 2] ZMod 2, f.comp B = 0 → f (A x) = 0 := by
  rw [extends_iff_range, ← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  apply forall_congr'
  intro f
  have h : f ∈ (LinearMap.range B).dualAnnihilator ↔ f.comp B = 0 := by
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro vanishes
      ext y
      exact vanishes _ ⟨y, rfl⟩
    · rintro e _ ⟨y, rfl⟩
      exact LinearMap.congr_fun e y
  rw [h]

/-- Independent private columns for all rows make the remaining signs free. -/
theorem extends_of_surjective (onto : Function.Surjective B) (x : S) : Extends A B x :=
  (extends_iff_range A B x).mpr (onto (A x))

/-- The rank of this map is the exact number of independent constraints
on the small sign vector after eliminating all other signs. -/
noncomputable def projectedMap : S →ₗ[ZMod 2] (R ⧸ LinearMap.range B) := (LinearMap.range B).mkQ.comp A

theorem extends_iff_ker (x : S) : Extends A B x ↔ x ∈ LinearMap.ker (projectedMap A B) := by
  rw [extends_iff_range, LinearMap.mem_ker, projectedMap, LinearMap.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- Exact count of compatible small sign vectors in finite dimension. -/
theorem number_of_sign_vectors [FiniteDimensional (ZMod 2) S] :
    Nat.card {x : S // Extends A B x} =
      2 ^ (Module.finrank (ZMod 2) S - Module.finrank (ZMod 2) (LinearMap.range (projectedMap A B))) := by
  let F := projectedMap A B
  have e : {x : S // Extends A B x} ≃ LinearMap.ker F :=
    Equiv.subtypeEquivRight (extends_iff_ker A B)
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_eq_fintype_card, ZMod.card]
  have rank := F.finrank_range_add_finrank_ker
  change 2 ^ Module.finrank (ZMod 2) (LinearMap.ker F) =
    2 ^ (Module.finrank (ZMod 2) S - Module.finrank (ZMod 2) (LinearMap.range F))
  congr 1
  omega

end Projection

end PrimeFactors.SquareClassProjection
