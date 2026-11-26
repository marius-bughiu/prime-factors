import PrimeFactors.WeightedTripleReduction
import PrimeFactors.WeightedMultiplierPell
import Mathlib.Data.Nat.ModEq

/-! Removing two proportional weighted rows preserves both signed gcds of
a square relation whenever their public labels are units modulo the input. -/

namespace PrimeFactors.WeightedSubsetReduction

/-- A pair of proportional positive remainders has a positive square root
congruent to the product of the labels with the same sign everywhere. -/
theorem pair_root {A B r s d e n : ℕ} (first : A^2 = d+4*r*n)
    (second : B^2 = e+4*s*n) (dp : 0 < d) (ep : 0 < e) (same : s*A^2 = r*B^2) :
    ∃ w : ℕ, 0 < w ∧ w^2 = d*e ∧ w ≤ A*B ∧ w ≡ A*B [MOD n] := by
  obtain ⟨w, hw⟩ := WeightedTripleReduction.square_of_proportional first second dp ep same
    (show d*e*(d*e) = (d*e)^2 by ring)
  have sq : w^2 = d*e := by simpa only [pow_two] using hw.symm
  have wp : 0 < w := by
    by_contra! h
    have zero : w = 0 := by omega
    rw [zero] at sq
    exact (Nat.mul_pos dp ep).ne' (by simpa using sq.symm)
  have le : w ≤ A*B := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    rw [sq, mul_pow]
    exact Nat.mul_le_mul (by omega) (by omega)
  exact ⟨w, wp, sq, le, (Nat.modEq_iff_dvd' le).mpr
    (Nat.gcd_eq_right_iff_dvd.mp (WeightedMultiplierPell.zero_gcd first second sq same))⟩

/-- Here P and F are the products of the other labels and remainders.
Deleting the pair gives exactly the same minus gcd and the same plus gcd. -/
theorem remove_pair {A B r s d e n P F z : ℕ} (first : A^2 = d+4*r*n)
    (second : B^2 = e+4*s*n) (dp : 0 < d) (ep : 0 < e) (same : s*A^2 = r*B^2)
    (aUnit : A.Coprime n) (bUnit : B.Coprime n) (bound : F ≤ P^2) (square : d*e*F = z^2) :
    ∃ u : ℕ, u^2 = F ∧ (A*B*P-z).gcd n = (P-u).gcd n ∧
      (A*B*P+z).gcd n = (P+u).gcd n := by
  obtain ⟨w, wp, ws, wle, modEq⟩ := pair_root first second dp ep same
  obtain ⟨u, rfl, us⟩ := AffineExcessSingle.remove_square wp (by rw [square.symm, ws])
  have ule : u ≤ P := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (us.trans_le bound)
  have unit : (A*B).Coprime n := (aUnit.symm.mul_right bUnit.symm).symm
  have congr := modEq.mul_right u
  have minus : (A*B*P-w*u) ≡ A*B*(P-u) [MOD n] := by
    apply congr.add_right_cancel
    rw [Nat.sub_add_cancel (Nat.mul_le_mul wle ule), ← Nat.mul_add, Nat.sub_add_cancel ule]
  have plus : (A*B*P+w*u) ≡ A*B*(P+u) [MOD n] := by
    rw [Nat.mul_add]
    exact congr.add_left _
  exact ⟨u, us, minus.gcd_eq.trans (unit.gcd_mul_left_cancel _),
    plus.gcd_eq.trans (unit.gcd_mul_left_cancel _)⟩

/-- The square condition and the two actual gcd outputs for an indexed subset. -/
def Matches {ι : Type*} (S : Finset ι) (A D : ι → ℕ) (n minus plus : ℕ) : Prop :=
  ∃ z : ℕ, (∏ i ∈ S, D i) = z^2 ∧ ((∏ i ∈ S, A i)-z).gcd n = minus ∧
    ((∏ i ∈ S, A i)+z).gcd n = plus

private theorem prod_erase_two {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℕ)
    {i j : ι} (hi : i ∈ S) (hj : j ∈ S) (ne : i ≠ j) :
    (∏ k ∈ S, f k) = f i*f j*(∏ k ∈ (S.erase i).erase j, f k) := by
  rw [← S.mul_prod_erase f hi,
    ← (S.erase i).mul_prod_erase f (Finset.mem_erase_of_ne_of_mem ne.symm hj),
    mul_assoc]

/-- Every match of positive remainders and unit labels contains a match with
identical outputs in which the weighted directions are pairwise distinct. -/
theorem reduced_subset {ι : Type*} (S : Finset ι) (A r D : ι → ℕ) {n minus plus : ℕ}
    (rows : ∀ i ∈ S, (A i)^2 = D i+4*r i*n) (pos : ∀ i ∈ S, 0 < D i)
    (units : ∀ i ∈ S, (A i).Coprime n) (hit : Matches S A D n minus plus) :
    ∃ T ⊆ S, Matches T A D n minus plus ∧
      ∀ i ∈ T, ∀ j ∈ T, i ≠ j → r j*(A i)^2 ≠ r i*(A j)^2 := by
  classical
  let pool := S.powerset.filter (fun T => Matches T A D n minus plus)
  have whole : S ∈ pool := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by rfl), hit⟩
  obtain ⟨T, hT, minimal⟩ := pool.exists_min_image Finset.card ⟨S, whole⟩
  obtain ⟨sub, matched⟩ := Finset.mem_filter.mp hT
  have hsub := Finset.mem_powerset.mp sub
  refine ⟨T, hsub, matched, ?_⟩
  intro i hi j hj ne same
  let U := (T.erase i).erase j
  have uSub : U ⊆ S := (Finset.erase_subset j _).trans ((Finset.erase_subset i _).trans hsub)
  have bound : (∏ k ∈ U, D k) ≤ (∏ k ∈ U, A k)^2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun k hk => by
      have := rows k (uSub hk); omega)
  obtain ⟨z, square, minusEq, plusEq⟩ := matched
  rw [prod_erase_two T D hi hj ne] at square
  rw [prod_erase_two T A hi hj ne] at minusEq plusEq
  obtain ⟨u, us, um, up⟩ := remove_pair (rows i (hsub hi)) (rows j (hsub hj))
    (pos i (hsub hi)) (pos j (hsub hj)) same (units i (hsub hi))
    (units j (hsub hj)) bound square
  have good : U ∈ pool := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr uSub,
    u, us.symm, um.symm.trans minusEq, up.symm.trans plusEq⟩
  have smaller : U.card < T.card :=
    Finset.card_erase_le.trans_lt (Finset.card_erase_lt_of_mem hi)
  exact (not_le_of_gt smaller) (minimal U good)

/-- The empty relation cannot give a proper minus gcd. -/
theorem nonempty_of_minus {ι : Type*} {S : Finset ι} {A D : ι → ℕ} {n minus plus : ℕ}
    (hit : Matches S A D n minus plus) (proper : minus < n) : S.Nonempty := by
  by_contra! empty
  rw [Finset.not_nonempty_iff_eq_empty.mp empty] at hit
  obtain ⟨z, eqn, hm, _⟩ := hit
  simp only [Finset.prod_empty] at eqn hm
  have one : z = 1 := (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp (by simpa using eqn.symm)
  simp [one] at hm
  omega

/-- A failed label-unit check already reveals a proper divisor whenever
the label lies strictly between zero and the product. -/
theorem label_split {A n : ℕ} (lo : 0 < A) (hi : A < n) (bad : ¬ A.Coprime n) :
    1 < A.gcd n ∧ A.gcd n < n := by
  have ne : A.gcd n ≠ 1 := by simpa only [Nat.coprime_iff_gcd_eq_one] using bad
  exact ⟨by have := Nat.gcd_pos_of_pos_left n lo; omega, (Nat.gcd_le_left n lo).trans_lt hi⟩

end PrimeFactors.WeightedSubsetReduction
