import PrimeFactors.FactorSum
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace PrimeFactors

open Finset
open scoped Classical

section FiniteField
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private noncomputable def squareIndicator (x : F) : ℤ := if IsSquare x then 1 else 0

private theorem twice_squareIndicator (x : F) :
    2 * squareIndicator x = 1 + quadraticChar F x + (if x = 0 then 1 else 0) := by
  by_cases zero : x = 0
  · simp [squareIndicator, zero, quadraticChar_zero]
  · by_cases sq : IsSquare x
    · simp [squareIndicator, zero, sq, (quadraticChar_one_iff_isSquare zero).mpr sq]
    · simp [squareIndicator, zero, sq, quadraticChar_neg_one_iff_not_isSquare.mpr sq]

/-- The two shifted linear characters have total correlation minus one. -/
private theorem shifted_character_sum (odd : ringChar F ≠ 2) {h : F} (hh : h ≠ 0) :
    ∑ x : F, quadraticChar F x * quadraticChar F (x + h) = -1 := by
  let χ := quadraticChar F
  have j := jacobiSum_nontrivial_inv (quadraticChar_ne_one odd)
  rw [(quadraticChar_isQuadratic F).inv] at j
  have hh2 := quadraticChar_sq_one hh
  have hm2 := quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0))
  change ∑ x : F, χ x * χ (x + h) = -1
  calc
    _ = ∑ x : F, χ (-h * x) * χ (-h * x + h) :=
      (Equiv.sum_comp (Equiv.mulLeft₀ (-h) (neg_ne_zero.mpr hh)) (fun x => χ x * χ (x + h))).symm
    _ = ∑ x : F, χ (-1) * (χ x * χ (1 - x)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [show -h * x + h = h * (1 - x) by ring, show -h = -1 * h by ring, map_mul, map_mul,
        map_mul]
      change quadraticChar F (-1) * quadraticChar F h * quadraticChar F x *
        (quadraticChar F h * quadraticChar F (1 - x)) = _
      linear_combination quadraticChar F (-1) * quadraticChar F x * quadraticChar F (1 - x) * hh2
    _ = χ (-1) * jacobiSum χ χ := (Finset.mul_sum ..).symm
    _ = -1 := by
      change quadraticChar F (-1) * jacobiSum (quadraticChar F) (quadraticChar F) = -1
      rw [j]
      nlinarith

/-- Count products including the singular discriminants at both endpoints. -/
private theorem shifted_square_sum (odd : ringChar F ≠ 2) (neg : quadraticChar F (-1) = -1)
    (h : F) (hh : h ≠ 0) :
    4 * ∑ x : F, squareIndicator x * squareIndicator (x + h) = Fintype.card F + 1 := by
  let χ := quadraticChar F
  have anti : χ (-h) = -χ h := by
    change quadraticChar F (-h) = _
    rw [show -h = (-1) * h by ring, map_mul, neg]
    ring
  have point (x : F) : 4 * (squareIndicator x * squareIndicator (x+h)) =
      1 + χ x + χ (x+h) + χ x * χ (x+h) +
        (if x = 0 then 1 + χ h else 0) + (if x = -h then 1 + χ (-h) else 0) := by
    calc
      _ = (2 * squareIndicator x) * (2 * squareIndicator (x+h)) := by ring
      _ = _ := by
        rw [twice_squareIndicator, twice_squareIndicator]
        by_cases hx : x = 0
        · subst x
          simp [χ, hh, quadraticChar_zero]
          ring
        · by_cases hm : x = -h
          · subst x
            simp [χ, hx, hh, quadraticChar_zero]
            ring
          · have hsum : x + h ≠ 0 := fun he => hm (eq_neg_of_add_eq_zero_left he)
            simp [χ, hx, hm, hsum]
            ring
  have sum1 : ∑ x : F, χ x = 0 := quadraticChar_sum_zero odd
  have sum2 : ∑ x : F, χ (x + h) = 0 := (Equiv.sum_comp (Equiv.addRight h) χ).trans sum1
  have corr : ∑ x : F, χ x * χ (x + h) = -1 := shifted_character_sum odd hh
  rw [Finset.mul_sum]
  simp_rw [point]
  simp [Finset.sum_add_distrib, sum1, sum2, corr, anti]
  ring

private theorem twice_sum_squareIndicator (odd : ringChar F ≠ 2) :
    2 * ∑ x : F, squareIndicator x = Fintype.card F + 1 := by
  rw [Finset.mul_sum]
  simp_rw [twice_squareIndicator]
  simp [Finset.sum_add_distrib]
  exact quadraticChar_sum_zero odd

end FiniteField

/-- Exactly half the unit products are locally compatible with any one proposed sum. -/
theorem single_admissible_products {ℓ : ℕ} [Fact ℓ.Prime] (odd : ℓ ≠ 2) (s : ZMod ℓ) :
    2 * ∑ n ∈ (univ.erase (0 : ZMod ℓ)),
      (if AdmissibleSum n s then (1 : ℤ) else 0) + 1 = ℓ := by
  have charOdd : ringChar (ZMod ℓ) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have two : (2 : ZMod ℓ) ≠ 0 := Ring.two_ne_zero charOdd
  have four : (4 : ZMod ℓ) ≠ 0 := by
    simpa only [show (4 : ZMod ℓ) = 2 * 2 by norm_num] using mul_ne_zero two two
  let e := (Equiv.mulLeft₀ 4 four).trans (Equiv.subLeft (s ^ 2))
  let mask := fun n : ZMod ℓ => if AdmissibleSum n s then (1 : ℤ) else 0
  have term (n : ZMod ℓ) : squareIndicator (e n) = mask n := by
    simp only [squareIndicator, mask, admissibleSum_iff_isSquare odd]
    rfl
  have all : 2 * ∑ x : ZMod ℓ, squareIndicator x = ℓ + 1 := by
    simpa only [ZMod.card] using twice_sum_squareIndicator charOdd
  rw [← Equiv.sum_comp e squareIndicator] at all
  simp only [term] at all
  have mask0 : mask 0 = 1 := by simp [mask, admissibleSum_iff_isSquare odd, IsSquare.sq]
  have split := Finset.sum_erase_add (s := univ) mask (Finset.mem_univ (0 : ZMod ℓ))
  rw [mask0] at split
  change 2 * ∑ n ∈ (univ.erase (0 : ZMod ℓ)), mask n + 1 = ℓ
  linarith

/-- For a prime 3 modulo 4 and two candidates with distinct squared residues, exactly
(ℓ−3)/4 nonzero product residues admit both candidates. This averages over products. -/
theorem paired_admissible_products {ℓ : ℕ} [Fact ℓ.Prime] (three : ℓ % 4 = 3)
    (s t : ZMod ℓ) (distinct : s ^ 2 ≠ t ^ 2) :
    4 * ∑ n ∈ (univ.erase (0 : ZMod ℓ)),
      (if AdmissibleSum n s ∧ AdmissibleSum n t then (1 : ℤ) else 0) + 3 = ℓ := by
  have odd : ℓ ≠ 2 := by omega
  have charOdd : ringChar (ZMod ℓ) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have neg : quadraticChar (ZMod ℓ) (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr (by simpa [FiniteField.isSquare_neg_one_iff] using three)
  have four : (4 : ZMod ℓ) ≠ 0 := by
    have two : (2 : ZMod ℓ) ≠ 0 := Ring.two_ne_zero charOdd
    simpa only [show (4 : ZMod ℓ) = 2 * 2 by norm_num] using mul_ne_zero two two
  let mask := fun n : ZMod ℓ => if AdmissibleSum n s ∧ AdmissibleSum n t then (1 : ℤ) else 0
  let f := fun x : ZMod ℓ => squareIndicator x * squareIndicator (x + (t^2-s^2))
  let e := (Equiv.mulLeft₀ 4 four).trans (Equiv.subLeft (s ^ 2))
  have term (n : ZMod ℓ) : f (e n) = mask n := by
    change squareIndicator (s^2 - 4*n) * squareIndicator (s^2-4*n+(t^2-s^2)) = _
    rw [show s^2-4*n+(t^2-s^2) = t^2-4*n by ring]
    simp only [mask, squareIndicator, admissibleSum_iff_isSquare odd]
    split_ifs <;> simp_all
  have corr := shifted_square_sum charOdd neg (t^2-s^2) (sub_ne_zero.mpr distinct.symm)
  change 4 * ∑ x : ZMod ℓ, f x = _ at corr
  rw [← Equiv.sum_comp e f] at corr
  simp only [term, ZMod.card] at corr
  have mask0 : mask 0 = 1 := by simp [mask, admissibleSum_iff_isSquare odd, IsSquare.sq]
  have split := Finset.sum_erase_add (s := univ) mask (Finset.mem_univ (0 : ZMod ℓ))
  rw [mask0] at split
  change 4 * ∑ n ∈ (univ.erase (0 : ZMod ℓ)), mask n + 3 = ℓ
  linarith

/-- A signed local test contributes +1 for a passing candidate and −1 for a rejection. -/
noncomputable def admissibleSign {m : ℕ} (n s : ZMod m) : ℤ :=
  if AdmissibleSum n s then 1 else -1

private theorem signed_pair_sum {ℓ : ℕ} [Fact ℓ.Prime] (three : ℓ % 4 = 3)
    (s t : ZMod ℓ) : ∑ n ∈ (univ.erase (0 : ZMod ℓ)),
      admissibleSign n s * admissibleSign n t = if s ^ 2 = t ^ 2 then (ℓ : ℤ)-1 else -2 := by
  have odd : ℓ ≠ 2 := by omega
  let units := univ.erase (0 : ZMod ℓ)
  have count : (units.card : ℤ) + 1 = ℓ := by
    have h := Finset.card_erase_add_one (Finset.mem_univ (0 : ZMod ℓ))
    simp only [Finset.card_univ, ZMod.card] at h
    exact_mod_cast h
  split_ifs with eq
  · have term (n : ZMod ℓ) : admissibleSign n s * admissibleSign n t = 1 := by
      simp only [admissibleSign, admissibleSum_iff_isSquare odd, eq]
      split_ifs <;> decide
    simp only [term, Finset.sum_const, nsmul_eq_mul, mul_one]
    change (units.card : ℤ) = _
    omega
  · let mask := fun (n v : ZMod ℓ) => if AdmissibleSum n v then (1 : ℤ) else 0
    let both := fun n : ZMod ℓ => if AdmissibleSum n s ∧ AdmissibleSum n t then (1 : ℤ) else 0
    have term (n : ZMod ℓ) : admissibleSign n s * admissibleSign n t =
        4 * both n - 2 * mask n s - 2 * mask n t + 1 := by
      simp only [admissibleSign, mask, both]
      split_ifs <;> simp_all
    have singles := single_admissible_products odd s
    have singlet := single_admissible_products odd t
    have pair := paired_admissible_products three s t eq
    change 2 * ∑ n ∈ units, mask n s + 1 = ℓ at singles
    change 2 * ∑ n ∈ units, mask n t + 1 = ℓ at singlet
    change 4 * ∑ n ∈ units, both n + 3 = ℓ at pair
    change ∑ n ∈ units, _ = -2
    simp only [term, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith

/-- Exact second moment over nonzero product residues for any candidate block whose
squared residues are distinct. The signed sum is twice the survivor count minus the block size. -/
theorem admissible_block_second_moment {ℓ : ℕ} [Fact ℓ.Prime] (three : ℓ % 4 = 3)
    (B : Finset (ZMod ℓ)) (distinct : Set.InjOn (fun s : ZMod ℓ => s ^ 2) B) :
    ∑ n ∈ (univ.erase (0 : ZMod ℓ)), (∑ s ∈ B, admissibleSign n s) ^ 2 =
      (B.card : ℤ) * (ℓ + 1 - 2 * B.card) := by
  let units := univ.erase (0 : ZMod ℓ)
  have row (s : ZMod ℓ) (hs : s ∈ B) : (∑ t ∈ B,
      ∑ n ∈ units, admissibleSign n s * admissibleSign n t) =
      (ℓ : ℤ) + 1 - 2 * B.card := by
    have entries (t : ZMod ℓ) (ht : t ∈ B) :
        (∑ n ∈ units, admissibleSign n s * admissibleSign n t) =
        (if t = s then (ℓ : ℤ) + 1 else 0) - 2 := by
      rw [signed_pair_sum three]
      by_cases same : t = s
      · simp [same]
        ring
      · have sq : s ^ 2 ≠ t ^ 2 := fun h => same (distinct hs ht h).symm
        simp [sq, same]
    rw [Finset.sum_congr rfl entries, Finset.sum_sub_distrib]
    simp [hs]
    ring
  calc
    _ = ∑ n ∈ units, ∑ s ∈ B, ∑ t ∈ B, admissibleSign n s * admissibleSign n t := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum, units]
      simp only [mul_comm]
    _ = ∑ s ∈ B, ∑ t ∈ B, ∑ n ∈ units, admissibleSign n s * admissibleSign n t := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_congr rfl row]
      simp
      ring

/-- For every fixed nonzero product, precisely a quarter (rounded up) of the field
consists of square classes that cannot be the square of an admissible sum. -/
theorem rejected_square_class_count {ℓ : ℕ} [Fact ℓ.Prime] (three : ℓ % 4 = 3)
    (n : ZMod ℓ) (hn : n ≠ 0) :
    4 * ((univ.filter fun x : ZMod ℓ => IsSquare x ∧ ¬ IsSquare (x - 4 * n)).card : ℤ) =
      ℓ + 1 := by
  have odd : ℓ ≠ 2 := by omega
  have charOdd : ringChar (ZMod ℓ) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have neg : quadraticChar (ZMod ℓ) (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr (by simpa [FiniteField.isSquare_neg_one_iff] using three)
  have two : (2 : ZMod ℓ) ≠ 0 := Ring.two_ne_zero charOdd
  have four : (4 : ZMod ℓ) ≠ 0 := by
    simpa only [show (4 : ZMod ℓ) = 2 * 2 by norm_num] using mul_ne_zero two two
  have pair := shifted_square_sum charOdd neg (-(4*n)) (neg_ne_zero.mpr (mul_ne_zero four hn))
  simp only [← sub_eq_add_neg, ZMod.card] at pair
  have singles := twice_sum_squareIndicator charOdd
  rw [ZMod.card] at singles
  have term (x : ZMod ℓ) :
      (if IsSquare x ∧ ¬ IsSquare (x-4*n) then (1 : ℤ) else 0) =
      squareIndicator x - squareIndicator x * squareIndicator (x - 4*n) := by
    simp only [squareIndicator]
    split_ifs <;> simp_all
  rw [← Finset.sum_boole]
  simp_rw [term, Finset.sum_sub_distrib]
  linarith

/-- A prime cannot reject a block with more distinct squared candidate residues than
there are rejected square classes. The block may repeat squared residues. -/
theorem block_has_admissible_of_square_classes {ℓ : ℕ} [Fact ℓ.Prime] (three : ℓ % 4 = 3)
    (n : ZMod ℓ) (hn : n ≠ 0) (B : Finset (ZMod ℓ))
    (large : ℓ + 1 < 4 * (B.image (fun s => s ^ 2)).card) :
    ∃ s ∈ B, AdmissibleSum n s := by
  by_contra! fail
  have odd : ℓ ≠ 2 := by omega
  have subset : B.image (fun s => s ^ 2) ⊆
      univ.filter (fun x : ZMod ℓ => IsSquare x ∧ ¬ IsSquare (x - 4*n)) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsSquare.sq s,
      fun h => fail s hs ((admissibleSum_iff_isSquare odd _ _).mpr h)⟩
  have counted := Finset.card_le_card subset
  have fixed := rejected_square_class_count three n hn
  omega

/-- Four distinct, consecutive candidates in the required mod-four progression
can all fail the same prime. Their squares repeat two classes. -/
theorem four_rejections_mod_seven :
    ∀ i : Fin 4, ¬ AdmissibleSum (34387 : ZMod 7) (372 + 4 * (i.val : ZMod 7)) := by
  unfold AdmissibleSum
  decide

end PrimeFactors
