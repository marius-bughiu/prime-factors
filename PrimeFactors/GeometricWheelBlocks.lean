import PrimeFactors.GeometricBlockReading
import PrimeFactors.GeometricSumLanes

/-! Evaluation of a filtered geometric product at a shared step. Relative indices
start at zero at the lower endpoint of the sum interval. The residue filter
continues to test the absolute sum. -/
namespace PrimeFactors.GeometricWheelBlocks

open Finset GeometricBlockReading

/-- Number of indices with offset `a<m` in an interval of `count` positions. -/
def laneLength (m count a : ℕ) : ℕ := count/m + if a<count%m then 1 else 0

theorem index_lt {a m : ℕ} (ha : a<m) (count j : ℕ) :
    a+m*j<count ↔ j<laneLength m count a := by
  have hp : 0<m := by omega
  have total := Nat.mod_add_div count m
  have rem := Nat.mod_lt count hp
  unfold laneLength
  rcases lt_trichotomy j (count/m) with less | eq | more
  · have step := Nat.mul_le_mul_left m (show j+1≤count/m by omega)
    rw [Nat.mul_succ] at step
    split_ifs <;> omega
  · subst j
    split_ifs <;> omega
  · have step := Nat.mul_le_mul_left m (show count/m+1≤j by omega)
    rw [Nat.mul_succ] at step
    split_ifs <;> omega

private theorem lane_image {a m : ℕ} (ha : a<m) (count : ℕ) :
    ((range (laneLength m count a)).image (fun j => a+m*j)) =
      (range count).filter (fun i => i%m=a) := by
  ext i
  simp only [mem_image,mem_range,mem_filter]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact ⟨(index_lt ha ..).mpr hj, by simp [Nat.mod_eq_of_lt ha]⟩
  · rintro ⟨lt,mod⟩
    have eq : a+m*(i/m)=i := by simpa only [mod] using Nat.mod_add_div i m
    exact ⟨i/m,(index_lt ha count (i/m)).mp (eq.trans_lt lt),eq⟩

/-- The union of residue progressions has exactly the sum of their individual
lengths, including the possibly incomplete last turn. -/
theorem retained_count (M : Finset ℕ) {m : ℕ} (valid : ∀ a∈M, a<m) (count : ℕ) :
    ((range count).filter (fun i => i%m∈M)).card = ∑ a∈M, laneLength m count a := by
  rw [←sum_card_fiberwise_eq_card_filter (range count) M (fun i => i%m)]
  apply sum_congr rfl
  intro a ha
  have pos : 0<m := Nat.zero_lt_of_lt (valid a ha)
  rw [←lane_image (valid a ha),card_image_of_injective _ (by
    intro i j eq
    exact Nat.eq_of_mul_eq_mul_left pos (Nat.add_left_cancel eq)), card_range]

variable {R : Type*} [CommRing R]

/-- Every progression uses the same geometric base. Its scaled target and
the correction for its exact length depend on its offset. -/
theorem normalized_lane (y : R) (h : Rˣ) (a m len : ℕ) :
    (∏ j∈range len, (y-(h:R)^(a+m*j))) =
      ((h:R)^a)^len * block (y*((↑(h⁻¹):R)^a)) (h^m) len := by
  unfold block
  rw [show ((h:R)^a)^len = ∏ _j∈range len, (h:R)^a by simp, ←prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  have inv : (h:R)^a*(↑(h⁻¹):R)^a=1 := by rw [←mul_pow,Units.mul_inv,one_pow]
  rw [pow_add, pow_mul, Units.val_pow_eq_pow_val,mul_sub]
  rw [show (h:R)^a * (y*(↑(h⁻¹):R)^a)=y*((h:R)^a*(↑(h⁻¹):R)^a) by ring,inv,mul_one]

/-- The shared full evaluation and (where present) its one last normalized
factor. The empty product also handles intervals shorter than the modulus. -/
noncomputable def corrected (y : R) (h : Rˣ) (a m count : ℕ) : R :=
  let u := y*((↑(h⁻¹):R)^a)
  ((h:R)^a)^(laneLength m count a) *
    (block u (h^m) (count/m) *
     (if a<count%m then u-((h:R)^m)^(count/m) else 1))

theorem wheel (y : R) (h : Rˣ) {m : ℕ} (M : Finset ℕ)
    (valid : ∀ a∈M, a<m) (count : ℕ) :
    (∏ i∈(range count).filter (fun i => i%m∈M), (y-(h:R)^i)) =
      ∏ a∈M, corrected y h a m count := by
  rw [←prod_fiberwise_eq_prod_filter (range count) M (fun i => i%m)]
  apply prod_congr rfl
  intro a ha
  have pos : 0<m := Nat.zero_lt_of_lt (valid a ha)
  rw [←lane_image (valid a ha),prod_image (by
    intro i _ j _ eq
    exact Nat.eq_of_mul_eq_mul_left pos (Nat.add_left_cancel eq)), normalized_lane]
  unfold corrected laneLength
  split_ifs <;> simp [block,prod_range_succ]

/-- The original allowed absolute sums determine the filtered set of relative
indices; the perturbed scalar is evaluated on that set without renumbering. -/
theorem mem_kept_iff {n lower count i : ℕ} :
    i ∈ GeometricSumLanes.kept n lower count ↔
      i<count ∧ (lower+i)%32∈GeometricSumLanes.residues (n%32) := by
  simp only [GeometricSumLanes.kept,GeometricSumLanes.offsets,mem_filter,mem_range,
    Nat.mod_lt _ (by decide : 0<32),true_and,←Nat.add_mod]

/-- All the retained relative indices use one geometric base of stride 32. -/
theorem wheel32 (y : R) (h : Rˣ) (n lower count : ℕ) :
    (∏ i∈GeometricSumLanes.kept n lower count, (y-(h:R)^i)) =
      ∏ a∈GeometricSumLanes.offsets (n%32) (lower%32), corrected y h a 32 count :=
  wheel y h _ (fun _ ha => mem_range.mp (mem_filter.mp ha).1) count

theorem reading (y g z t : R) (h : Rˣ) (root : (h:R)=g*(1+t)) (n lower count : ℕ) :
    (GeometricReadingLift.product (GeometricSumLanes.kept n lower count) y g z).eval t =
      ∏ a∈GeometricSumLanes.offsets (n%32) (lower%32), corrected (y*(1+z*t)) h a 32 count := by
  rw [GeometricReadingLift.eval_product,←root,wheel32]

end PrimeFactors.GeometricWheelBlocks
