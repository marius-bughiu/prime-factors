import PrimeFactors.PrimitiveIntervalSuppliedExample
import PrimeFactors.IntervalWheelResidues

/-! Count the sums compatible with a supplied interval reading and public
modular arithmetic, including a final incomplete period of residues. -/
namespace PrimeFactors.IntervalWheelBand

open Finset PrimitiveIntervalCandidateBand PrimitiveIntervalMoment

noncomputable def screened (n b : ℕ) (v : ℤ) (e w : ℕ) : Finset ℕ := by
  classical
  exact (candidates n b v e).filter fun s => AdmissibleSum (n : ZMod w) (s : ZMod w)

theorem mem_screened {n b s e w : ℕ} {v : ℤ} :
    s ∈ screened n b v e w ↔
      s ∈ candidates n b v e ∧ AdmissibleSum (n : ZMod w) (s : ZMod w) := by
  classical
  exact mem_filter

/-- The modular test has a witness for the actual sum at every modulus. -/
theorem contains_true_sum {p q e : ℕ} {v exactValue : ℤ} [Fact p.Prime] [Fact q.Prime]
    (ord : p < q) (balanced : q < 2*p) (odd : (p*q)%2=1)
    (reading : aggregate p q (cutoff (p*q))=(exactValue:ℂ))
    (error : |exactValue-v| ≤ e) (w : ℕ) :
    p+q ∈ screened (p*q) (cutoff (p*q)) v e w := by
  exact mem_screened.mpr ⟨contains_from_aggregate ord balanced odd reading error,
    admissibleSum_of_factor_pair w rfl⟩

/-- On a band of diameter at most d, record the block relative to its first
element and the absolute sum residue. Together they determine the sum. -/
theorem count_blocks {n b e w d : ℕ} {v : ℤ} (positive : 0 < w)
    (diameter : ∀ s ∈ candidates n b v e, ∀ t ∈ candidates n b v e, s ≤ t → t-s ≤ d) :
    (screened n b v e w).card ≤ (d/w+1)*LocalSumMenu.count n w := by
  classical
  letI : NeZero w := ⟨positive.ne'⟩
  let S := screened n b v e w
  change S.card ≤ _
  by_cases nonempty : S.Nonempty
  · let m := S.min' nonempty
    have hm := (mem_screened.mp (S.min'_mem nonempty)).1
    have least (x : S) : m ≤ x.val := S.min'_le _ x.property
    let R := {r : ZMod w // AdmissibleSum (n : ZMod w) r}
    let encode (x : S) : Fin (d/w+1) × R :=
      (⟨(x.val-m)/w, Nat.lt_succ_of_le (Nat.div_le_div_right
        (diameter m hm x.val (mem_screened.mp x.property).1 (least x)))⟩,
       ⟨(x.val : ZMod w),(mem_screened.mp x.property).2⟩)
    have inject : Function.Injective encode := by
      intro x y equal
      have quot : (x.val-m)/w = (y.val-m)/w := congrArg (fun a => a.1.val) equal
      have residue : (x.val : ZMod w) = (y.val : ZMod w) :=
        congrArg (fun a => a.2.val) equal
      have offset : ((x.val-m : ℕ) : ZMod w) = ((y.val-m : ℕ) : ZMod w) := by
        rw [Nat.cast_sub (least x),Nat.cast_sub (least y),residue]
      have rem := congrArg ZMod.val offset
      simp only [ZMod.val_natCast] at rem
      have same := congrArg₂ (fun q r : ℕ => w*q+r) quot rem
      simp only [Nat.div_add_mod] at same
      exact Subtype.ext (by have := least x; have := least y; omega)
    have bound := Nat.card_le_card_of_injective encode inject
    rw [Nat.card_prod] at bound
    simpa only [LocalSumMenu.count, R, Nat.card_eq_fintype_card, Fintype.card_fin,
      Fintype.card_coe] using bound
  · simp [not_nonempty_iff_eq_empty.mp nonempty]

/-- A budget of 2^1050 on a full-size input permits a sum diameter of 2^27. -/
theorem full_width_blocks {n e w : ℕ} (v : ℤ) (positive : 0 < w)
    (size : 2^2047 ≤ n) (error : e ≤ 2^1050) :
    (screened n (cutoff n) v e w).card ≤ (2^27/w+1)*LocalSumMenu.count n w := by
  apply count_blocks positive
  intro s hs t ht ord
  have lower := full_width_cutoff size
  have dist := (ordered_diameter hs ht ord).trans error
  have cost := (Nat.mul_le_mul_right (t-s) (by omega : 2^1023 ≤ cutoff n+3)).trans dist
  rw [show (2:ℕ)^1050=2^1023*2^27 by rw [←pow_add]] at cost
  exact Nat.le_of_mul_le_mul_left cost (by positivity)

theorem full_width_635040 {n e : ℕ} (v : ℤ)
    (cop : IntervalWheelResidues.modulus.Coprime n)
    (size : 2^2047 ≤ n) (error : e ≤ 2^1050) :
    (screened n (cutoff n) v e IntervalWheelResidues.modulus).card ≤ 635040 := by
  have blocks := full_width_blocks v (w:=IntervalWheelResidues.modulus) (by decide) size error
  have periods : 2^27/IntervalWheelResidues.modulus+1=7 := by decide +kernel
  rw [periods] at blocks
  exact blocks.trans (Nat.mul_le_mul_left 7 (IntervalWheelResidues.count_le cop))

/-- Every product in the stated 2,048-bit population meets the wheel's
coprimality hypothesis because the modulus is smaller than either prime. -/
theorem balanced_635040 {p q e : ℕ} (pp : p.Prime) (qp : q.Prime)
    (width : 2^1023 ≤ p) (ord : p ≤ q) (v : ℤ) (size : 2^2047 ≤ p*q) (error : e ≤ 2^1050) :
    (screened (p*q) (cutoff (p*q)) v e IntervalWheelResidues.modulus).card ≤ 635040 := by
  have small : IntervalWheelResidues.modulus < p :=
    (by decide +kernel : IntervalWheelResidues.modulus < 2^1023).trans_le width
  have positive : 0 < IntervalWheelResidues.modulus := by decide
  have pc := pp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt positive small)
  have qc := qp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt positive (small.trans_le ord))
  exact full_width_635040 v (pc.symm.mul_right qc.symm) size error

/-- On the seeded 39-bit example, remainders modulo 15 distinguish all four
wrong sums from the true one before an integer square root is needed. -/
theorem control39 :
    screened 419636024497 458058 (-112538867588) 16000000 15 = {1310542} := by
  ext s
  rw [mem_screened,PrimitiveIntervalSuppliedExample.five_candidates]
  simp only [mem_insert,mem_singleton]
  constructor
  · rintro ⟨cases,allowed⟩
    rcases cases with rfl|rfl|rfl|rfl|rfl <;> first | rfl | (exfalso; revert allowed; unfold AdmissibleSum; decide +kernel)
  · rintro rfl
    exact ⟨by simp,⟨(556559:ZMod 15),(753983:ZMod 15),by decide +kernel,by decide +kernel⟩⟩

end PrimeFactors.IntervalWheelBand
