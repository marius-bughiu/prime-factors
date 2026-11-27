import PrimeFactors.UniversalSpacing
import PrimeFactors.TwoAdicSumSpacing
import PrimeFactors.ThreeAdicUniversalSpacing

/-! An integer is a possible spacing between locally admissible factor sums
for every product and every positive modulus exactly when 20160 divides it. -/
namespace PrimeFactors.UniversalSumStride
open FactorSumSpacing

/-- A prime at least five always has a factor pair with distinct coordinates.
Its trace lifts along every displacement which vanishes modulo the prime. -/
theorem prime_dividing_shift {p : ℕ} [Fact p.Prime] (large : 5≤p) (n t : ℤ)
    (div : (p:ℤ)∣t) (k : ℕ) : Gap (p^(k+1)) n t := by
  have two : (2 : ZMod p)≠0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
  have three : (3 : ZMod p)≠0 := by
    intro z
    have := Nat.le_of_dvd (by decide : 0<3) ((ZMod.natCast_zmod_eq_zero_iff_dvd 3 p).mp z)
    omega
  obtain ⟨x,y,prod,diff⟩ : ∃ x y : ZMod p, x*y=(n : ZMod p) ∧ x≠y := by
    by_cases one : (n : ZMod p)=1
    · refine ⟨2,1/2,by rw [one,mul_div_cancel₀ _ two],?_⟩
      intro h
      apply three
      have eq := (eq_div_iff two).mp h
      linear_combination eq
    · exact ⟨1,n,one_mul _,Ne.symm one⟩
  obtain ⟨s,hs⟩ := ZMod.intCast_surjective (x+y)
  have regular : (x+y)^2-4*(n : ZMod p)≠0 := by
    rw [←prod,show (x+y)^2-4*(x*y)=(x-y)^2 by ring]
    exact pow_ne_zero _ (sub_ne_zero.mpr diff)
  have tz := (ZMod.intCast_zmod_eq_zero_iff_dvd t p).mpr div
  have lift (u : ℤ) (eq : (u : ZMod p)=x+y) : AdmissibleSum (n : ZMod (p^(k+1))) u := by
    apply (admissibleSum_primePow_iff_of_regular (by omega : p≠2) n u ?_ k).mpr
    · exact ⟨x,y,prod,eq.symm⟩
    · simpa only [Int.cast_sub,Int.cast_pow,Int.cast_mul,Int.cast_ofNat,eq] using regular
  exact ⟨s,lift s hs,by simpa only [Int.cast_add] using lift (s+t) (by rw [Int.cast_add,tz,add_zero,hs])⟩

/-- Simultaneous local compatibility of a prescribed spacing at any positive
modulus. The two local factor pairs and their starting sum may depend on the modulus. -/
theorem all_moduli (n t : ℤ) (dt : (20160:ℤ)∣t) (m : ℕ) (hm : 0<m) :
    Gap m n t := by
  revert hm
  induction m using Nat.recOnPosPrimePosCoprime with
  | hp p k pp kp =>
    cases k with
    | zero => omega
    | succ k =>
      intro _
      letI : Fact p.Prime := ⟨pp⟩
      by_cases large : 11≤p
      · exact prime_power_all large n t k
      have small : p=2 ∨ p=3 ∨ p=5 ∨ p=7 := by
        have table : ∀ j : Fin 11, j.val.Prime → j.val=2 ∨ j.val=3 ∨ j.val=5 ∨ j.val=7 := by decide
        exact table ⟨p,by omega⟩ pp
      rcases small with rfl|rfl|rfl|rfl
      · exact TwoAdicSumSpacing.sixtyfour n t (k+1) ((by decide : (64:ℤ)∣20160).trans dt)
      · obtain ⟨h,rfl⟩ := (by decide : (9:ℤ)∣20160).trans dt
        exact ThreeAdicUniversalSpacing.multiple_nine n h k
      · exact prime_dividing_shift (by decide) n t ((by decide : (5:ℤ)∣20160).trans dt) k
      · exact prime_dividing_shift (by decide) n t ((by decide : (7:ℤ)∣20160).trans dt) k
  | h0 => omega
  | h1 =>
    intro _
    have every (s : ZMod 1) : AdmissibleSum (n : ZMod 1) s :=
      ⟨0,0,Subsingleton.elim _ _,Subsingleton.elim _ _⟩
    exact ⟨0,every _,every _⟩
  | h a b ha hb ab ia ib =>
    intro _
    exact (crt_iff ab n t).mpr ⟨ia (by omega),ib (by omega)⟩

private theorem nine (t : ZMod 9) : Gap 9 4 t → Gap 9 8 t → t=0 := by
  revert t
  unfold Gap AdmissibleSum
  decide +kernel

private theorem five (t : ZMod 5) : Gap 5 3 t → Gap 5 2 t → t=0 := by
  revert t
  unfold Gap AdmissibleSum
  decide +kernel

private noncomputable def gapDecision (n t : ZMod 7) : Decidable (Gap 7 n t) := by
  unfold Gap AdmissibleSum
  infer_instance

attribute [local instance] gapDecision

private theorem seven (t : ZMod 7) : Gap 7 5 t → Gap 7 3 t → Gap 7 6 t → t=0 := by
  revert t
  decide +kernel

/-- Finite witnesses for sharpness. These particular classes also occur on three
checked products of two distinct 1024-bit primes. -/
theorem necessary {t : ℤ} (two : Gap 64 1 t ∧ Gap 64 5 t ∧ Gap 64 59 t)
    (three : Gap 9 4 t ∧ Gap 9 8 t) (five' : Gap 5 3 t ∧ Gap 5 2 t)
    (seven' : Gap 7 5 t ∧ Gap 7 3 t ∧ Gap 7 6 t) : (20160:ℤ)∣t := by
  have d2 := TwoAdicSumSpacing.sixtyfour_needed t two.1 two.2.1 two.2.2
  have d3 := (ZMod.intCast_zmod_eq_zero_iff_dvd t 9).mp (nine t three.1 three.2)
  have d5 := (ZMod.intCast_zmod_eq_zero_iff_dvd t 5).mp (five t five'.1 five'.2)
  have d7 := (ZMod.intCast_zmod_eq_zero_iff_dvd t 7).mp (seven t seven'.1 seven'.2.1 seven'.2.2)
  have merge (a b : ℤ) (h : a.gcd b=1) (da : a∣t) (db : b∣t) : a*b∣t :=
    (Int.isCoprime_iff_gcd_eq_one.mpr h).mul_dvd da db
  exact merge 576 35 (by decide) (merge 64 9 (by decide) d2 d3) (merge 5 7 (by decide) d5 d7)

/-- Exact universal set of integer displacements, including zero and negative values. -/
theorem universal_iff (t : ℤ) : (∀ (n : ℤ) (m : ℕ), 0<m → Gap m n t) ↔ (20160:ℤ)∣t := by
  constructor
  · intro all
    apply necessary
    · exact ⟨all 1 64 (by decide),all 5 64 (by decide),all 59 64 (by decide)⟩
    · exact ⟨all 4 9 (by decide),all 8 9 (by decide)⟩
    · exact ⟨all 3 5 (by decide),all 2 5 (by decide)⟩
    · exact ⟨all 5 7 (by decide),all 3 7 (by decide),all 6 7 (by decide)⟩
  · intro dt n m hm
    exact all_moduli n t dt m hm

end PrimeFactors.UniversalSumStride
