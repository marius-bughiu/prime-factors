import PrimeFactors.FiniteWheelPrecision
import PrimeFactors.StableDiscriminantClasses
import PrimeFactors.PublicPrimeSquareCounts
import PrimeFactors.SevenPrimeFilterSavings

/-! Compare a fixed mod-four condition and seven odd prime-square tests to
the same mod-four condition and every power of the same seven odd primes,
inside each published factor-width interval. -/

namespace PrimeFactors.PublicStableWheelCounts

open SevenPrimeFilterSavings (prime isSquareAt)
open PublicWheelWidthControls (start width tests period_bounds)
open LocalSumMenu (count)
open ChebyshevQuarticScale (fresh crossed)
open StableDiscriminantClasses (stableCount)

set_option maxRecDepth 8192
set_option exponentiation.threshold 4096

private abbrev Row := Option (Fin 7)

private def modulus : Row → ℕ
  | none => 4
  | some i => (prime i)^16

private theorem positive : ∀ i, 0 < modulus i := by decide +kernel
private theorem cop : Pairwise (fun i j => (modulus i).Coprime (modulus j)) := by
  unfold Pairwise
  decide +kernel

private theorem primes : ∀ i : Fin 7, (prime i).Prime ∧ prime i ≠ 2 := by decide +kernel
private instance (i : Row) : NeZero (modulus i) := ⟨(positive i).ne'⟩

private noncomputable def rows (n : ℕ) (settled : Bool) :
    (i : Row) → Finset (ZMod (modulus i)) := by
  classical
  intro i
  exact match i with
  | none => Finset.univ.filter (AdmissibleSum (n : ZMod 4))
  | some j => Finset.univ.filter fun s => AdmissibleSum (n : ZMod ((prime j)^16)) s ∧
      (settled = false ∨ s^2-4*n ≠ 0)

/-- A sum passes modulo four and at every positive odd prime-power depth
for the primes 3, 5, 7, 11, 13, 17 and 19. -/
def AllPowers (n s : ℕ) : Prop :=
  AdmissibleSum (n : ZMod 4) (s : ZMod 4) ∧ ∀ i : Fin 7, ∀ e : ℕ,
    AdmissibleSum (n : ZMod ((prime i)^e)) (s : ZMod ((prime i)^e))

noncomputable def survivors (n : ℕ) :=
  Nat.card {k : Fin (width n) // AllPowers n (start n+k.val)}

private noncomputable def size (n : ℕ) (settled : Bool) : Row → ℕ
  | none => 1
  | some i => primePowerSumCount (prime i) (isSquareAt i n) 16 -
      (if settled && isSquareAt i n then 2 else 0)

private theorem sizes {n : ℕ} (odd : ¬2∣n) (unit : ∀ i, ¬prime i ∣ n)
    (b : Bool) (i : Row) : (rows n b i).card = size n b i := by
  classical
  cases i with
  | none =>
    have h := IntervalWheelResidues.count_four odd
    simpa only [rows,size,count,Nat.card_eq_fintype_card,Fintype.card_subtype] using h
  | some i =>
    letI : Fact (prime i).Prime := ⟨(primes i).1⟩
    have sign : isSquareAt i n = true ↔ IsSquare (n : ZMod (prime i)) := by
      rw [isSquareAt,decide_eq_true_eq]
      constructor <;> rintro ⟨x,h⟩ <;> exact ⟨x,h.symm⟩
    have nz : firstPrimeDigit (prime i) 15 (n : ZMod ((prime i)^16)) ≠ 0 := by
      rw [map_natCast]
      exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp.mt (unit i)
    have total := card_primePower_admissibleSum (primes i).2 15 _ nz
    rw [map_natCast] at total
    simp only [Nat.reduceAdd] at total
    have safe := StableDiscriminantClasses.stable_count (primes i).2 (unit i) 15
    change stableCount n ((prime i)^16) + _ =
      Nat.card {s : ZMod ((prime i)^16) // AdmissibleSum (n : ZMod ((prime i)^16)) s} at safe
    rw [total] at safe
    cases b with
    | false =>
      simp only [rows,size,Bool.false_and,Bool.false_eq_true,if_false,Nat.sub_zero,
        true_or,and_true]
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at total
      by_cases sq : IsSquare (n : ZMod (prime i))
      · simpa only [sq,decide_true,sign.mpr sq] using total
      · have bit : isSquareAt i n = false := Bool.eq_false_iff.mpr (fun h => sq (sign.mp h))
        simpa only [sq,decide_false,bit] using total
    | true =>
      simp only [rows,size,Bool.true_and,Bool.true_eq_false,false_or]
      rw [stableCount,Nat.card_eq_fintype_card,Fintype.card_subtype] at safe
      by_cases sq : IsSquare (n : ZMod (prime i))
      · simp only [sq,if_true,decide_true] at safe
        simp only [sign.mpr sq,if_true]
        exact Nat.eq_sub_of_add_eq safe
      · have bit : isSquareAt i n = false := Bool.eq_false_iff.mpr (fun h => sq (sign.mp h))
        simpa only [sq,if_false,decide_false,bit,Bool.false_eq_true,Nat.sub_zero,add_zero] using safe

private theorem bounds {n : ℕ} (odd : ¬2∣n) (unit : ∀ i, ¬prime i ∣ n) :
    width n / (∏ i, modulus i) * (∏ i, size n true i) ≤ survivors n ∧
      survivors n ≤ (width n / (∏ i, modulus i) + 1) * (∏ i, size n false i) := by
  classical
  have both := FiniteWheelPrecision.sandwich modulus positive cop (rows n true) (rows n false)
    (start n) (width n) (fun k => AllPowers n (start n+k.val))
  have keep (k : Fin (width n))
      (h : ∀ i, ((start n+k.val : ℕ) : ZMod (modulus i)) ∈ rows n true i) :
      AllPowers n (start n+k.val) := by
    refine ⟨(Finset.mem_filter.mp (h none)).2,?_⟩
    intro i e
    letI : Fact (prime i).Prime := ⟨(primes i).1⟩
    obtain ⟨pass,extra⟩ := (Finset.mem_filter.mp (h (some i))).2
    exact StableDiscriminantClasses.permanent (primes i).2 15 pass (extra.resolve_left (by decide)) e
  have necessary (k : Fin (width n)) (h : AllPowers n (start n+k.val)) :
      ∀ i, ((start n+k.val : ℕ) : ZMod (modulus i)) ∈ rows n false i := by
    rintro (_|i)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2 i 16,Or.inl rfl⟩
  simpa only [sizes odd unit] using both keep necessary

/-- Bounds in basis points relative to the number passing the seven
prime-square tests and the same modulo-four test on the identical window. -/
def Relative (n lower upper : ℕ) : Prop :=
  lower * tests n PublicPrimeSquareCounts.modulus ≤ 10000*survivors n ∧
    10000*survivors n ≤ upper * tests n PublicPrimeSquareCounts.modulus

private theorem certify {n lo hi a b c : ℕ} (odd : ¬2∣n) (unit : ∀ i, ¬prime i∣n)
    (widths : lo≤width n ∧ width n≤hi) (base : count n PublicPrimeSquareCounts.modulus=c)
    (numbers : a*((hi/PublicPrimeSquareCounts.modulus+1)*c) ≤
        10000*(lo/(∏ i,modulus i)*(∏ i,size n true i)) ∧
      10000*((hi/(∏ i,modulus i)+1)*(∏ i,size n false i)) ≤
        b*(lo/PublicPrimeSquareCounts.modulus*c)) : Relative n a b := by
  have old := period_bounds n PublicPrimeSquareCounts.modulus (by decide)
  rw [base] at old
  have new := bounds odd unit
  have increase (m : ℕ) : lo/m ≤ width n/m ∧ width n/m ≤ hi/m :=
    ⟨Nat.div_le_div_right widths.1,Nat.div_le_div_right widths.2⟩
  exact ⟨(Nat.mul_le_mul_left _ (old.2.trans (Nat.mul_le_mul_right _ (Nat.succ_le_succ
    (increase _).2)))).trans (numbers.1.trans (Nat.mul_le_mul_left _ ((Nat.mul_le_mul_right _
    (increase _).1).trans new.1))),
    (Nat.mul_le_mul_left _ (new.2.trans (Nat.mul_le_mul_right _ (Nat.succ_le_succ
    (increase _).2)))).trans (numbers.2.trans (Nat.mul_le_mul_left _ ((Nat.mul_le_mul_right _
    (increase _).1).trans old.1)))⟩

theorem fresh_bounds : Relative fresh 3124 3126 := by
  refine certify (lo:=2557561*10^300) (hi:=2557562*10^300) (by decide +kernel)
    (by decide +kernel) ?_ PublicPrimeSquareCounts.fresh_period (by decide +kernel)
  exact PublicWheelLookupCosts.width_between (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem crossed_bounds : Relative crossed 2885 2886 := by
  refine certify (lo:=11130366*10^300) (hi:=11130367*10^300) (by decide +kernel)
    (by decide +kernel) ?_ PublicPrimeSquareCounts.crossed_period (by decide +kernel)
  exact PublicWheelLookupCosts.width_between (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PrimeFactors.PublicStableWheelCounts
