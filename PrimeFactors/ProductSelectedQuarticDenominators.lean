import PrimeFactors.ThreeQuarticDenominators
import PrimeFactors.QuarticDenominatorBands

/-! Selecting quartic denominator trials from the public product. -/
namespace PrimeFactors.ProductSelectedQuarticDenominators

open MixedPrefixSample (eligible)
open ComplementaryQuarticProducts (choices)
open ScaledQuarticReadings (run)
open QuarticDenominatorBands (Gates)
open scoped Classical
set_option exponentiation.threshold 4096
attribute [local irreducible] eligible

def denominators (n : ℕ) : List ℕ :=
  [1] ++ (if 9*n<5*2^2048 then [725] else []) ++
    (if 3*n<2*2^2048 then [1517] else [])

def recover (n : ℕ) := run n (denominators n)

theorem mem_denominators {n d : ℕ} : d∈denominators n ↔ Gates n d := by
  by_cases a : 9*n<5*2^2048 <;> by_cases b : 3*n<2*2^2048 <;>
    simp only [denominators,Gates,a,b,ite_true,ite_false] <;> simp [or_assoc]

private theorem subset {n d : ℕ} (mem : d∈denominators n) : d∈([1,725,1517]:List ℕ) := by
  rcases mem_denominators.mp mem with rfl|⟨rfl,_⟩|⟨rfl,_⟩ <;> simp

private theorem bounds {d : ℕ} (hd : d∈([1,725,1517]:List ℕ)) : 0<d ∧ d≤2048 := by
  have three : d=1 ∨ d=725 ∨ d=1517 := by simpa using hd
  rcases three with rfl|rfl|rfl <;> decide

theorem choices_agree {p q : ℕ} (mem : (p,q)∈eligible) :
    (∃ d∈([1,725,1517]:List ℕ),(choices (d^4*(p*q))).Nonempty) ↔
      ∃ d∈denominators (p*q),(choices (d^4*(p*q))).Nonempty := by
  constructor
  · rintro ⟨d,hd,hit⟩
    obtain ⟨t,_,_,ok,yes⟩ := QuarticDenominatorBands.raw_hit mem (bounds hd).1 (bounds hd).2 hit
    exact ⟨t,mem_denominators.mpr ok,yes⟩
  · exact fun ⟨d,hd,hit⟩ => ⟨d,subset hd,hit⟩

/-- Product-only selection agrees on the returned pair and on failure. -/
theorem agrees {p q : ℕ} (mem : (p,q)∈eligible) :
    ThreeQuarticDenominators.recover (p*q)=recover (p*q) := by
  unfold ThreeQuarticDenominators.recover recover
  rw [ScaledQuarticReadings.run_eq mem _ (fun _ hd => (bounds hd).2),
    ScaledQuarticReadings.run_eq mem _ (fun _ hd => (bounds (subset hd)).2)]
  exact if_congr (choices_agree mem) rfl rfl

theorem reference {p q : ℕ} (mem : (p,q)∈eligible) :
    run (p*q) (List.range' 1 2048)=recover (p*q) :=
  (ThreeQuarticDenominators.identical mem).trans (agrees mem)

/-- Exact trial lists in all three public input intervals. -/
theorem intervals (n : ℕ) :
    (9*n<5*2^2048 → denominators n=[1,725,1517]) ∧
    (5*2^2048≤9*n → 3*n<2*2^2048 → denominators n=[1,1517]) ∧
    (2*2^2048≤3*n → denominators n=[1]) := by
  constructor
  · intro low
    have mid : 3*n<2*2^2048 := by omega
    rw [denominators,if_pos low,if_pos mid]
    rfl
  constructor
  · intro low mid
    rw [denominators,if_neg (not_lt.mpr low),if_pos mid]
    rfl
  · intro high
    have low : 5*2^2048≤9*n := by omega
    rw [denominators,if_neg (not_lt.mpr low),if_neg (not_lt.mpr high)]
    rfl

end PrimeFactors.ProductSelectedQuarticDenominators
