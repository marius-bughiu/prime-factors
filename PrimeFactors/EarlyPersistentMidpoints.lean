import PrimeFactors.PersistentLocalSurvivors

/-! Simultaneous local square tests in a short interval of consecutive midpoints.
The count is independent of the starting midpoint and the chosen prime-power depths. -/
namespace PrimeFactors.EarlyPersistentMidpoints

open PersistentLocalSurvivors

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

/-- An integer midpoint passes every precision for all primes through 643. -/
def Passes (N h : ℕ) : Prop := ∀ p ∈ smallPrimes 643, ∀ e : ℕ,
  IsSquare (((h : ℤ)^2-N : ℤ) : ZMod (p^e))

/-- Distinct offsets in the supplied consecutive interval which pass simultaneously. -/
abbrev survivors (start N : ℕ) := {k : Fin (2^896) // Passes N (start+k.val)}

theorem prime_count : (smallPrimes 643).card=117 := by decide +kernel

private theorem period_value : period 643 =
    404216391396774320311642097145459323179982829832174595950210082154780698087980056818082664546229860469132355556386269147242590906715763229865642486115226815653739722940733188030270895876623616209968664048779282599222295217449562280801775535338683362615341176830533895040 := by decide +kernel

private theorem lanes_value : minPerPeriod 643 =
    247991752716332969553835928378701198771368899782405806030356785362867756808748505738966691962598430937272317590273003987256578778629360793750078997561887190165944171276215324295826515659617950760960000000000000000000000000000000000 := by decide +kernel

theorem period_bounds : 2^895≤period 643 ∧ period 643<2^896 := by rw [period_value]; decide +kernel

theorem complete_periods : 2^896/period 643=1 := by rw [period_value]; decide +kernel

theorem lane_bounds : 2^765+1<minPerPeriod 643 ∧ minPerPeriod 643<2^766 := by rw [lanes_value]; decide +kernel

private theorem one_period {a n k b : ℕ} (q : a=1) (lanes : b+1<n) (floor : a*n≤k) : b<k := by
  rw [q,one_mul] at floor
  omega

attribute [local irreducible] minPerPeriod period smallPrimes

/-- The guaranteed complete period alone supplies more than the stated number
of offsets. No average over products or starting points enters the estimate. -/
theorem count (start N : ℕ) (unit : ∀ p ∈ smallPrimes 643, ¬p∣N) :
    2^765<Nat.card (survivors start N) :=
  one_period complete_periods lane_bounds.1 (persistent_interval 643 start (2^896) N unit)

/-- Injectivity of the doubled midpoint turns the offset bound into a lower
bound on any finite set containing the indicated sums. -/
theorem tally {start N : ℕ} (unit : ∀ p ∈ smallPrimes 643, ¬p∣N) (S : Finset ℕ)
    (keep : ∀ k : Fin (2^896), Passes N (start+k.val) → 2*(start+k.val)∈S) :
    2^765<S.card := by
  let f (k : survivors start N) : S := ⟨2*(start+k.val.val),keep k.val k.property⟩
  have inject : Function.Injective f := by
    intro x y eq
    have same : 2*(start+x.val.val)=2*(start+y.val.val) := congrArg Subtype.val eq
    exact Subtype.ext (Fin.ext (by omega))
  have card := Nat.card_le_card_of_injective f inject
  exact (count start N unit).trans_le (by simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using card)

end PrimeFactors.EarlyPersistentMidpoints
