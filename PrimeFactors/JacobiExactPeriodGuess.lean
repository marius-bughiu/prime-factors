import PrimeFactors.DivisorSum
import PrimeFactors.FactorSum
import PrimeFactors.JacobiPeriodProbe

/-! Test equality with the least shared period at stride (N−1)/2. The input
is the product and one proposed period. A factor pair derived from the guess
allows the exact period to be recomputed and checked. -/

namespace PrimeFactors.JacobiExactPeriodGuess

open JacobiPeriodCount JacobiPeriodProbe JacobiMomentPeriod

/-- Form the factor-sum guess with one scaled integer square root, then use
the existing quadratic discriminant decoder for the candidate pair. -/
def candidate (n t : ℕ) : ℕ × ℕ :=
  let total := n+1-(n/t).sqrt^2*t
  recoverFromSigma n (n+total+1)

/-- Return the nontrivial sorted pair only when its product and its exact
reduced-predecessor product agree with the two inputs. -/
def recover (n t : ℕ) : Option (ℕ × ℕ) :=
  if t=0 then none else
    let z := candidate n t
    if 1<z.1 ∧ z.1≤z.2 ∧ z.1*z.2=n ∧ residualProduct z.1 z.2=t then some z else none

private theorem at_residual {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q) :
    0<residualProduct p q ∧ candidate (p*q) (residualProduct p q) = (p,q) := by
  let g := (p-1).gcd (q-1)
  let a := (p-1)/g
  let b := (q-1)/g
  have pg := Nat.sub_pos_of_lt pp.one_lt
  have qg := Nat.sub_pos_of_lt qp.one_lt
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ pg
  have ga : g*a=p-1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have gb : g*b=q-1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have ap : 0<a := Nat.div_pos (Nat.le_of_dvd pg (Nat.gcd_dvd_left ..)) gp
  have less : a<b := Nat.lt_of_mul_lt_mul_left (show g*a<g*b by omega)
  have sum := (sum_from_period ap less (by omega : p=g*a+1) (by omega : q=g*b+1)).2
  refine ⟨Nat.mul_pos ap (ap.trans less),?_⟩
  change recoverFromSigma (p*q) (p*q+(p*q+1-(p*q/(a*b)).sqrt^2*(a*b))+1) = (p,q)
  rw [sum,←sigma_semiprime pp qp lt.ne]
  exact recoverFromSigma_correct pp qp lt

/-- For any two distinct primes in increasing order, the computable decoder
returns both factors exactly at the true reduced-predecessor product. -/
theorem recover_eq {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q) (t : ℕ) :
    recover (p*q) t = if t=residualProduct p q then some (p,q) else none := by
  obtain ⟨positive,pair⟩ := at_residual pp qp lt
  by_cases h : t=residualProduct p q
  · subst t
    simp [recover,positive.ne',pair,pp.one_lt,lt.le]
  · rw [if_neg h]
    by_cases zero : t=0
    · simp [recover,zero]
    rw [recover,if_neg zero]
    dsimp only
    split
    · rename_i pass
      obtain ⟨x,y⟩ := ordered_semiprime_pair_unique pp qp lt.le pass.2.1 pass.1 pass.2.2.1
      exact False.elim (h (by simpa only [x,y] using pass.2.2.2.symm))
    · rfl

/-- The boolean readout decides equality with the least positive all-offset
period on inputs where both prime factors are at least seven. -/
theorem accepted_iff_least {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 7≤p) (lt : p<q) (t : ℕ) :
    (recover (p*q) t).isSome = true ↔
      IsLeast {r : ℕ | 0<r ∧ AllOffsets (completeEven (p*q)) ((p*q-1)/2) r} t := by
  have pp : p.Prime := Fact.out
  have qp : q.Prime := Fact.out
  have cop := (Nat.coprime_primes pp qp).mpr lt.ne
  have char := canonical_period cop hp (hp.trans lt.le)
  have pos := (at_residual pp qp lt).1
  have least : IsLeast {r : ℕ | 0<r ∧ AllOffsets (completeEven (p*q)) ((p*q-1)/2) r}
      (residualProduct p q) := by
    refine ⟨⟨pos,(char _).mpr dvd_rfl⟩,?_⟩
    rintro r ⟨rp,works⟩
    exact Nat.le_of_dvd rp ((char r).mp works)
  rw [recover_eq pp qp lt]
  by_cases h : t=residualProduct p q
  · simp [h,least]
  · simp only [if_neg h,Option.isSome_none,Bool.false_eq_true,false_iff]
    exact fun other => h (other.unique least)

/-- At 221 the guesses 3 and 48 both reconstruct the true factor pair before
the final equality check. Only 12 is the least period; 48 is a multiple of it. -/
theorem control_221 :
    recover 221 0 = none ∧
    candidate 221 3 = (13,17) ∧ recover 221 3 = none ∧
    candidate 221 48 = (13,17) ∧ recover 221 48 = none ∧
    recover 221 12 = some (13,17) := by decide +kernel

end PrimeFactors.JacobiExactPeriodGuess
