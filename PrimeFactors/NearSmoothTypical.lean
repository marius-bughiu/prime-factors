import PrimeFactors.NearSmoothSumPopulation
import PrimeFactors.NearSmoothSumWindows

/-! Compare the unclipped exceptional band in the population count with the
clipped, parity-aware endpoints actually used by the seven-row equation. -/

namespace PrimeFactors.NearSmoothTypical

open NearSmoothSumPopulation NearSmoothSumWindows

/-- Feasibility after clipping implies feasibility at the raw upper midpoint.
Failure of the raw lower gap test is thus necessary for a feasible clipped
band to fail the corresponding lower gap test. -/
theorem gap_of_regular {n b t g : ℕ} (regular : ¬IllConditioned n b t g)
    (order : leftHalf n (sumLo b (2*t))≤sumHi b (2*t)/2) :
    g^2 ≤ (leftHalf n (sumLo b (2*t)))^2-n := by
  have nA : n≤(leftHalf n (sumLo b (2*t)))^2 := ceilSqrt_le_iff.mp (le_max_right ..)
  have hi : sumHi b (2*t)/2≤midpoint b+t := by unfold sumHi midpoint; omega
  have reaches := nA.trans (Nat.pow_le_pow_left (order.trans hi) 2)
  have raw : n+g^2≤(midpoint b-t)^2 := by
    by_contra! lost
    exact regular ⟨reaches,lost⟩
  have left : midpoint b-t≤(sumLo b (2*t)+1)/2 := by unfold midpoint sumLo; omega
  have move := Nat.pow_le_pow_left (left.trans (le_max_left _ (ceilSqrt n))) 2
  change g^2≤(max ((sumLo b (2*t)+1)/2) (ceilSqrt n))^2-n
  omega

/-- A center kept for the full-size 2^400 absolute error promise is covered
by one seven-row equation unless it meets the population exception predicate. -/
theorem fit_of_regular {n b : ℕ} (member : b∈active n (2^400))
    (regular : ¬IllConditioned n b (2^399) (2^983)) :
    upper n (sumHi b (2^400))-lower n (sumLo b (2^400))≤4*radius := by
  have order := (Finset.mem_filter.mp member).2.1
  apply tolerances _ _ _ order
  left
  refine ⟨le_rfl,?_⟩
  have power : 2*(2:ℕ)^399=2^400 := by decide +kernel
  apply (power ▸ gap_of_regular regular (by rw [power]; exact order))

/-- Starting from a population of ordered representatives of eligible prime
pairs, remove precisely the pairs for which at least one surviving center is
too wide. Their count is strictly below pop/2^55 under the supplied analytic
prime-count estimate. Every other input has a polynomial root set covering the
entire near-sum family. The theorem makes no lower bound on the number of
factor pairs that actually satisfy the near-sum promise. -/
theorem typical_sweep {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {pop : ℕ}
    (den : 2^1023*first.card<44331*pop)
    (input : ∀ z∈pairs, z.1∈first ∧ z.1.Prime ∧ z.2.Prime ∧ 2^1023≤z.1 ∧
      z.1≤z.2 ∧ 2^2047≤z.1*z.2) :
    ∃ bad⊆pairs, 2^55*bad.card<pop ∧ ∀ z∈pairs, z∉bad →
      Covers (z.1*z.2) (2^400) (6*(active (z.1*z.2) (2^400)).card) := by
  classical
  let fails (n : ℕ) : Prop := ∃ b∈active n (2^400),
    4*radius < upper n (sumHi b (2^400))-lower n (sumLo b (2^400))
  let bad := pairs.filter fun z => fails (z.1*z.2)
  refine ⟨bad,Finset.filter_subset ..,exception_fraction den ?_,?_⟩
  · intro z hz
    obtain ⟨inPop,b,activeB,fail⟩ := Finset.mem_filter.mp hz
    obtain ⟨fst,_,_,lo,_,_⟩ := input z inPop
    have inMenu := (Finset.mem_filter.mp activeB).1
    have bound := Finset.mem_range.mp (Finset.mem_filter.mp inMenu).1
    refine ⟨fst,lo,b,bound,?_⟩
    by_contra regular
    exact (not_le_of_gt fail) (fit_of_regular activeB regular)
  · intro z hz good
    obtain ⟨_,pp,qp,lo,order,large⟩ := input z hz
    have fit (b : ℕ) (hb : b∈active (z.1*z.2) (2^400)) :
        upper (z.1*z.2) (sumHi b (2^400))-lower (z.1*z.2) (sumLo b (2^400))≤4*radius := by
      by_contra! tooWide
      exact good (Finset.mem_filter.mpr ⟨hz,b,hb,tooWide⟩)
    have primeCop {p : ℕ} (hp : p.Prime) (cap : 45360<p) : p.Coprime 45360 := by
      apply hp.coprime_iff_not_dvd.mpr
      intro h
      exact (not_le_of_gt cap) (Nat.le_of_dvd (by decide : 0<45360) h)
    have cop := Nat.coprime_mul_iff_left.mpr ⟨primeCop pp (by omega),primeCop qp (by omega)⟩
    have odd := (pp.odd_of_ne_two (by omega)).mul (qp.odd_of_ne_two (by omega))
    exact sweep large cop odd fit

end PrimeFactors.NearSmoothTypical
