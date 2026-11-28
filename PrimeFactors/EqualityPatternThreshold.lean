import PrimeFactors.EqualityPatternSampling
import PrimeFactors.SphereCircleIdentity

/-! For two possible sizes with equal priors, the optimal anonymous comparison
is a threshold on the number of distinct labels. Unit-target circles on a
single product have exactly the same anonymous observation law. -/
namespace PrimeFactors.EqualityPatternThreshold

open Finset EqualityPatternSampling SphereCircleIdentity
open scoped Classical

/-- After clearing denominators, this is the likelihood comparison for a
specified equality pattern using k distinct labels in t draws. Ties favor M. -/
def chooseLarger (m M t k : ℕ) : Prop :=
  m.descFactorial k * M^t ≤ M.descFactorial k * m^t

theorem threshold {m M t k j : ℕ} (sizes : m≤M) (more : k≤j)
    (h : chooseLarger m M t k) : chooseLarger m M t j := by
  induction j, more using Nat.le_induction with
  | base => exact h
  | succ j _ ih =>
    unfold chooseLarger at *
    rw [Nat.descFactorial_succ,Nat.descFactorial_succ,mul_assoc,mul_assoc]
    exact Nat.mul_le_mul (Nat.sub_le_sub_right sizes j) ih

/-- This choice maximizes the contribution of each individual transcript to
the equal-prior correct-decision probability, even against randomized tests. -/
theorem optimum (m M t k : ℕ) (u : ℝ) (lo : 0≤u) (hi : u≤1) :
    let a : ℝ := m.descFactorial k * M^t
    let b : ℝ := M.descFactorial k * m^t
    (1-u)*a+u*b ≤ if chooseLarger m M t k then b else a := by
  classical
  dsimp only
  split_ifs with h
  · have w : (m.descFactorial k:ℝ)*(M:ℝ)^t≤(M.descFactorial k:ℝ)*(m:ℝ)^t := by
      exact_mod_cast (show _ ≤ _ from h)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hi) (sub_nonneg.mpr w)]
  · have w : (M.descFactorial k:ℝ)*(m:ℝ)^t≤(m.descFactorial k:ℝ)*(M:ℝ)^t := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge h))
    nlinarith only [mul_nonneg lo (sub_nonneg.mpr w)]

/-- Equal cardinalities imply identical expectations for every equality-only
test, for any number of draws. Here the two populations belong to the same N. -/
theorem blind_to_target {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a b : ZMod (p*q)} (ua : IsUnit a)
    (ub : IsUnit b) (t : ℕ) (f : List ℕ→ℝ) :
    expect (circle (ZMod (p*q)) a).card t 0 f=expect (circle (ZMod (p*q)) b).card t 0 f := by
  have eqn : (circle (ZMod (p*q)) a).card=(circle (ZMod (p*q)) b).card := by
    exact_mod_cast (semiprime diff op oq ua).trans (semiprime diff op oq ub).symm
  rw [eqn]

end PrimeFactors.EqualityPatternThreshold
