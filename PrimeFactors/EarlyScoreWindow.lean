import PrimeFactors.ScoreOrderSlowdown

/-! A window of even sums whose scores precede the target regardless of
the two sums' favored statuses. Visiting such a sum still requires the
original residue menu to admit it. -/

namespace PrimeFactors.EarlyScoreWindow

open PeriodicSumRank
set_option exponentiation.threshold 4096

private theorem score_bounds (n s : ℕ) :
    4*(s^2-4*n)≤ScoreSumOrder.key n s ∧ ScoreSumOrder.key n s≤25*(s^2-4*n) := by
  unfold ScoreSumOrder.key
  split_ifs <;> omega

/-- The worst ordering places the smaller sum in the weight-25 group and
the larger sum in the weight-4 group. Rounding at the lower endpoint costs
at most one unit in the sufficient margin. -/
theorem before_of_margin {n t S : ℕ} (np : 0<n) (lower : ceilSqrt (4*n)≤t)
    (margin : 25*(t-ceilSqrt (4*n)+1)≤4*(S-ceilSqrt (4*n))) :
    t<S ∧ ScoreSumOrder.key n t<ScoreSumOrder.key n S := by
  have lt : t<S := by omega
  refine ⟨lt,lt_of_not_ge (fun bad => ?_)⟩
  have limit := (score_bounds n S).1.trans (bad.trans (score_bounds n t).2)
  have distance := ScoreOrderSlowdown.promoted_distance np lower lt limit
  omega

/-- The even sum associated to the midpoint sqrt(n) rounded down, plus
one and a nonnegative offset. -/
def candidate (n j : ℕ) := 2*(n.sqrt+1+j)

private theorem lower_bracket (n : ℕ) :
    2*n.sqrt≤ceilSqrt (4*n) ∧ ceilSqrt (4*n)≤2*(n.sqrt+1) := by
  have cap : 4*n≤(ceilSqrt (4*n))^2 := ceilSqrt_le_iff.mp le_rfl
  constructor
  · apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    nlinarith only [Nat.sqrt_le' n,cap]
  · apply ceilSqrt_le_iff.mpr
    nlinarith only [Nat.lt_succ_sqrt n]

/-- All 2^896 offsets are before a target at least 2^900 above its lower
endpoint, including offset zero. This statement concerns the ordering
before any residue conditions are imposed. -/
theorem early {n S j : ℕ} (np : 0<n) (long : ceilSqrt (4*n)+2^900≤S) (jlt : j<2^896) :
    ceilSqrt (4*n)≤candidate n j ∧ candidate n j<S ∧ ScoreSumOrder.before n (candidate n j) S := by
  obtain ⟨lo,hi⟩ := lower_bracket n
  have reach : ceilSqrt (4*n)≤candidate n j ∧ candidate n j≤ceilSqrt (4*n)+2*j+2 := by
    unfold candidate
    omega
  have budget : 25*(2*(2^896)+1)≤4*2^900 := by decide +kernel
  have condition : 25*(candidate n j-ceilSqrt (4*n)+1)≤4*(S-ceilSqrt (4*n)) := by omega
  obtain ⟨lt,key⟩ := before_of_margin np reach.1 condition
  exact ⟨reach.1,lt,Or.inl key⟩

/-- An admitted early-window sum belongs to the actual score prefix. -/
theorem mem_prefix {n S j hi : ℕ} (np : 0<n) (long : ceilSqrt (4*n)+2^900≤S) (jlt : j<2^896)
    (upper : S≤hi) (pass : passes (n%100) (candidate n j%100)=true) :
    candidate n j∈ScoreSumOrder.«prefix» n (ceilSqrt (4*n)) hi S := by
  obtain ⟨lower,lt,before⟩ := early np long jlt
  exact ScoreSumOrder.mem_prefix.mpr ⟨⟨lower,lt.le.trans upper⟩,pass,before⟩

end PrimeFactors.EarlyScoreWindow
