import PrimeFactors.QuotientStripScheduleCost
import Mathlib.Tactic

namespace PrimeFactors.QuotientStripTailIndices

set_option exponentiation.threshold 4096

/-- Inclusive final endpoint of each full block equals the next start minus one. -/
def start (L W j : ℤ) := L+j*W
def stop (L W j : ℤ) := L+(j+1)*W-1

theorem full_indices {L W T H : ℤ} (wpos : 0 < W) (room : L ≤ T-H) (wide : 3*W ≤ H) :
    ∃ i j : ℤ, 0 ≤ i ∧ i ≤ j ∧
      T-H ≤ start L W i ∧ start L W i < T-H+W ∧
      T-W < stop L W j ∧ stop L W j ≤ T := by
  let i := -((L-(T-H))/W)
  let j := (T+1-L)/W-1
  have eqI : start L W i = T-H+(L-(T-H))%W := by
    have h := Int.emod_add_ediv (L-(T-H)) W
    dsimp only [start,i]
    nlinarith only [h]
  have eqJ : stop L W j = T-(T+1-L)%W := by
    have h := Int.emod_add_ediv (T+1-L) W
    dsimp only [stop,j]
    nlinarith only [h]
  have ip : 0 ≤ i := by
    dsimp only [i]
    have prod := Int.ediv_mul_le (L-(T-H)) (ne_of_gt wpos)
    by_contra! h
    have wrong := mul_pos (neg_neg_iff_pos.mp h) wpos
    omega
  have ri := Int.emod_nonneg (L-(T-H)) (ne_of_gt wpos)
  have riw := Int.emod_lt_of_pos (L-(T-H)) wpos
  have rj := Int.emod_nonneg (T+1-L) (ne_of_gt wpos)
  have rjw := Int.emod_lt_of_pos (T+1-L) wpos
  have ij : i ≤ j := by
    by_contra! h
    have hi := mul_le_mul_of_nonneg_right (show j+1 ≤ i by omega) wpos.le
    dsimp only [start,stop] at eqI eqJ
    omega
  exact ⟨i,j,ip,ij,by omega,by omega,by omega,by omega⟩

/-- The public band begins before the full-size near-square-root subinterval. -/
theorem band_begins_before {n : ℕ} (tbig : 11*2^1020  ≤  n.sqrt) :
    (PrimeFactors.QuotientStripScheduleCost.first n : ℤ)  ≤  (n.sqrt : ℤ)-2^679 := by
  let a := ((n-1)/2).sqrt
  have a2 := Nat.sqrt_le' ((n-1)/2)
  change a^2 ≤ _ at a2
  have t2 := Nat.lt_succ_sqrt' n
  have ht : 4*a  ≤  3*(n.sqrt+1) := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    have half : 2*((n-1)/2) ≤ n := by omega
    nlinarith only [a2,t2,half,Nat.zero_le n.sqrt]
  change ((a+1 : ℕ) : ℤ)  ≤  _
  omega

end PrimeFactors.QuotientStripTailIndices
