import PrimeFactors.DisplacedPrimePartners
import PrimeFactors.SixTraceBudget
import PrimeFactors.SixTraceNewProducts

/-! Compare two search schedules at the same budget on every partner supplied
by the displaced prime-gap theorem. All labels are determined by the product. -/
namespace PrimeFactors.DisplacedTraceSchedules
open Finset Real InteriorBatchPopulation SixTraceBudget

set_option exponentiation.threshold 8192

private theorem first_eq (n : ℕ) : ceilSqrt (24*n)=⌈2*sqrt (6*(n:ℝ))⌉₊ := by
  have same (u : ℕ) : ceilSqrt (24*n)≤u ↔ ⌈2*sqrt (6*(n:ℝ))⌉₊ ≤ u := by
    rw [ceilSqrt_le_iff,Nat.ceil_le]
    have sq := sq_sqrt (by positivity : (0:ℝ)≤6*(n:ℝ))
    constructor
    · intro h
      have h' : 24*(n:ℝ) ≤ (u:ℝ)^2 := by exact_mod_cast h
      exact (sq_le_sq₀ (by positivity) (Nat.cast_nonneg u)).mp (by nlinarith only [h',sq])
    · intro h
      have h' := pow_le_pow_left₀ (by positivity) h 2
      exact_mod_cast (show 24*(n:ℝ) ≤ (u:ℝ)^2 by nlinarith only [h',sq])
  exact le_antisymm ((same _).mpr le_rfl) ((same _).mp le_rfl)

private theorem between {s first : ℕ} {t : ℝ} (t0 : 0≤t) (ceil : first=⌈t⌉₊)
    (low : 4199202 < (s:ℝ)-t) (high : (s:ℝ)-t ≤ 6230450) :
    first+(1-first%2)+2*2^21 ≤ s ∧ first ≤ s ∧ unitCount s < unitCount first+2^21 := by
  have le : t ≤ first := ceil ▸ Nat.le_ceil _
  have lt : (first:ℝ) < t+1 := ceil ▸ Nat.ceil_lt_add_one t0
  have l : first+4199201 ≤ s := by
    exact_mod_cast (show (first:ℝ)+4199201≤s by linarith only [low,lt])
  have h : s ≤ first+6230450 := by
    exact_mod_cast (show (s:ℝ)≤first+6230450 by linarith only [high,le])
  unfold unitCount
  split_ifs <;> omega

/-- For each smaller prime in the specified range, a partner makes skipping
multiples of three strictly win a fixed budget of 2,097,152 square tests. -/
theorem partner (gap : PrimeGapMultiplier.PrimeInInterval) {p : ℕ}
    (hp : p∈InteriorBatchPopulation.interior) :
    ∃ q∈neighbors p, q.Prime ∧ p<q ∧ q<U ∧ bin p q ∧
      (unitHit (p*q) (ceilSqrt (24*(p*q))) (2^21) ∧
      ¬oddHit (p*q) (ceilSqrt (24*(p*q))) (2^21)) := by
  obtain ⟨q,hq,qp,_,_,lo,hi⟩ := DisplacedPrimePartners.partner gap hp
  obtain ⟨bn,pl,pq,qu,_,_⟩ := interior_split hp hq
  have pp : p.Prime := (mem_filter.mp (by simpa only [InteriorBatchPopulation.interior,firstPrimes] using hp)).2
  have cop (l : ℕ) (pr : l.Prime) (large : 6<l) : Nat.Coprime 6 l :=
    (pr.coprime_iff_not_dvd.mpr (fun d => (not_le_of_gt large) (Nat.le_of_dvd (by decide) d))).symm
  have unit := (Nat.Coprime.mul_right (cop p pp (by omega)) (cop q qp (by omega))).symm
  obtain ⟨beyond,above,rank⟩ := between (by positivity) (first_eq (p*q)) lo hi
  have width : U=2*2^1023 := by decide +kernel
  exact ⟨q,hq,qp,pq,qu,bn,unit_hit_at_minimum pp qp unit above rank,
    odd_miss_of_endpoint pp qp pq (by omega) beyond⟩

/-- Each different smaller prime supplies a different newly split input. -/
theorem new_products (gap : PrimeGapMultiplier.PrimeInInterval)
    (low : 1415*(firstPrimes 0 (79*(U/128))).card ≤ 2*(79*(U/128)))
    (high : 2*(82*(U/128)) ≤ 1419*(firstPrimes 0 (82*(U/128))).card) :
    2^1009 < (successes unitHit (2^21) \ successes oddHit (2^21)).card :=
  SixTraceNewProducts.many_new_of_endpoints low high (partner gap)

end PrimeFactors.DisplacedTraceSchedules
