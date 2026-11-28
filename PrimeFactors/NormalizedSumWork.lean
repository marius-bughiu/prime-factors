import PrimeFactors.GlobalSumOrderCost
import PrimeFactors.FavoredSumWork

/-! Normalizing the actual square-test counts of the two traversals by the
common width B=2^1024. The seven-per-block ascending bound applies to the
square-unit product classes modulo five. -/

namespace PrimeFactors.NormalizedSumWork

open Real GlobalSumOrderCost FactorSumPrefixCost PeriodicSumRank FullRangeResidueEstimates
open WideResiduePrimeSupply (B)
open MixedPrefixSample (eligible)
open private PrimeFactors.FullPopulationFavoredSums.mem_eligible from PrimeFactors.FullPopulationFavoredSums
open private PrimeFactors.FavoredSumWork.marks_same PrimeFactors.FavoredSumWork.favored_mod5
  from PrimeFactors.FavoredSumWork
open private PrimeFactors.ProductDeficitBand.left_cap from PrimeFactors.ProductDeficitBand

set_option exponentiation.threshold 4096
attribute [local irreducible] eligible

noncomputable def coord (p : ℕ) : ℝ := (p:ℝ)/(B:ℝ)

/-- Difference in actual square tests through the successful target, including
the cost of all later favored candidates when the true sum is ordinary. -/
noncomputable def saved (p q : ℕ) : ℝ :=
  (saving (p*q) (ceilSqrt (4*(p*q))) (ProductDeficitBand.sumCap (p*q) X) (p+q):ℤ)

/-- Number of square tests in ascending order, including the successful test. -/
noncomputable def ascending (p q : ℕ) : ℝ :=
  ((passingPrefix (p*q) (ceilSqrt (4*(p*q))) (p+q)).card:ℕ)

/-- Actual square tests in the ordering that visits all favored residues first. -/
noncomputable def prioritized (p q : ℕ) : ℝ :=
  ((globalPrefix (p*q) (ceilSqrt (4*(p*q))) (ProductDeficitBand.sumCap (p*q) X) (p+q)).card:ℕ)

theorem saved_eq (p q : ℕ) : saved p q=ascending p q-prioritized p q := by
  simp only [saved,ascending,prioritized,saving,Int.cast_sub,Int.cast_natCast]

private theorem before_identity (p q : ℕ) :
    (B:ℝ)*(sqrt (coord q)-sqrt (coord p))^2 =
      (p:ℝ)+q-2*sqrt (p*q:ℕ) := by
  have hb : (0:ℝ)<B := by norm_num [B]
  calc
    _ = (sqrt (q:ℝ)-sqrt (p:ℝ))^2 := by
      rw [coord,coord,sqrt_div (Nat.cast_nonneg q),sqrt_div (Nat.cast_nonneg p),
        ←sub_div,div_pow,sq_sqrt hb.le]
      field_simp [hb.ne']
    _ = _ := by
      rw [Nat.cast_mul,sqrt_mul (Nat.cast_nonneg p)]
      nlinarith only [sq_sqrt (Nat.cast_nonneg p : (0:ℝ)≤p),sq_sqrt (Nat.cast_nonneg q : (0:ℝ)≤q)]

private theorem floor_endpoint (n : ℕ) : 2*sqrt n ≤ (ceilSqrt (4*n):ℝ) := by
  have hi : 4*(n:ℝ) ≤ (ceilSqrt (4*n):ℝ)^2 := by exact_mod_cast (ceilSqrt_le_iff.mp le_rfl : 4*n≤(ceilSqrt (4*n))^2)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,sq_sqrt (Nat.cast_nonneg n)]
  norm_num only [Nat.reducePow] at *
  linarith only [hi]

private theorem target_low (p q : ℕ) : ceilSqrt (4*(p*q))≤p+q := by
  apply ceilSqrt_le_iff.mpr
  zify
  nlinarith only [sq_nonneg ((p:ℤ)-q)]

private theorem target_high {p q : ℕ} (pl : X≤p) (order : p<q) (qh : q<B) :
    p+q≤ProductDeficitBand.sumCap (p*q) X := by
  have top : q<2*X := (by decide : B=2*X) ▸ qh
  exact le_min (PrimeFactors.ProductDeficitBand.left_cap (by decide : 0<X) pl (pl.trans order.le))
    (CenteredSumQuartic.sum_upper rfl (by decide : 0<2*X-1) (by omega) (by omega))

private theorem after_bound {p q : ℕ} (pl : X≤p) (order : p<q) (qh : q<B) :
    ((ProductDeficitBand.sumCap (p*q) X-(p+q):ℕ):ℝ) ≤
      (B:ℝ)*((1-coord p)*(1-coord q)) := by
  have top : q<2*X := (by decide : B=2*X) ▸ qh
  have size : p*q≤(2*X-1)^2 := by
    rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
  have hi := hi_upper (by decide : 0<X) size
  have eq : 2*(X:ℝ)=(B:ℝ) := by exact_mod_cast (by decide : 2*X=B)
  rw [eq,Nat.cast_mul] at hi
  have formula : (B:ℝ)*((1-coord p)*(1-coord q)) = (B:ℝ)+(p:ℝ)*q/B-(p+q) := by
    unfold coord
    field_simp [show (B:ℝ)≠0 by norm_num [B]]
    ring
  rw [Nat.cast_sub (target_high pl order qh),Nat.cast_add,formula]
  exact sub_le_sub_right hi _

private theorem prime_nonzero {p : ℕ} (pl : X≤p) (pp : p.Prime) : p%5≠0 := by
  intro zero
  have eq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) pp).mp (Nat.dvd_of_mod_eq_zero zero)
  exact ((by decide : 5<X).trans_le pl).ne eq

private theorem marks_opposite {p q : ℕ} (unit : p%5≠0) (opp : (p%5+q%5)%5=0) :
    ((p*q)%5=1 ∨ (p*q)%5=4) ∧ favored ((p*q)%100) ((p+q)%100)=false := by
  have table : ∀ a b : Fin 5, a.val≠0 → (a.val+b.val)%5=0 →
      ((a.val*b.val)%5=1 ∨ (a.val*b.val)%5=4) ∧
      (((a.val+b.val)%5)*((a.val+b.val)%5))%5≠(4*((a.val*b.val)%5))%5 := by decide
  have pair := table ⟨p%5,Nat.mod_lt _ (by decide)⟩ ⟨q%5,Nat.mod_lt _ (by decide)⟩ unit opp
  refine ⟨by simpa only [Nat.mul_mod p q] using pair.1,?_⟩
  apply Bool.eq_false_iff.mpr
  intro good
  rw [PrimeFactors.FavoredSumWork.favored_mod5,Nat.mul_mod p q,Nat.add_mod p q] at good
  exact pair.2 good

/-- All square unit products obey the ascending bound in both target groups. -/
theorem ascending_bound {p q : ℕ} (sq : (p*q)%5=1 ∨ (p*q)%5=4) :
    100*ascending p q ≤ 7*(B:ℝ)*(sqrt (coord q)-sqrt (coord p))^2+700 := by
  let s := p+q
  let lo := ceilSqrt (4*(p*q))
  have le : lo≤s := target_low p q
  have work : 100*ascending p q≤7*((s-lo:ℕ):ℝ)+700 := by
    unfold ascending
    exact_mod_cast ascending_upper sq le
  rw [Nat.cast_sub le] at work
  have rad := floor_endpoint (p*q)
  rw [mul_assoc,(before_identity p q)]
  change _ ≤ 7*((p:ℝ)+q-2*sqrt (p*q:ℕ))+700
  have sum : (s:ℝ)=(p:ℝ)+q := Nat.cast_add ..
  rw [sum] at work
  exact work.trans (add_le_add_right (mul_le_mul_of_nonneg_left (sub_le_sub_left rad _) (by norm_num)) _)

/-- Same nonzero remainder puts the true sum in the favored group. -/
theorem favored_bound {p q : ℕ} (h : (p,q)∈eligible) (same : p%5=q%5) :
    0≤saved p q ∧ 5*(B:ℝ)*(sqrt (coord q)-sqrt (coord p))^2-505 ≤ 100*saved p q ∧
      100*ascending p q ≤ 7*(B:ℝ)*(sqrt (coord q)-sqrt (coord p))^2+700 := by
  obtain ⟨pl,_,_,pp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp h
  obtain ⟨sq,mark⟩ := PrimeFactors.FavoredSumWork.marks_same (prime_nonzero pl pp) same
  let s := p+q
  let lo := ceilSqrt (4*(p*q))
  let hi := ProductDeficitBand.sumCap (p*q) X
  have positive : (0:ℤ)≤saving (p*q) lo hi s := by rw [favored_exact mark]; positivity
  have le : lo≤s := target_low p q
  have work : 5*((s-lo:ℕ):ℝ)-500≤100*saved p q := by
    unfold saved
    exact_mod_cast favored_lower (hi:=hi) sq le mark
  rw [Nat.cast_sub le] at work
  have rad := lo_upper (p*q)
  have sum : (s:ℝ)=(p:ℝ)+q := Nat.cast_add ..
  rw [sum] at work
  refine ⟨by unfold saved; exact_mod_cast positive,?_,ascending_bound sq⟩
  rw [mul_assoc,before_identity]
  have round {w a b t : ℝ} (endpoint : a≤b+1) (work : 5*(t-a)-500≤w) :
      5*(t-b)-505≤w := by linarith
  exact round rad work

/-- Opposite nonzero remainders put the true sum in the ordinary group. -/
theorem ordinary_bound {p q : ℕ} (h : (p,q)∈eligible) (opp : (p%5+q%5)%5=0) :
    -2*(B:ℝ)*((1-coord p)*(1-coord q))-200 ≤ 100*saved p q ∧
      100*ascending p q ≤ 7*(B:ℝ)*(sqrt (coord q)-sqrt (coord p))^2+700 := by
  obtain ⟨pl,order,qu,pp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp h
  obtain ⟨sq,mark⟩ := marks_opposite (prime_nonzero pl pp) opp
  let hi := ProductDeficitBand.sumCap (p*q) X
  let s := p+q
  have work : -(2*((hi-s:ℕ):ℝ))-200≤100*saved p q := by
    unfold saved
    exact_mod_cast ordinary_lower (lo:=ceilSqrt (4*(p*q))) sq (target_high pl order qu) mark
  refine ⟨?_,ascending_bound sq⟩
  rw [mul_assoc]
  have combine {v w r : ℝ} (cap : v≤w) (old : -(2*v)-200≤r) : -2*w-200≤r := by linarith
  exact combine (after_bound pl order qu) work

end PrimeFactors.NormalizedSumWork
