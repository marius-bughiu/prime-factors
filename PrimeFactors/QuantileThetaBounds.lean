import PrimeFactors.QuantilePopulationBounds
import PrimeFactors.SquareRootPhasePopulation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Complex.ExponentialBounds

/-! Finite arithmetic for the unconditional central-sum population estimate.
Axler, Proposition 1.1 and (1.6), https://arxiv.org/pdf/2203.05917, bounds
`|θ(x)-x|`. Partial summation, replacing the prime-count measures, integration
of the three slab masses and the phase discrepancy are analytic hypotheses.
The error propagation, constants and majority after conditioning are proved here. -/
namespace PrimeFactors.QuantileThetaBounds

/-- The logarithm and normalized eligible area satisfy the bounds used
in the analytic estimate throughout the target input band. -/
theorem target_band : 709<Real.log ((2:ℝ)^1023) ∧ Real.log ((2:ℝ)^1024)<710 ∧
    306/1000<1-Real.log 2 ∧ (1-Real.log 2)/4<775/10000 := by
  rw [Real.log_pow,Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  exact ⟨by linarith only [Real.log_two_gt_d9],by linarith only [Real.log_two_lt_d9],
    by linarith only [Real.log_two_lt_d9],by linarith only [Real.log_two_gt_d9]⟩

/-- Two endpoint errors and an integrated error, with two extra units
allowed for arbitrary open/closed interval endpoints. -/
theorem theta_discrepancy {X ε : ℝ} (size : 10^20≤X)
    (summation : ε≤(24334/10^6)*(4*X/709^4+X/709^5)+2) : ε<(385338/10^18)*X := by
  linarith only [size,summation]

/-- Replace each of the two prime-count measures with its smooth measure.
Here V is the one-dimensional smooth mass and D the sorted eligible mass. -/
theorem theta_error {X V ε E D : ℝ} (x0 : 0<X) (v0 : 0≤V) (e0 : 0≤ε)
    (discrep : ε≤(385338/10^18)*X) (mass : V≤X/709)
    (total : (306/1000)*X^2/710^2≤D) (region : E≤ε*(2*V+ε)) : E/D<179070/10^14 := by
  have pos : 0<D := lt_of_lt_of_le (by positivity) total
  apply (div_lt_iff₀ pos).mpr
  calc E ≤ _ := region
       _ ≤ ((385338/10^18)*X)*(2*(X/709)+(385338/10^18)*X) :=
         mul_le_mul discrep (by linarith only [mass,discrep]) (by linarith only [v0,e0]) (by positivity)
       _ < (179070/10^14)*((306/1000)*X^2/710^2) := by nlinarith only [sq_pos_of_pos x0]
       _ ≤ _ := mul_le_mul_of_nonneg_left total (by norm_num)

/-- Lower endpoints for the logarithmic gap height H=log(1/n)/2 on the
three successive product bins ending at n=9/16, 10/16 and 11/16. -/
theorem slab_heights : 28/100 ≤ Real.log (16/9)/2 ∧ 23/100 ≤ Real.log (16/10)/2 ∧
    18/100 ≤ Real.log (16/11)/2 := by
  have a := Real.le_log_one_add_of_nonneg (x:=7/9) (by norm_num)
  have b := Real.le_log_one_add_of_nonneg (x:=6/10) (by norm_num)
  have c := Real.le_log_one_add_of_nonneg (x:=5/11) (by norm_num)
  norm_num at a b c ⊢
  exact ⟨by linarith only [a],by linarith only [b],by linarith only [c]⟩

/-- With z=λ², the smooth fiber's analytic upper tilt is below 2.98315e-8. -/
theorem upper_fiber {z : ℝ} (small : z≤1/2047^2) : z/(8*(1-z)^2)<298315/10^13 := by
  have near : 0<1-z := by linarith
  have sq : (1-(1/2047^2:ℝ))^2 ≤ (1-z)^2 := by gcongr
  apply (div_lt_iff₀ (by positivity)).mpr
  calc z ≤ _ := small
       _ < (298315/10^13)*(8*(1-1/2047^2)^2) := by norm_num
       _ ≤ _ := by gcongr

noncomputable def height : Fin 3 → ℝ := ![28/100,23/100,18/100]

/-- Lower relative smooth mass from a bin of width 1/16, height at least h,
area at most 0.0775 for the whole region and density ratio (709/710)². -/
noncomputable def weightFloor (h : ℝ) := (h/16)*(709/710)^2/(775/10000)

/-- Lower smooth tilt on a slab from λ≥h/710 and λ≤1/2047. -/
noncomputable def tiltFloor (h : ℝ) := (1-1/2047^2)*(h/710)^2/8

/-- The normalized smooth mass lower bound follows by dividing the slab
area/density lower bound by the upper bound on total mass. -/
theorem slab_weight {h B M D : ℝ} (height0 : 0≤h) (pos : 0<D)
    (slab : h*B^2/(16*710^2)≤M) (whole : D≤(775/10000)*B^2/709^2) : weightFloor h≤M/D := by
  apply (le_div_iff₀ pos).mpr
  calc weightFloor h*D ≤ weightFloor h*((775/10000)*B^2/709^2) :=
         mul_le_mul_of_nonneg_left whole (by unfold weightFloor; positivity)
       _ = h*B^2/(16*710^2) := by unfold weightFloor; ring
       _ ≤ M := slab

/-- The analytic lower tilt on one fiber implies the advertised floor
uniformly throughout its slab. -/
theorem slab_fiber {h l T : ℝ} (height0 : 0≤h) (lo : h/710≤l) (hi : l≤1/2047)
    (lower : (1-l^2)*l^2/8≤T) : tiltFloor h ≤ T := by
  have l0 : 0≤l := le_trans (by positivity) lo
  have hs : (h/710)^2 ≤ l^2 := by gcongr
  have ls : l^2 ≤ (1/2047:ℝ)^2 := by gcongr
  have z : 0≤1-l^2 := by linarith only [ls]
  apply le_trans _ lower
  unfold tiltFloor
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul (by linarith only [ls]) hs (by positivity) z

/-- The sum of the three slab contributions to the global smooth tilt. -/
theorem three_slabs {weight tilt : Fin 3 → ℝ} {T : ℝ}
    (mass : ∀ i, weightFloor (height i)≤weight i)
    (fiber : ∀ i, tiltFloor (height i)≤tilt i) (sum : ∑ i, weight i*tilt i≤T) : 79666/10^13<T := by
  calc 79666/10^13 < ∑ i, weightFloor (height i)*tiltFloor (height i) := by
         norm_num [Fin.sum_univ_succ,weightFloor,tiltFloor,height]
       _ ≤ ∑ i, weight i*tilt i := Finset.sum_le_sum fun i _ =>
         mul_le_mul (mass i) (fiber i) (by unfold tiltFloor; positivity)
           (le_trans (by fin_cases i <;> norm_num [weightFloor,height]) (mass i))
       _ ≤ _ := sum

/-- The given analytic discrepancy and smooth tilt put the actual inner
fraction strictly between 0.49999996837 and 0.49999999383. -/
theorem coverage {G J g j E : ℝ} (pos : 0<G+J) (g0 : 0≤g) (j0 : 0≤j)
    (good : |g-G|≤E) (bad : |j-J|≤E) (ratio : E/(G+J)≤179070/10^14)
    (tiltLo : 79666/10^13≤1/2-G/(G+J)) (tiltHi : 1/2-G/(G+J)≤298315/10^13) :
    49999996837/10^11 < g/(g+j) ∧ g/(g+j) < 49999999383/10^11 := by
  have e0 := (abs_nonneg _).trans good
  have small : E < (1/4)*(G+J) := (div_lt_iff₀ pos).mp (lt_of_le_of_lt ratio (by norm_num))
  have lo : (1/4)*(G+J) ≤ G := (le_div_iff₀ pos).mp (by linarith only [tiltHi])
  have hi : G ≤ (3/4)*(G+J) := (div_le_iff₀ pos).mp (by linarith only [tiltLo])
  obtain ⟨a,b⟩ := abs_le.mp (QuantilePopulationBounds.fraction_error e0 (by linarith only [small,lo])
    (by linarith only [small,hi]) g0 j0 good bad)
  constructor <;> linarith only [a,b,ratio,tiltLo,tiltHi]

/-- At most 300 fractional binary digits of √N may be conditioned on here.
At the finest width every individual cell is populated and has a strict
outer majority, given the two per-cell count discrepancy hypotheses. -/
theorem phase_300 {g j G J : ℕ} {E : ℝ} (pop : 0<(G:ℝ)+J)
    (upper : (G:ℝ)/(G+J)≤49999999383/10^11)
    (good : |(g:ℝ)-(1/(2:ℝ)^300)*G|≤E) (bad : |(j:ℝ)-(1/(2:ℝ)^300)*J|≤E)
    (disc : (2:ℝ)^328*E<(G:ℝ)+J) : 0<g+j ∧ (g:ℝ)/(g+j)<49999999756/10^11 ∧ g<j := by
  obtain ⟨pos,close⟩ := SquareRootPhasePopulation.phase_300 pop good bad disc
  have bound : (g:ℝ)/(g+j)<49999999756/10^11 := by linarith only [(abs_lt.mp close).2,upper]
  have less : (g:ℝ)/(g+j)<1/2 := lt_trans bound (by norm_num)
  have lt := (div_lt_iff₀ pos).mp less
  exact ⟨by exact_mod_cast pos,bound,by exact_mod_cast (show (g:ℝ)<j by linarith only [lt])⟩

end PrimeFactors.QuantileThetaBounds
