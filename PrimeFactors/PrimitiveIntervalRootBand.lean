import PrimeFactors.PrimitiveIntervalMoment
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Recover a short real interval for the smaller factor from a supplied,
possibly coarse estimate of the signed interval total. -/
namespace PrimeFactors.PrimitiveIntervalRootBand

open PrimitiveIntervalMoment

noncomputable def estimatedSum (n b v : ℝ) : ℝ :=
  max (2*Real.sqrt n) (b+1+Real.sqrt (v+2*n-2*b-1))

noncomputable def estimatedFactor (n b v : ℝ) : ℝ :=
  let s := estimatedSum n b v
  (s-Real.sqrt (s^2-4*n))/2

private theorem sqrt_error {a d : ℝ} (dp : 0≤d) :
    d*|Real.sqrt a-d|≤|a-d^2| := by
  by_cases ap : 0≤a
  · have nonneg := Real.sqrt_nonneg a
    calc
      _ ≤ (Real.sqrt a+d)*|Real.sqrt a-d| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ = |(Real.sqrt a+d)*(Real.sqrt a-d)| := by
        rw [abs_mul,abs_of_nonneg (add_nonneg nonneg dp)]
      _ = _ := by congr 1; nlinarith only [Real.sq_sqrt ap]
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge ap),zero_sub,abs_neg,abs_of_nonneg dp,
      abs_of_nonpos (show a-d^2≤0 by nlinarith only [sq_nonneg d,le_of_not_ge ap])]
    nlinarith only [le_of_not_ge ap]

private theorem clamp {lo t s : ℝ} (bound : lo≤s) : |max lo t-s|≤|t-s| := by
  rcases le_total lo t with top | low
  · rw [max_eq_right top]
  · rw [max_eq_left low,abs_of_nonpos (sub_nonpos.mpr bound),
      abs_of_nonpos (sub_nonpos.mpr (low.trans bound))]
    linarith

theorem sum_error {p q b v E : ℝ} (pp : 0≤p) (qp : 0≤q)
    (bp : 0≤b) (long : b≤p+q-b-1)
    (reading : |v-((p+q-b-1)^2-2*(p*q)+2*b+1)|≤E) :
    b*|estimatedSum (p*q) b v-(p+q)| ≤ E := by
  let a := v+2*(p*q)-2*b-1
  let d := p+q-b-1
  have dp : 0≤d := bp.trans long
  have lo : 2*Real.sqrt (p*q)≤p+q := by
    have h := Real.sq_sqrt (mul_nonneg pp qp)
    nlinarith only [h,sq_nonneg (q-p),Real.sqrt_nonneg (p*q),pp,qp]
  calc
    b*|estimatedSum (p*q) b v-(p+q)| ≤ b*|(b+1+Real.sqrt a)-(p+q)| :=
      mul_le_mul_of_nonneg_left (clamp lo) bp
    _ = b*|Real.sqrt a-d| := by dsimp only [d]; congr 2; ring
    _ ≤ d*|Real.sqrt a-d| := mul_le_mul_of_nonneg_right long (abs_nonneg _)
    _ ≤ |a-d^2| := sqrt_error dp
    _ = |v-((p+q-b-1)^2-2*(p*q)+2*b+1)| := by dsimp only [a,d]; congr 1; ring
    _ ≤ E := reading

/-- For fixed product, the smaller true root moves by at most twice the
smaller candidate root times the sum error divided by the true prime gap. -/
theorem lower_root_motion {p q x y : ℝ} (pp : 0≤p) (pq : p≤q) (xp : 0≤x)
    (xy : x≤y) (same : x*y=p*q) :
    (q-p)*|x-p| ≤ 2*x*|(x+y)-(p+q)| := by
  have twice : 2*x≤p+q := by
    nlinarith only [mul_nonneg xp (sub_nonneg.mpr xy),same,sq_nonneg (q-p),pp,pq,xp]
  have sign : 0≤q-x := by linarith
  have factor : (x-p)*(x-q) = x*((x+y)-(p+q)) := by nlinarith only [same]
  have equation := congrArg abs factor
  rw [abs_mul,abs_of_nonpos (by linarith : x-q≤0),abs_mul,abs_of_nonneg xp] at equation
  calc
    _ ≤ (2*(q-x))*|x-p| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ = _ := by linarith only [equation]

private theorem estimated_geometry {n b v : ℝ} (np : 0≤n) :
    let x := estimatedFactor n b v
    let y := estimatedSum n b v-x
    0≤x ∧ x≤y ∧ x*y=n := by
  let s := estimatedSum n b v
  change 0≤(s-Real.sqrt (s^2-4*n))/2 ∧ _ ∧ _
  have lo : 2*Real.sqrt n≤s := le_max_left ..
  have sp : 0≤s := by linarith [Real.sqrt_nonneg n]
  have square : 0≤s^2-4*n := by
    have := pow_le_pow_left₀ (by positivity : 0≤2*Real.sqrt n) lo 2
    nlinarith only [this,Real.sq_sqrt np]
  have ds := Real.sq_sqrt square
  have dp := Real.sqrt_nonneg (s^2-4*n)
  have le : Real.sqrt (s^2-4*n)≤s := by nlinarith only [ds,np,sp,dp]
  change 0≤(s-Real.sqrt (s^2-4*n))/2 ∧ (s-Real.sqrt (s^2-4*n))/2≤s-(s-Real.sqrt (s^2-4*n))/2 ∧
    ((s-Real.sqrt (s^2-4*n))/2)*(s-(s-Real.sqrt (s^2-4*n))/2)=n
  exact ⟨by linarith,by linarith,by nlinarith only [ds]⟩

/-- A pointwise bound for the explicit smaller-root estimate at any error
budget. It uses only the product, public cutoff, and supplied estimate v. -/
theorem estimate {p q b v E H : ℝ} (pp : 0≤p) (ordered : p≤q) (top : q≤H)
    (bp : 0≤b) (long : b≤p+q-b-1)
    (reading : |v-((p+q-b-1)^2-2*(p*q)+2*b+1)|≤E) :
    (q-p)*b*|estimatedFactor (p*q) b v-p| ≤ 2*H*E := by
  let s := estimatedSum (p*q) b v
  let x := estimatedFactor (p*q) b v
  let y := s-x
  obtain ⟨xp,xy,prod⟩ := estimated_geometry (b:=b) (v:=v) (mul_nonneg pp (pp.trans ordered))
  change 0≤x at xp
  change x≤y at xy
  change x*y=p*q at prod
  have move := lower_root_motion pp ordered xp xy prod
  rw [show x+y=s by dsimp [y]; ring] at move
  have xh : x≤H := by
    nlinarith only [mul_nonneg xp (sub_nonneg.mpr xy),prod,
      mul_le_mul_of_nonneg_right ordered (pp.trans ordered),top,pp,ordered,xp]
  have err := sum_error pp (pp.trans ordered) bp long reading
  change b*|s-(p+q)|≤E at err
  calc
    _ = b*((q-p)*|x-p|) := by ring
    _ ≤ b*(2*x*|s-(p+q)|) := mul_le_mul_of_nonneg_left move bp
    _ = 2*x*(b*|s-(p+q)|) := by ring
    _ ≤ 2*H*E := mul_le_mul (by linarith : 2*x≤2*H) err (mul_nonneg bp (abs_nonneg _))
      (by linarith : 0≤2*H)

end PrimeFactors.PrimitiveIntervalRootBand
