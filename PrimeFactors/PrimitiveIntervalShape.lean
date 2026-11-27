import PrimeFactors.PrimitiveIntervalMoment
import PrimeFactors.OppositeSquareScaleBands
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue

/-! A fixed multiple cN which approximates the signed interval aggregate
within 4B also predicts the sum to within eight at one fixed real factor
ratio. The ratio depends only on c. -/
namespace PrimeFactors.PrimitiveIntervalShape

open PrimitiveIntervalMoment

/-- The exact integer on the right of the interval aggregate identity. -/
def reading (p q : ℕ) : ℤ := value ((p:ℤ)*q) (cutoff (p*q)) ((p:ℤ)+q)

/-- On the intended prime pairs this is the actual signed character sum. -/
theorem aggregate_eq_reading {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ord : p<q) (bal : q<2*p) :
    aggregate p q (cutoff (p*q))=(reading p q:ℂ) := aggregate_value ord bal

/-- A fixed multiple of the product attains the stipulated absolute error. -/
noncomputable def hit (c : ℝ) (p q : ℕ) : Prop :=
  |(reading p q : ℝ)-c*((p:ℝ)*q)| ≤ 4*(cutoff (p*q):ℝ)

noncomputable def coefficient (c : ℝ) : ℝ := 1/Real.sqrt 2 + Real.sqrt (c+2)

private theorem cutoff_round (n : ℕ) : (cutoff n:ℝ) ≤ (1/Real.sqrt 2)*Real.sqrt n ∧
    (1/Real.sqrt 2)*Real.sqrt n < (cutoff n:ℝ)+1 := by
  have lo : (cutoff n)^2*2 ≤ n := (Nat.le_div_iff_mul_le (by decide : 0<2)).mp (Nat.sqrt_le' _)
  have hi : n < (cutoff n+1)^2*2 := (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mp
    (Nat.sqrt_lt'.mp (Nat.lt_succ_self (cutoff n)))
  rw [show (1/Real.sqrt 2)*Real.sqrt n = Real.sqrt ((n:ℝ)/2) by
    rw [Real.sqrt_div (by positivity)]; ring]
  constructor
  · apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    exact_mod_cast lo
  · apply (Real.sqrt_lt' (by positivity)).mpr
    apply (div_lt_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    exact_mod_cast hi

/-- Removing a square from an approximation costs at most its error divided
by the known positive root d. The auxiliary target is allowed to be negative. -/
private theorem root_error {d a K : ℝ} (dp : 0<d) (close : |d^2-a|≤K*d) :
    |d-Real.sqrt a|≤K := by
  apply le_of_mul_le_mul_right (a:=d) _ dp
  by_cases pos : 0≤a
  · calc
      _ ≤ |d-Real.sqrt a| *(d+Real.sqrt a) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (abs_nonneg _)
      _ = |(d-Real.sqrt a)*(d+Real.sqrt a)| := by rw [abs_mul,abs_of_nonneg (by positivity : 0≤d+Real.sqrt a)]
      _ = |d^2-a| := by rw [show (d-Real.sqrt a)*(d+Real.sqrt a)=d^2-(Real.sqrt a)^2 by ring,Real.sq_sqrt pos]
      _ ≤ _ := close
  · have neg := le_of_not_ge pos
    rw [Real.sqrt_eq_zero_of_nonpos neg,sub_zero,abs_of_pos dp]
    rw [abs_of_nonneg (sub_nonneg.mpr (neg.trans (sq_nonneg d)))] at close
    nlinarith only [close,neg]

/-- Before restricting to feasible balanced ratios, the implied sum has
coefficient 1/√2+√(c+2), for any real c. -/
theorem raw_shape_budget {c k : ℝ} {p q : ℕ} (pos : 0<p) (ord : p<q) (bal : q<2*p) (kn : 0≤k)
    (good : |(reading p q:ℝ)-c*((p:ℝ)*q)| ≤ k*(cutoff (p*q):ℝ)) :
    |(p:ℝ)+q-coefficient c*Real.sqrt ((p:ℝ)*q)|≤k+4 := by
  let b : ℝ := cutoff (p*q)
  let s : ℝ := (p:ℝ)+q
  let n : ℝ := (p:ℝ)*q
  let d := s-b-1
  have b0 : 0≤b := Nat.cast_nonneg _
  have bp : b+1 ≤ (p:ℝ) := by
    dsimp only [b]
    exact_mod_cast (show cutoff (p*q)+1≤p from Nat.succ_le_of_lt (cutoff_bounds pos bal).1)
  have pq : (p:ℝ)≤q := by exact_mod_cast ord.le
  have dlow : b+1≤d := by dsimp only [d,s]; linarith only [bp,pq]
  have dp : 0<d := by linarith only [dlow,b0]
  have square : d^2 = (reading p q:ℝ)+2*n-2*b-1 := by
    dsimp only [reading,value,d,s,n,b]
    push_cast
    ring
  have shift : d^2-(c+2)*n=((reading p q:ℝ)-c*n)-(2*b+1) := by rw [square]; ring
  obtain ⟨lo,hi⟩ := abs_le.mp (show |(reading p q:ℝ)-c*n|≤k*b from good)
  have compare := mul_le_mul_of_nonneg_left (show b≤d by linarith only [dlow]) kn
  have close : |d^2-(c+2)*n|≤(k+3)*d := by
    rw [shift,abs_le,add_mul]
    constructor <;> linarith only [lo,hi,dlow,b0,compare]
  have near := root_error dp close
  have npos : 0≤n := by dsimp only [n]; positivity
  rw [Real.sqrt_mul' _ npos] at near
  have floor := cutoff_round (p*q)
  simp only [Nat.cast_mul] at floor
  change b ≤ (1/Real.sqrt 2)*Real.sqrt n ∧ (1/Real.sqrt 2)*Real.sqrt n < b+1 at floor
  have roundoff : |b+1-(1/Real.sqrt 2)*Real.sqrt n|≤1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr floor.2.le),sub_le_iff_le_add]
    exact (add_le_add_right floor.1 1).trans_eq (add_comm _ _)
  change |s-coefficient c*Real.sqrt n|≤k+4
  rw [show s-coefficient c*Real.sqrt n = (d-Real.sqrt (c+2)*Real.sqrt n)+
    (b+1-(1/Real.sqrt 2)*Real.sqrt n) by dsimp only [d,coefficient]; ring]
  exact (abs_add_le ..).trans ((add_le_add near roundoff).trans_eq (by ring))

/-- Aggregate error E at positive cutoff B permits sum error E/B+4. -/
theorem raw_shape_error {c E : ℝ} {p q : ℕ} (pos : 0<p) (ord : p<q) (bal : q<2*p)
    (bound : 0<cutoff (p*q)) (good : |(reading p q:ℝ)-c*((p:ℝ)*q)|≤E) :
    |(p:ℝ)+q-coefficient c*Real.sqrt ((p:ℝ)*q)|≤E/(cutoff (p*q):ℝ)+4 := by
  have bp : 0<(cutoff (p*q):ℝ) := by exact_mod_cast bound
  exact raw_shape_budget pos ord bal (div_nonneg ((abs_nonneg _).trans good) bp.le)
    (by rwa [div_mul_cancel₀ E bp.ne'])

theorem raw_shape {c : ℝ} {p q : ℕ} (pos : 0<p) (ord : p<q) (bal : q<2*p) (good : hit c p q) :
    |(p:ℝ)+q-coefficient c*Real.sqrt ((p:ℝ)*q)|≤8 :=
  (raw_shape_budget pos ord bal (by norm_num : (0:ℝ)≤4) good).trans_eq (by norm_num)

private noncomputable def score (r : ℝ) := Real.sqrt r+1/Real.sqrt r

private theorem score_one : score 1=2 := by norm_num [score]

private theorem score_two : score 2=3/Real.sqrt 2 := by
  unfold score
  have pos : 0<Real.sqrt 2 := by positivity
  field_simp
  nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

private theorem balanced_range {p q : ℕ} (ord : p<q) (bal : q<2*p) :
    2*Real.sqrt ((p:ℝ)*q) ≤ (p:ℝ)+q ∧ (p:ℝ)+q ≤ score 2*Real.sqrt ((p:ℝ)*q) := by
  obtain ⟨lo,hi⟩ := OppositeSquareScaleBands.balanced_sum ord bal
  have lower : 4*((p:ℝ)*q)≤((p:ℝ)+q)^2 := by exact_mod_cast lo.le
  have upper : 2*((p:ℝ)+q)^2≤9*((p:ℝ)*q) := by exact_mod_cast hi
  have sq := Real.sq_sqrt (show 0≤(p:ℝ)*q by positivity)
  have half := Real.sq_sqrt (show 0≤((p:ℝ)*q)/2 by positivity)
  constructor
  · apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith only [lower,sq]
  · rw [score_two,show (3/Real.sqrt 2)*Real.sqrt ((p:ℝ)*q) = 3*Real.sqrt (((p:ℝ)*q)/2) by
      rw [Real.sqrt_div (by positivity)]; ring]
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith only [upper,half]

/-- Project an arbitrary coefficient to the attainable score interval and
choose one ratio independently of any subsequent observation. -/
private theorem choose_ratio (a : ℝ) : ∃ r ∈ Set.Icc (1:ℝ) 2,
    ∀ x s : ℝ, 0≤x → 2*x≤s → s≤score 2*x → |s-score r*x|≤|s-a*x| := by
  by_cases low : a<2
  · refine ⟨1,by constructor <;> norm_num,?_⟩
    intro x s xp left _
    have shifted := (mul_le_mul_of_nonneg_right low.le xp).trans left
    rw [score_one,abs_of_nonneg (sub_nonneg.mpr left),abs_of_nonneg (sub_nonneg.mpr shifted)]
    linarith only [mul_le_mul_of_nonneg_right low.le xp]
  by_cases high : score 2<a
  · refine ⟨2,by constructor <;> norm_num,?_⟩
    intro x s xp _ right
    have shifted := right.trans (mul_le_mul_of_nonneg_right high.le xp)
    rw [abs_of_nonpos (sub_nonpos.mpr right),abs_of_nonpos (sub_nonpos.mpr shifted)]
    linarith only [mul_le_mul_of_nonneg_right high.le xp]
  have continuous : ContinuousOn score (Set.Icc (1:ℝ) 2) :=
    Real.continuous_sqrt.continuousOn.add (continuousOn_const.div Real.continuous_sqrt.continuousOn
      fun _ hx => (Real.sqrt_pos.mpr (zero_lt_one.trans_le hx.1)).ne')
  have inside : a∈Set.Icc (score 1) (score 2) := ⟨score_one ▸ le_of_not_gt low,le_of_not_gt high⟩
  obtain ⟨r,hr,hrscore⟩ := intermediate_value_Icc (by norm_num : (1:ℝ)≤2) continuous inside
  exact ⟨r,hr,fun x s _ _ _ => by rw [hrscore]⟩

/-- The same comparison ratio applies at every nonnegative multiple k of
the cutoff in the aggregate-error budget. -/
theorem exists_ratio_budget (c : ℝ) : ∃ r ∈ Set.Icc (1:ℝ) 2, ∀ {p q : ℕ} {k : ℝ},
    0<p → p<q → q<2*p → 0≤k → |(reading p q:ℝ)-c*((p:ℝ)*q)|≤k*(cutoff (p*q):ℝ) →
    |(p:ℝ)+q-(Real.sqrt r+1/Real.sqrt r)*Real.sqrt ((p:ℝ)*q)|≤k+4 := by
  obtain ⟨r,hr,close⟩ := choose_ratio (coefficient c)
  refine ⟨r,hr,?_⟩
  intro p q k pos ord bal kn good
  obtain ⟨lo,hi⟩ := balanced_range ord bal
  exact (close _ _ (Real.sqrt_nonneg _) lo hi).trans (raw_shape_budget pos ord bal kn good)

/-- One comparison ratio works for every balanced input on which cN predicts
the exact aggregate within 4B. The existential comes before the factors. -/
theorem exists_ratio (c : ℝ) : ∃ r ∈ Set.Icc (1:ℝ) 2, ∀ {p q : ℕ},
    0<p → p<q → q<2*p → hit c p q →
    |(p:ℝ)+q-(Real.sqrt r+1/Real.sqrt r)*Real.sqrt ((p:ℝ)*q)|≤8 := by
  obtain ⟨r,hr,close⟩ := choose_ratio (coefficient c)
  refine ⟨r,hr,?_⟩
  intro p q pos ord bal good
  obtain ⟨lo,hi⟩ := balanced_range ord bal
  exact (close _ _ (Real.sqrt_nonneg _) lo hi).trans (raw_shape pos ord bal good)

end PrimeFactors.PrimitiveIntervalShape
