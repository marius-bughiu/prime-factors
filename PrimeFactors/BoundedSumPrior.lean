import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Sqrt

/-! Limit on any reordering when the underlying masses decrease with the
integer sum and residue information multiplies each mass by either two or
five. These are bounds for the specified prior on a finite candidate list. -/

namespace PrimeFactors.BoundedSumPrior

open Finset

private def ranks (s : Finset ℕ) (r : ℕ → ℕ) := ∑ i∈s,(r i+1)

/-- An injective assignment of one-based ranks pays at least the first
triangular number of that size. -/
private theorem rank_floor (s : Finset ℕ) (r : ℕ → ℕ) (inj : Set.InjOn r (s: Set ℕ)) :
    s.card*(s.card+1)≤2*ranks s r := by
  classical
  have lower (v : Finset ℕ) : v.card*(v.card+1)≤2*∑ i∈v,(i+1) := by
    induction v using Finset.induction_on_max with
    | h0 => simp
    | step a v lt ih =>
      have na : a∉v := fun h => (lt a h).false
      have size : v.card≤a := (card_le_card (show v⊆range a from
        fun i hi => mem_range.mpr (lt i hi))).trans_eq (card_range a)
      rw [card_insert_of_not_mem na,sum_insert na]
      nlinarith only [size,ih]
  have h := lower (s.image r)
  rw [card_image_of_injOn inj,sum_image (by exact inj)] at h
  exact h

private theorem range_total (n : ℕ) : 2*ranks (range n) id=n*(n+1) := by
  induction n with
  | zero => simp [ranks]
  | succ n ih =>
    simp only [ranks,sum_range_succ,id_eq] at ih ⊢
    nlinarith only [ih]

/-- Local multiplicity of a candidate. -/
def weight (hot : ℕ → Bool) (i : ℕ) := if hot i then 5 else 2

private theorem split_cost (n : ℕ) (hot : ℕ → Bool) (r : ℕ → ℕ) :
    ∑ i∈range n,weight hot i*(r i+1) =
    2*ranks (range n) r+3*ranks ((range n).filter (fun i => hot i=true)) r := by
  classical
  simp only [ranks,mul_sum,sum_filter,←sum_add_distrib]
  apply sum_congr rfl
  intro i _
  cases mark : hot i <;> simp [weight,mark]
  omega

/-- The two extreme arrangements of the heavy positions give a square
after scaling the best possible rank sum by the square root of 5/2. -/
private theorem extreme_bounds (k h z : ℝ) (hk : 0≤k) (hh : 0≤h)
    (hz : 1≤z) (square : z^2=5/2) :
    2*k*(k+1)+3*h*(2*k-h+1) ≤ z*(2*k*(k+1)+3*h*(h+1)) := by
  apply sub_nonneg.mp
  calc
    0 ≤ 2*(z-1)*((k-(z+1)*h)^2+k+3/2*h) :=
      mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hz)) (by positivity)
    _ = _ := by linear_combination (2*(z+1)*h^2-4*k*h)*square

private theorem uniform_bound (n : ℕ) (hot : ℕ → Bool) (r : ℕ → ℕ)
    (inj : Set.InjOn r ↑(range n)) :
    (∑ i∈range n, (weight hot i*(i+1):ℕ) : ℝ) ≤
      Real.sqrt (5/2)*(∑ i∈range n, (weight hot i*(r i+1):ℕ) : ℝ) := by
  classical
  let S := range n
  let H := S.filter (fun i => hot i=true)
  let z := Real.sqrt (5/2)
  have square : z^2=5/2 := Real.sq_sqrt (by norm_num)
  have hz : 1≤z := by nlinarith [Real.sqrt_nonneg (5/2)]
  have sub : H⊆S := filter_subset ..
  have card : S.card=n := card_range n
  have hs := rank_floor S r inj
  have hh := rank_floor H r (inj.mono sub)
  have other := rank_floor (S \ H) id (Function.injective_id.injOn)
  have size : (S \ H).card=n-H.card := by rw [card_sdiff sub,card]
  have small := card_le_card sub
  rw [card] at hs small
  rw [size] at other
  have total : ranks (S \ H) id+ranks H id=ranks S id := sum_sdiff sub
  have sum := range_total n
  change 2*ranks S id=_ at sum
  rify [small] at hs hh other total sum
  have best : 2*(n:ℝ)*(n+1)+3*(H.card:ℝ)*(H.card+1) ≤
      2*(2*(ranks S r:ℝ)+3*(ranks H r:ℝ)) := by linarith
  have worst : 2*(2*(ranks S id:ℝ)+3*(ranks H id:ℝ)) ≤
      2*(n:ℝ)*(n+1)+3*(H.card:ℝ)*(2*n-H.card+1) := by nlinarith only [other,total,sum]
  have bound := extreme_bounds n H.card z (by positivity) (by positivity) hz square
  change (∑ i∈range n, ((weight hot i*(id i+1):ℕ):ℝ))≤_
  rw [←Nat.cast_sum,←Nat.cast_sum,split_cost,split_cost]
  change ((2*ranks S id+3*ranks H id:ℕ):ℝ)≤z*((2*ranks S r+3*ranks H r:ℕ):ℝ)
  push_cast
  linarith only [worst.trans (bound.trans (mul_le_mul_of_nonneg_left best (by linarith)))]

/-- For any nonnegative antitone base density, multiplying individual masses
by two or five leaves every injective rank assignment with at least
`√(2/5)` times the ascending order's expected rank. Both sides may be
divided by the same positive total mass. -/
theorem sharp_improvement (n : ℕ) (base : ℕ → ℝ) (hot : ℕ → Bool) (r : ℕ → ℕ)
    (nonneg : ∀ i, 0≤base i) (decreasing : Antitone base) (inj : Set.InjOn r ↑(range n)) :
    Real.sqrt (2/5)*(∑ i∈range n,base i*(weight hot i*(i+1):ℕ)) ≤
    ∑ i∈range n,base i*(weight hot i*(r i+1):ℕ) := by
  let z := Real.sqrt (5/2)
  let delta (i : ℕ) : ℝ := z*(weight hot i*(r i+1):ℕ)-(weight hot i*(i+1):ℕ)
  have prefix_pos (k : ℕ) (le : k≤n) : 0≤∑ i∈range k,delta i := by
    have bound := uniform_bound k hot r (inj.mono (range_mono le))
    simpa only [delta,sum_sub_distrib,←mul_sum,sub_nonneg] using bound
  have pos : 0≤∑ i∈range n, base i • delta i := by
    rw [sum_range_by_parts]
    apply sub_nonneg.mpr
    exact (sum_nonpos fun i hi => mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (decreasing (Nat.le_succ i)))
      (prefix_pos _ (by have := mem_range.mp hi; omega))).trans
      (mul_nonneg (nonneg _) (prefix_pos _ le_rfl))
  simp only [smul_eq_mul,delta,mul_sub,sum_sub_distrib] at pos
  simp_rw [mul_left_comm (base _) z] at pos
  rw [←mul_sum,sub_nonneg] at pos
  have cancel : Real.sqrt (2/5) * z = 1 := by
    rw [show z=Real.sqrt (5/2) from rfl,←Real.sqrt_mul (by norm_num)]
    norm_num
  simpa only [←mul_assoc,cancel,one_mul] using
    (mul_le_mul_of_nonneg_left pos (Real.sqrt_nonneg (2/5)))

/-- The rational five-eighths bound follows from the square-root bound. -/
theorem bounded_improvement (n : ℕ) (base : ℕ → ℝ) (hot : ℕ → Bool) (r : ℕ → ℕ)
    (nonneg : ∀ i, 0≤base i) (decreasing : Antitone base) (inj : Set.InjOn r ↑(range n)) :
    5*(∑ i∈range n,base i*(weight hot i*(i+1):ℕ)) ≤
    8*(∑ i∈range n,base i*(weight hot i*(r i+1):ℕ)) := by
  have root := Real.sq_sqrt (show (0:ℝ)≤2/5 by norm_num)
  have bound : (5:ℝ)/8 ≤ Real.sqrt (2/5) := by
    nlinarith [Real.sqrt_nonneg (2/5)]
  have cost := sharp_improvement n base hot r nonneg decreasing inj
  have pos : 0≤∑ i∈range n,base i*(weight hot i*(i+1):ℕ) :=
    sum_nonneg (fun i _ => mul_nonneg (nonneg i) (by positivity))
  linarith only [(mul_le_mul_of_nonneg_right bound pos).trans cost]

private def tailHeavy (l i : ℕ) := if i<l then false else true

private def tailFirst (l h i : ℕ) := if i<l then h+i else i-l

private theorem segment (n a b : ℕ) :
    ∑ i∈range n,b*(a+i+1) = b*(n*a+ranks (range n) id) := by
  simp only [ranks,id_eq,Nat.add_assoc,mul_add,←mul_sum,sum_add_distrib,sum_const,card_range,
    smul_eq_mul]
  rw [mul_sum]

private theorem two_segments (l h : ℕ) :
    let asc := ∑ i∈range (l+h),weight (tailHeavy l) i*(i+1)
    let first := ∑ i∈range (l+h),weight (tailHeavy l) i*(tailFirst l h i+1)
    2*asc=2*(l+h)*(l+h+1)+3*h*(2*l+h+1) ∧
    2*first=2*(l+h)*(l+h+1)+3*h*(h+1) := by
  dsimp only
  have a : ∑ i∈range l,weight (tailHeavy l) i*(i+1) = 2*ranks (range l) id := by
    rw [ranks,mul_sum]
    exact sum_congr rfl (fun i hi => by simp [weight,tailHeavy,mem_range.mp hi])
  have b : (∑ i∈range h,weight (tailHeavy l) (l+i)*(l+i+1)) =
      5*(h*l+ranks (range h) id) := by
    simpa [weight,tailHeavy] using segment h l 5
  have c : (∑ i∈range l,weight (tailHeavy l) i*(tailFirst l h i+1)) =
      2*(l*h+ranks (range l) id) := by
    rw [←segment]
    exact sum_congr rfl (fun i hi => by simp [weight,tailHeavy,tailFirst,mem_range.mp hi])
  have d : (∑ i∈range h,weight (tailHeavy l) (l+i)*(tailFirst l h (l+i)+1)) =
      5*ranks (range h) id := by
    simp [weight,tailHeavy,tailFirst,ranks,mul_sum]
  rw [Finset.sum_range_add,Finset.sum_range_add,a,b,c,d]
  constructor <;> nlinarith only [range_total l,range_total h]

/-- Flat base masses with a block of heavy positions at the end approach
the bound, by moving this block to the beginning. In particular no larger
universal lower ratio holds, even for permutations of a complete list. -/
theorem sharpness {ε : ℝ} (positive : 0<ε) :
    ∃ (n : ℕ) (hot : ℕ → Bool) (r : ℕ → ℕ), Set.InjOn r ↑(range n) ∧
      (∀ i<n, r i<n) ∧
      (∑ i∈range n, ((weight hot i*(r i+1):ℕ):ℝ)) <
      (Real.sqrt (2/5)+ε)*(∑ i∈range n, ((weight hot i*(i+1):ℕ):ℝ)) := by
  let z := Real.sqrt (5/2)
  have square : z^2=5/2 := Real.sq_sqrt (by norm_num)
  have one : 1<z := by nlinarith [Real.sqrt_nonneg (5/2)]
  have two : z<2 := by nlinarith [Real.sqrt_nonneg (5/2)]
  obtain ⟨h,large⟩ := exists_nat_gt (12/ε)
  have hpos : 0<h := by exact_mod_cast (lt_of_le_of_lt (by positivity : (0:ℝ)≤12/ε) large)
  have h1 : (1:ℝ)≤h := by exact_mod_cast hpos
  let l := ⌊z*h⌋₊
  have low : (l:ℝ)≤z*h := Nat.floor_le (mul_nonneg (by linarith) (by positivity))
  have high : z*h<(l:ℝ)+1 := Nat.lt_floor_add_one _
  refine ⟨l+h,tailHeavy l,tailFirst l h,?_,?_,?_⟩
  · intro i hi j hj eq
    simp only [mem_coe,mem_range] at hi hj
    unfold tailFirst at eq
    split_ifs at eq <;> omega
  · intro i hi
    unfold tailFirst
    split_ifs <;> omega
  let A : ℕ := ∑ i∈range (l+h),weight (tailHeavy l) i*(i+1)
  let C : ℕ := ∑ i∈range (l+h),weight (tailHeavy l) i*(tailFirst l h i+1)
  obtain ⟨asc,best⟩ := two_segments l h
  change 2*A=_ at asc
  change 2*C=_ at best
  rify at asc best
  have close : ((l:ℝ)-z*h)^2≤1 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr low) (show 0≤1+((l:ℝ)-z*h) by linarith)]
  have exact_gap :
      z*(2*(C:ℝ))-2*A=2*(z-1)*(((l:ℝ)-z*h)^2+l+h+3/2*h) := by
    linear_combination z*best-asc+(4*(l:ℝ)*h-2*(z-1)*h^2)*square
  have inner : ((l:ℝ)-z*h)^2+l+h+3/2*h ≤ 6*h := by
    linarith only [h1,close,low,mul_le_mul_of_nonneg_right two.le (by positivity : (0:ℝ)≤h)]
  have gap : z*(2*(C:ℝ))-2*A≤12*h := by
    rw [exact_gap]
    calc
      _ ≤ 2*(z-1)*(6*h) := mul_le_mul_of_nonneg_left inner (by linarith)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right two.le (by positivity : (0:ℝ)≤h)]
  have a_floor : (h:ℝ)^2≤2*A := by
    nlinarith only [asc, sq_nonneg (l:ℝ), Nat.cast_nonneg (α:=ℝ) l, Nat.cast_nonneg (α:=ℝ) h,
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) l) (Nat.cast_nonneg (α:=ℝ) h)]
  have grow : 12*(h:ℝ) < ε*(2*A) := by
    calc
      _ < ((h:ℝ)*ε)*h := mul_lt_mul_of_pos_right ((div_lt_iff₀ positive).mp large) (by positivity)
      _ ≤ _ := by simpa only [pow_two,mul_left_comm,mul_comm,mul_assoc] using
                   mul_le_mul_of_nonneg_left a_floor positive.le
  have cancel : Real.sqrt (2/5)*z=1 := by
    rw [show z=Real.sqrt (5/2) from rfl,←Real.sqrt_mul (by norm_num)]
    norm_num
  rw [←Nat.cast_sum,←Nat.cast_sum]
  change (C:ℝ)<(Real.sqrt (2/5)+ε)*A
  apply lt_of_mul_lt_mul_left (a:=z)
  · nlinarith only [gap.trans_lt grow,mul_le_mul_of_nonneg_right one.le
      (show 0≤ε*(2*(A:ℝ)) by positivity),congrArg (fun x : ℝ => x*(A:ℝ)) cancel]
  · linarith

end PrimeFactors.BoundedSumPrior
