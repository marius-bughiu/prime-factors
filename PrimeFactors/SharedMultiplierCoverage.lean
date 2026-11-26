import PrimeFactors.MultiplierDivisorReach
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! Geometric coverage of every factorization of a common multiplier in a
single prefix of weighted Fermat traces. Integer candidates include composites. -/
namespace PrimeFactors.SharedMultiplierCoverage
open Finset

/-- The right endpoint of the balanced search is the square root of the input.
Write the input as t⁴ and the multiplier as r⁴. -/
def inWindow (t r s a b x : ℝ) : Prop :=
  0 < x ∧ x ≤ t^2 ∧ a*x^2 + b*t^4 < (2*r^2*t^2+s^2)*x

private theorem weight_floor {t r s a b x : ℝ} (tp : 0<t) (rp : 0<r) (ap : 0<a)
    (ab : a*b=r^4) (short : s^2≤r^2*t^2) (hit : inWindow t r s a b x) :
    r^2 ≤ 3*a := by
  obtain ⟨_,xt,inside⟩ := hit
  have hnon : 0≤2*r^2*t^2+s^2 := by positivity
  have high := mul_le_mul_of_nonneg_left xt hnon
  have bound := mul_le_mul_of_nonneg_right short (sq_nonneg t)
  have bt : b*t^4 < (3*r^2)*t^4 := by
    nlinarith only [inside,high,bound,mul_nonneg ap.le (sq_nonneg x)]
  have bcap := lt_of_mul_lt_mul_right bt (by positivity : 0≤t^4)
  have hab := mul_lt_mul_of_pos_left bcap ap
  have ha : r^2*r^2 ≤ (3*a)*r^2 := by nlinarith only [hab,ab]
  exact le_of_mul_le_mul_right ha (sq_pos_of_pos rp)

private theorem coordinate {t r s a b x : ℝ} (rp : 0<r) (tp : 0<t) (sp : 0≤s)
    (ap : 0<a) (ab : a*b=r^4) (hit : inWindow t r s a b x) :
    |2*a*x-(2*r^2*t^2+s^2)| ≤ 2*r*t*s+s^2 := by
  have multiplied := mul_lt_mul_of_pos_left hit.2.2 (show 0<4*a by positivity)
  have disc : (2*a*x-(2*r^2*t^2+s^2))^2 < 4*r^2*t^2*s^2+s^4 := by
    nlinarith only [multiplied,congrArg (fun v : ℝ => 4*v*t^4) ab]
  have loose : (2*a*x-(2*r^2*t^2+s^2))^2 ≤ (2*r*t*s+s^2)^2 := by
    nlinarith only [disc,show 0≤r*t*s^3 by positivity]
  exact (sq_le_sq.mp loose).trans_eq (abs_of_nonneg (by positivity))

/-- Diameters shrink as the fourth root of the multiplier grows. The two
points may be arbitrary integer positions, independent of divisibility. -/
theorem diameter {t r s a b x y : ℝ} (tp : 0<t) (r1 : 1≤r) (sp : 0≤s) (ap : 0<a)
    (ab : a*b=r^4) (short : s^2≤r^2*t^2) (hx : inWindow t r s a b x)
    (hy : inWindow t r s a b y) (xy : x≤y) :
    r*(y-x) ≤ 6*t*s+3*s^2 := by
  have rp : 0<r := by linarith
  have floor := weight_floor tp rp ap ab short hx
  have low := (abs_le.mp (coordinate rp tp sp ap ab hx)).1
  have high := (abs_le.mp (coordinate rp tp sp ap ab hy)).2
  have span : a*(y-x) ≤ 2*r*t*s+s^2 := by linarith only [low,high]
  have cap := mul_le_mul_of_nonneg_right floor (sub_nonneg.mpr xy)
  have norm := mul_le_mul_of_nonneg_right r1 (sq_nonneg s)
  have total : (r*(y-x))*r ≤ (6*t*s+3*s^2)*r := by nlinarith only [span,cap,norm]
  exact le_of_mul_le_mul_right total rp

private theorem row_count {t r s a b : ℝ} (tp : 0<t) (r1 : 1≤r) (sp : 0≤s) (ap : 0<a)
    (ab : a*b=r^4) (short : s^2≤r^2*t^2) (row : Finset ℕ)
    (mem : ∀ x∈row, inWindow t r s a b x) :
    r*row.card ≤ r+6*t*s+3*s^2 := by
  by_cases nonempty : row.Nonempty
  · let x := row.min' nonempty
    let y := row.max' nonempty
    have cover : row ⊆ Icc x y := fun z hz => mem_Icc.mpr ⟨row.min'_le z hz,row.le_max' z hz⟩
    have xy : x≤y := row.min'_le _ (row.max'_mem nonempty)
    have card := card_le_card cover
    rw [Nat.card_Icc] at card
    have bound : row.card+x ≤ y+1 := by omega
    have cast : (row.card:ℝ)+x≤y+1 := by exact_mod_cast bound
    have cmp := diameter tp r1 sp ap ab short (mem x (row.min'_mem nonempty))
      (mem y (row.max'_mem nonempty)) (by exact_mod_cast xy)
    have scaled := mul_le_mul_of_nonneg_left cast (by linarith : 0≤r)
    nlinarith only [cmp,scaled]
  · simp only [Finset.not_nonempty_iff_eq_empty.mp nonempty,card_empty,Nat.cast_zero,mul_zero]
    positivity


/-- All divisor directions cost one common prefix. The sum of their integer
coverage is still bounded, even if the multiplier depends on the input. -/
theorem all_directions {t r s : ℝ} {k : ℕ} (hk : k≠0) (rk : (k:ℝ)=r^4)
    (r1 : 1≤r) (rt : r≤t) (sp : 0≤s) (short : s^2≤r^2*t^2)
    (row : ℕ → Finset ℕ)
    (mem : ∀ a∈k.divisors, ∀ x∈row a, inWindow t r s a (k/a:ℕ) x) :
    ((k.divisors.biUnion row).card : ℝ) ≤ 9*(t+6*t*s+3*s^2) := by
  have rp : 0<r := by linarith
  have tp : 0<t := by linarith
  have bound := MultiplierDivisorReach.fourth_power_bound hk
  have cb : (k.divisors.card:ℝ)^4 < 9^4*(k:ℝ) := by exact_mod_cast bound
  have card : (k.divisors.card:ℝ) ≤ 9*r := by
    by_contra! larger
    have contra := pow_le_pow_left₀ (by positivity : 0≤9*r) larger.le 4
    rw [mul_pow,←rk] at contra
    linarith
  have total : r*((k.divisors.biUnion row).card:ℝ) ≤
      (k.divisors.card:ℝ)*(r+6*t*s+3*s^2) := calc
    _ ≤ r*(∑ a∈k.divisors, ((row a).card:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ rp.le
      exact_mod_cast (card_biUnion_le : (k.divisors.biUnion row).card ≤ _)
    _ = ∑ a∈k.divisors, r*((row a).card:ℝ) := by rw [mul_sum]
    _ ≤ ∑ _a∈k.divisors, (r+6*t*s+3*s^2) := by
      apply sum_le_sum
      intro a ha
      have pos := Nat.pos_of_mem_divisors ha
      have fact := Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1
      have cast : (a:ℝ)*(k/a:ℕ)=r^4 := by rw [←rk]; exact_mod_cast fact
      exact row_count tp r1 sp (by exact_mod_cast pos) cast short (row a) (mem a ha)
    _ = _ := by simp; ring
  apply le_of_mul_le_mul_left (a:=r) _ rp
  calc
    _ ≤ _ := total
    _ ≤ (9*r)*(r+6*t*s+3*s^2) := mul_le_mul_of_nonneg_right card (by positivity)
    _ ≤ r*(9*(t+6*t*s+3*s^2)) := by nlinarith only [mul_le_mul_of_nonneg_left rt rp.le]

noncomputable def fourthRoot (n : ℕ) : ℝ := Real.sqrt (Real.sqrt n)

private theorem fourth_sq (n : ℕ) : fourthRoot n ^ 2 = Real.sqrt n := Real.sq_sqrt (Real.sqrt_nonneg _)

private theorem fourth_pow (n : ℕ) : fourthRoot n ^ 4 = (n:ℝ) := by
  rw [show 4=2*2 by decide,pow_mul,fourth_sq,Real.sq_sqrt (Nat.cast_nonneg _)]

/-- Public condition for a location below the first omitted trace, for some
ordered factorization of the multiplier. The factor location need not divide n. -/
def Reaches (n k : ℕ) (height : ℝ) (x : ℕ) : Prop :=
  0<x ∧ (x:ℝ)≤Real.sqrt n ∧ ∃ a∈k.divisors,
    (a:ℝ)*x^2 + (k/a:ℕ)*(n:ℝ) < (2*Real.sqrt ((k:ℝ)*n)+height)*x

set_option exponentiation.threshold 4096
set_option maxHeartbeats 1000000

/-- Even a billion independently selected multipliers and a prefix of
2³² consecutive integer traces per multiplier cover fewer than 2⁵⁶⁴
possible integer locations at 2,048 bits. The extra unit accounts for ceiling. -/
theorem billion_multipliers {n : ℕ} (bits : 2^2047≤n) (top : n<2^2048)
    (menu locations : Finset ℕ) (budget : menu.card≤10^9)
    (weights : ∀ k∈menu, 0<k ∧ k≤n)
    (reached : ∀ x∈locations, ∃ k∈menu, Reaches n k (2^32+1) x) :
    locations.card < 2^564 := by
  classical
  let t := fourthRoot n
  let s : ℝ := 65537
  let row (k a : ℕ) := locations.filter (fun (x : ℕ) =>
    inWindow t (fourthRoot k) s a (k/a:ℕ) x)
  have tlo : 65537 ≤ t := by
    apply le_of_not_gt
    intro h
    have cmp := pow_le_pow_left₀ (Real.sqrt_nonneg _ : 0≤t) h.le 4
    have lower : (65537:ℝ)^4 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide +kernel : 65537^4<2^2047) bits)
    change fourthRoot n ^ 4 ≤ _ at cmp
    rw [fourth_pow] at cmp
    linarith
  have thi : t ≤ 2^512 := by
    apply le_of_not_gt
    intro h
    have cmp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2^512) h.le 4
    change _ ≤ fourthRoot n ^ 4 at cmp
    rw [fourth_pow, ←pow_mul] at cmp
    exact (not_le.mpr (by exact_mod_cast top : (n:ℝ)<2^2048)) cmp
  have size (k : ℕ) (hk : k∈menu) :
      (((k.divisors.biUnion (row k)).card):ℝ) ≤
      9*(t+6*t*s+3*s^2) := by
    obtain ⟨kp,kn⟩ := weights _ hk
    have r1 : 1≤fourthRoot k := by
      have one : (1:ℝ)≤k := by exact_mod_cast kp
      simpa [fourthRoot] using Real.sqrt_le_sqrt (Real.sqrt_le_sqrt one)
    have rt : fourthRoot k ≤ t := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (by exact_mod_cast kn))
    have rp : 1≤fourthRoot k ^2 := by nlinarith only [r1,sq_nonneg (fourthRoot k-1)]
    have st : s^2≤t^2 := pow_le_pow_left₀ (by norm_num [s]) tlo 2
    apply all_directions kp.ne' (fourth_pow k).symm r1 rt (by norm_num [s])
      (st.trans (by nlinarith only [mul_le_mul_of_nonneg_right rp (sq_nonneg t)]))
    exact fun a _ x hx => (mem_filter.mp hx).2
  have cover : locations ⊆ menu.biUnion (fun k => k.divisors.biUnion (row k)) := by
    intro x hx
    obtain ⟨k,hk,xp,xt,a,ha,ineq⟩ := reached _ hx
    refine mem_biUnion.mpr ⟨k,hk,mem_biUnion.mpr ⟨a,ha,mem_filter.mpr ⟨hx,?_⟩⟩⟩
    refine ⟨by exact_mod_cast xp,by simpa [t,fourth_sq] using xt,?_⟩
    rw [show t ^4 = (n:ℝ) from fourth_pow n, fourth_sq,show t^2=Real.sqrt n from fourth_sq n]
    rw [Real.sqrt_mul (Nat.cast_nonneg _) _] at ineq
    have spare := mul_le_mul_of_nonneg_right (by norm_num [s] : (2:ℝ)^32+1≤s^2) (Nat.cast_nonneg x)
    nlinarith only [ineq,spare]
  have cap : (locations.card:ℝ) ≤ (menu.card:ℝ)*(9*(t+6*t*s+3*s^2)) := calc
    _ ≤ ∑ k∈menu, (((k.divisors.biUnion (row k)).card):ℝ) := by
      exact_mod_cast (card_le_card cover).trans card_biUnion_le
    _ ≤ ∑ _k∈menu, (9*(t+6*t*s+3*s^2)) := sum_le_sum size
    _ = _ := by simp
  have mb : (menu.card:ℝ)≤10^9 := by exact_mod_cast budget
  have total : (locations.card:ℝ)<2^564 := calc
    _ ≤ _ := cap
    _ ≤ (10:ℝ)^9*(9*((2^512)+6*(2^512)*s+3*s^2)) := by gcongr
    _ < _ := by norm_num [s]
  exact_mod_cast total

end PrimeFactors.SharedMultiplierCoverage
