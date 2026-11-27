import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-! An elementary uniform bound for the product of the maximum density
improvements available at odd primes after the second digit. -/
namespace PrimeFactors.PrimePowerRatioProduct

noncomputable def ratio (p : ℕ) : ℚ :=
  1 + (2*(p:ℚ)+4)/((p:ℚ)*((p:ℚ)^2-2*(p:ℚ)-1))

private def small : Finset ℕ := {3,5,7,11,13,17,19,23}
private def oddFrom (i : ℕ) := 2*i+25

private theorem tail_factor (p : ℕ) (large : 25 ≤ p) :
    ratio p ≤ (p:ℚ)^2 / (((p:ℚ)-2)*((p:ℚ)+2)) := by
  have hp : 25 ≤ (p:ℚ) := by exact_mod_cast large
  have pos : 0 < (p:ℚ)*((p:ℚ)^2-2*p-1) :=
    mul_pos (by linarith) (by nlinarith [sq_nonneg ((p:ℚ)-2)])
  have other : 0 < ((p:ℚ)-2)*(p+2) := mul_pos (by linarith) (by linarith)
  unfold ratio
  rw [show 1+(2*(p:ℚ)+4)/((p:ℚ)*((p:ℚ)^2-2*p-1)) =
    ((p:ℚ)*((p:ℚ)^2-2*p-1)+(2*p+4))/(p*((p:ℚ)^2-2*p-1)) by
      conv_rhs => rw [add_div,div_self pos.ne']]
  apply (div_le_div_iff₀ pos other).mpr
  nlinarith [mul_nonneg (show 0≤(p:ℚ)-6 by linarith) (sq_nonneg (p:ℚ))]

theorem ratio_ge_one (p : ℕ) (large : 3 ≤ p) : 1 ≤ ratio p := by
  have hp : 3 ≤ (p:ℚ) := by exact_mod_cast large
  unfold ratio
  have product := mul_nonneg (show 0 ≤ (p:ℚ)-3 by linarith) (show 0 ≤ (p:ℚ)+1 by linarith)
  have d : 0 ≤ (p:ℚ)*((p:ℚ)^2-2*p-1) :=
    mul_nonneg (by linarith) (by nlinarith)
  linarith [div_nonneg (show 0≤2*(p:ℚ)+4 by linarith) d]

private noncomputable def chosen (S : Finset ℕ) (p : ℕ) : ℚ := if p ∈ S then ratio p else 1

private theorem chosen_bounds (S : Finset ℕ) {p : ℕ} (hp : 3≤p) :
    0 ≤ chosen S p ∧ chosen S p ≤ ratio p := by
  have one := ratio_ge_one p hp
  unfold chosen
  split_ifs <;> constructor <;> linarith

private theorem tail_bound (S : Finset ℕ) (k : ℕ) :
    (∏ i ∈ Finset.range k, chosen S (oddFrom i)) ≤
      (25/23 : ℚ)*((2*(k:ℚ)+23)/(2*k+25)) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.prod_range_succ]
    have hp : 25 ≤ oddFrom k := by unfold oddFrom; omega
    obtain ⟨low,upper⟩ := chosen_bounds S (by omega : 3≤oddFrom k)
    have step := mul_le_mul ih (upper.trans (tail_factor _ hp)) low
      (show (0:ℚ) ≤ 25/23*((2*(k:ℚ)+23)/(2*k+25)) by positivity)
    refine step.trans_eq ?_
    simp only [oddFrom,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    rw [show 2*(k:ℚ)+25-2 = 2*k+23 by ring,
      show 2*((k:ℚ)+1)+23 = 2*k+25 by ring, show 2*((k:ℚ)+1)+25 = 2*k+25+2 by ring]
    field_simp [show 2*(k:ℚ)+23 ≠ 0 by positivity, show 2*(k:ℚ)+25 ≠ 0 by positivity,
      show 2*(k:ℚ)+25+2 ≠ 0 by positivity]
    ring

/-- This applies to every finite selection, with no assumption on its largest prime. -/
theorem product_lt_four (S : Finset ℕ) (primes : ∀ p∈S, p.Prime ∧ p≠2) :
    (∏ p ∈ S, ratio p) < 4 := by
  let k := S.sup id + 1
  let tail := (Finset.range k).image oddFrom
  have small_bound : ∀ p ∈ small, 3≤p ∧ p<25 := by decide +kernel
  have cover : S ⊆ small ∪ tail := by
    intro p hp
    obtain ⟨prime,odd⟩ := primes p hp
    rcases lt_or_ge p 25 with small_p | big
    · apply Finset.mem_union_left
      have catalog : ∀ x : Fin 25, x.val.Prime → x.val≠2 → x.val∈small := by decide +kernel
      exact catalog ⟨p,small_p⟩ prime odd
    · apply Finset.mem_union_right
      obtain ⟨j,hj⟩ := prime.odd_of_ne_two odd
      have limit : p ≤ S.sup id := Finset.le_sup (f:=id) hp
      exact Finset.mem_image.mpr ⟨(p-25)/2,Finset.mem_range.mpr (by dsimp [k]; omega),
        by unfold oddFrom; omega⟩
  have disjoint : Disjoint small tail := by
    apply Finset.disjoint_left.mpr
    intro p mem other
    obtain ⟨i,_,e⟩ := Finset.mem_image.mp other
    have := (small_bound p mem).2
    unfold oddFrom at e
    omega
  have extend : (∏ p ∈ S, ratio p) = ∏ p ∈ small ∪ tail, chosen S p := by
    calc
      _ = ∏ p ∈ S, chosen S p := Finset.prod_congr rfl (fun p hp => by simp [chosen,hp])
      _ = _ := Finset.prod_subset cover (fun p _ hp => by simp [chosen,hp])
  rw [extend,Finset.prod_union disjoint,Finset.prod_image (fun i _ j _ h => by unfold oddFrom at h; omega)]
  have first : (∏ p ∈ small, chosen S p) ≤ ∏ p ∈ small, ratio p :=
    Finset.prod_le_prod (fun p hp => (chosen_bounds S (small_bound p hp).1).1)
      (fun p hp => (chosen_bounds S (small_bound p hp).1).2)
  have initial : (∏ p ∈ small, ratio p)*(25/23 : ℚ) < 4 := by decide +kernel
  have frac : (2*(k:ℚ)+23)/(2*k+25) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  exact (mul_le_mul first ((tail_bound S k).trans ((mul_le_mul_of_nonneg_left frac (by norm_num)).trans_eq
    (mul_one _))) (Finset.prod_nonneg (fun i _ => (chosen_bounds S (p:=oddFrom i)
      (by unfold oddFrom; omega)).1)) (Finset.prod_nonneg (fun p hp =>
      le_trans (by norm_num) (ratio_ge_one p (small_bound p hp).1)))).trans_lt initial

end PrimeFactors.PrimePowerRatioProduct
