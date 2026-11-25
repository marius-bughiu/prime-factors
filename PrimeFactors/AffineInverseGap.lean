import PrimeFactors.InverseGapPopulation
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq

/-! Population of pairs passing a modular-inverse resultant test whose sign parameter
is an integer polynomial in the public product. The quantitative results use affine polynomials. -/

namespace PrimeFactors.AffineInverseGap

open Finset InverseGapPopulation

set_option exponentiation.threshold 230000

/-- The public test permits every possible accidental agreement with the true sum. -/
def Hit (p q : ℕ) (e : ℤ) : Prop :=
  ((p:ℤ)+q) ∣ ((p:ℤ)*q+1)^2 + (p:ℤ)*q*e^2

private theorem hit_congr {p q : ℕ} {e g : ℤ}
    (eg : e ≡ g [ZMOD (p:ℤ)+q]) : Hit p q e ↔ Hit p q g := by
  have eq := ((eg.pow 2).mul_left ((p:ℤ)*q)).add_left (((p:ℤ)*q+1)^2)
  simp only [Hit, ←Int.modEq_zero_iff_dvd]
  exact ⟨fun he => eq.symm.trans he, fun hg => eq.trans hg⟩

private theorem replace_input (p q : ℕ) :
    (p:ℤ)*q ≡ -(p:ℤ)^2 [ZMOD (p:ℤ)+q] := by
  apply Int.modEq_iff_dvd.mpr
  exact ⟨-(p:ℤ),by ring⟩

/-- At every successful sum one can substitute -p² for the full input in *any*
fixed integer polynomial. The resulting divisor row is independent of q. -/
theorem polynomial_row (f : Polynomial ℤ) {p q : ℕ} (hit : Hit p q (f.eval ((p:ℤ)*q))) :
    p+q ∣ looseValue p (f.eval (-(p:ℤ)^2)) := by
  apply loose_divisor
  apply (hit_congr ?_).mp hit
  exact Int.modEq_iff_dvd.mpr ((Int.modEq_iff_dvd.mp (replace_input p q)).trans
    (Polynomial.sub_dvd_eval_sub _ _ f))

def affine (a b n : ℤ) : ℤ := a*n+b

theorem affine_row (a b : ℤ) {p q : ℕ} (hit : Hit p q (affine a b ((p:ℤ)*q))) :
    p+q ∣ looseValue p (affine a b (-(p:ℤ)^2)) :=
  loose_divisor ((hit_congr (((replace_input p q).mul_left a).add_right b)).mp hit)

/-- Every nonzero slope in the 40-bit box overshoots the magnitude of the actual
inverse gap on the full-size inputs, although its divisibility test can still succeed. -/
theorem actual_gap_too_small {n a b : ℤ} (large : 2^2047≤n) (nonzero : a≠0)
    (small : |b|<2^40) : 2^1024≤|affine a b n| := by
  have nh : 0≤n := le_trans (by positivity) large
  have ah := abs_pos.mpr nonzero
  have atLeast : n ≤ |a| * n := by
    simpa using mul_le_mul_of_nonneg_right (show 1 ≤ |a| by omega) nh
  have triangle : |affine a b n + -b| ≤ |affine a b n| + |-b| := abs_add_le _ _
  rw [show affine a b n + -b=a*n by unfold affine; ring,abs_mul,abs_of_nonneg nh,abs_neg] at triangle
  have wide : (2:ℤ)^1024 + 2^40 < 2^2047 := by decide +kernel
  omega

/-- Reducing the output modulo an unrelated modulus can change it modulo the
unknown sum. A small fixed output range may still be handled by a fixed-list bound. -/
theorem remainder_example :
    (15:ℤ)%11=4 ∧ (-(3:ℤ)^2)%11=2 ∧ Hit 3 5 (15%11) ∧ ¬Hit 3 5 ((-(3:ℤ)^2)%11) := by
  unfold Hit
  decide +kernel

private theorem value_pos {p : ℕ} (hp : 1<p) (e : ℤ) : 0<value p e := by
  apply Int.natAbs_pos.mpr
  intro eq
  have d : (p:ℤ) ∣ 1 := ⟨(p:ℤ)+e,by nlinarith only [eq]⟩
  have d' : p ∣ 1 := by exact_mod_cast d
  exact (not_le_of_gt hp) (Nat.le_of_dvd (by decide) d')

private theorem magnitude {p U C a b : ℤ} (pos : 1<p) (upper : p<U) (cp : 0<C)
    (ha : |a|≤C) (hb : |b|≤C) :
    |(p^2-1)^2-(p*affine a b (-p^2))^2| < (C*U^3)^2 := by
  have pp : 0<p := by omega
  have up : 0<U := by omega
  have coarse : p^2+1≤U^2 := by
    have h := mul_self_le_mul_self (show 0≤p+1 by omega) (show p+1≤U by omega)
    nlinarith only [h, pp]
  have g : |affine a b (-p^2)| ≤ C*U^2 := calc
    _ ≤ |a*(-p^2)| + |b| := abs_add_le _ _
    _ = |a| *p^2+|b| := by rw [abs_mul,abs_neg,abs_of_nonneg (sq_nonneg p)]
    _ ≤ C*p^2+C := add_le_add (mul_le_mul_of_nonneg_right ha (sq_nonneg _)) hb
    _ = C*(p^2+1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left coarse cp.le
  have pg : |p*affine a b (-p^2)| < C*U^3 := calc
    _ ≤ p*(C*U^2) := by rw [abs_mul,abs_of_pos pp]; gcongr
    _ < U*(C*U^2) := by gcongr
    _ = _ := by ring
  have ps : |p^2-1| < C*U^3 := by
    rw [abs_of_nonneg (by nlinarith only [pos, sq_nonneg (p-1)] : 0≤p^2-1)]
    have increase := mul_le_mul_of_nonneg_right (show 1≤U by omega) (sq_nonneg U)
    have mult := mul_le_mul_of_nonneg_right (show 1≤C by omega) (by positivity : 0≤U^3)
    nlinarith only [coarse,increase,mult]
  have a2 := mul_self_lt_mul_self (abs_nonneg _) ps
  have b2 := mul_self_lt_mul_self (abs_nonneg _) pg
  rw [←sq, sq_abs] at a2 b2
  apply abs_lt.mpr
  constructor <;> nlinarith only [a2,b2,sq_nonneg (p^2-1),sq_nonneg (p*affine a b (-p^2))]

/-- The successful sum divides a *nonzero* bounded integer for each fixed p,a,b. -/
theorem row_size {p t : ℕ} {a b : ℤ} (pos : 1<p) (small : p<2^1024)
    (ha : |a|≤2^t) (hb : |b|≤2^t) :
    0<looseValue p (affine a b (-(p:ℤ)^2)) ∧
    looseValue p (affine a b (-(p:ℤ)^2)) < 2^(6144+2*t) := by
  let g := affine a b (-(p:ℤ)^2)
  refine ⟨Nat.mul_pos (value_pos pos g) (value_pos pos (-g)),?_⟩
  have exactRow : (looseValue p g : ℤ)=|((p:ℤ)^2-1)^2-((p:ℤ)*g)^2| := by
    simp only [looseValue,value,Nat.cast_mul,Int.natCast_natAbs,←abs_mul]
    congr 1
    ring
  have h := magnitude (p:=(p:ℤ)) (U:=(2:ℤ)^1024) (C:=(2:ℤ)^t)
    (by exact_mod_cast pos) (by exact_mod_cast small) (by positivity) ha hb
  have size : (((2:ℤ)^t)*((2:ℤ)^1024)^3)^2 = 2^(6144+2*t) := by
    rw [mul_pow,←pow_mul,←pow_mul,←pow_mul,←pow_add]
    congr 1
    omega
  rw [size] at h
  exact_mod_cast (show (looseValue p g : ℤ)<2^(6144+2*t) by rw [exactRow]; exact h)

/-- The algorithm can choose coefficients after seeing N. All allowed choices are
included in this union, even when the choice function is computationally unbounded. -/
def Admits (pairs : Finset (ℕ × ℕ)) (first : Finset ℕ) (menu : Finset (ℤ × ℤ)) : Prop :=
  ∀ x ∈ pairs, x.1 ∈ first ∧
    ∃ c ∈ menu, Hit x.1 x.2 (affine c.1 c.2 ((x.1:ℤ)*x.2))

def rowValue (p : ℕ) (c : ℤ × ℤ) := looseValue p (affine c.1 c.2 (-(p:ℤ)^2))

theorem row_count {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {menu : Finset (ℤ × ℤ)}
    (good : ∀ p∈first, 1<p) (cover : Admits pairs first menu) :
    pairs.card ≤ ∑ p ∈ first, ∑ c ∈ menu, (rowValue p c).divisors.card := by
  classical
  let covered (p : ℕ) (c : ℤ × ℤ) := (rowValue p c).divisors.image fun d => (p,d-p)
  have inside : pairs ⊆ first.biUnion (fun p => menu.biUnion (covered p)) := by
    intro x hx
    obtain ⟨pIn,c,hc,hit⟩ := cover x hx
    have pos : 0<rowValue x.1 c := Nat.mul_pos (value_pos (good _ pIn) _) (value_pos (good _ pIn) _)
    exact mem_biUnion.mpr ⟨_,pIn,mem_biUnion.mpr ⟨_,hc,mem_image.mpr
      ⟨x.1+x.2,Nat.mem_divisors.mpr ⟨affine_row c.1 c.2 hit,pos.ne'⟩,by simp⟩⟩⟩
  exact (card_le_card inside).trans (card_biUnion_le.trans
    (sum_le_sum fun _ _ => card_biUnion_le.trans (sum_le_sum fun _ _ => card_image_le)))

private theorem menu_card {menu : Finset (ℤ × ℤ)} {t : ℕ}
    (small : ∀ c∈menu, |c.1|<2^t ∧ |c.2|<2^t) : menu.card ≤ 2^(2*t+2) := by
  let box := Ioo (-((2:ℤ)^t)) (2^t)
  have inside : menu ⊆ box ×ˢ box := by
    intro c hc
    obtain ⟨a,b⟩ := small c hc
    exact mem_product.mpr ⟨mem_Ioo.mpr (abs_lt.mp a),mem_Ioo.mpr (abs_lt.mp b)⟩
  have bound : box.card ≤ 2^(t+1) := by
    change (Ioo _ _).card ≤ _
    rw [Int.card_Ioo, pow_succ]
    have p : (0:ℤ) < 2^t := by positivity
    have h := Int.toNat_of_nonneg (show 0≤(2:ℤ)^t-(-(2^t))-1 by omega)
    exact_mod_cast (show (((2:ℤ)^t-(-(2^t))-1).toNat:ℤ) ≤ (2:ℤ)^t*2 by rw [h]; omega)
  have h : menu.card ≤ 2^(t+1)*2^(t+1) := (card_le_card inside).trans (by
    rw [card_product]; exact Nat.mul_le_mul bound bound)
  simpa only [←pow_add, show t+1+(t+1)=2*t+2 by omega] using h

private theorem fraction {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {menu : Finset (ℤ × ℤ)}
    {population t bits cap : ℕ} (base : 2^1023*first.card < 44331*population)
    (primes : ∀ p∈first, 1<p ∧ p<2^1024)
    (coef : ∀ c∈menu, |c.1|<2^t ∧ |c.2|<2^t) (has : menu.Nonempty)
    (cover : Admits pairs first menu) (capPos : 0<cap)
    (size : 2^(14882+32*(6144+2*t)) ≤ cap^336)
    (scale : 44331*(2^bits*cap) ≤ 2^1023) :
    2^bits*pairs.card < menu.card*population := by
  have num : pairs.card ≤ first.card*(menu.card*cap) := calc
    _ ≤ _ := row_count (fun p hp => (primes p hp).1) cover
    _ ≤ ∑ _p ∈ first, ∑ _c ∈ menu, cap := by
      apply sum_le_sum
      intro p hp
      apply sum_le_sum
      intro c hc
      obtain ⟨pos,small⟩ := row_size (primes p hp).1 (primes p hp).2
        (coef c hc).1.le (coef c hc).2.le
      apply (Nat.pow_le_pow_iff_left (by decide : 336≠0)).mp
      exact (UniformDivisorCount.below_power_two pos small).le.trans size
    _ = _ := by simp [nsmul_eq_mul]
  apply Nat.lt_of_mul_lt_mul_left (a:=2^1023)
  calc
    2^1023*(2^bits*pairs.card) ≤ 2^1023*(2^bits*(first.card*(menu.card*cap))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ num)
    _ = (2^1023*first.card)*(2^bits*(menu.card*cap)) := by ac_rfl
    _ < (44331*population)*(2^bits*(menu.card*cap)) := Nat.mul_lt_mul_of_pos_right base
      (Nat.mul_pos (by positivity) (Nat.mul_pos (card_pos.mpr has) capPos))
    _ = (44331*(2^bits*cap))*(menu.card*population) := by ac_rfl
    _ ≤ 2^1023*(menu.card*population) := Nat.mul_le_mul_right _ scale

private theorem adaptive {g total m t bits : ℕ} (small : m≤2^(2*t+2))
    (h : 2^(bits+(2*t+2))*g<m*total) : 2^bits*g<total := by
  apply Nat.lt_of_mul_lt_mul_left (a:=2^(2*t+2))
  rw [←Nat.mul_assoc,←pow_add,Nat.add_comm (2*t+2) bits]
  exact h.trans_le (Nat.mul_le_mul_right total small)

/-- With 16-bit coefficient magnitudes, a fixed rule covers less than one in 2^375;
an arbitrary adaptive choice from the entire coefficient box covers less than one in 2^341. -/
theorem fraction16 {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {menu : Finset (ℤ × ℤ)}
    {population : ℕ} (base : 2^1023*first.card < 44331*population)
    (primes : ∀ p∈first, 1<p ∧ p<2^1024)
    (coef : ∀ c∈menu, |c.1|<2^16 ∧ |c.2|<2^16) (has : menu.Nonempty)
    (cover : Admits pairs first menu) :
    2^375*pairs.card < menu.card*population ∧ 2^341*pairs.card<population := by
  have h := fraction (t:=16) (bits:=375) (cap:=45*2^627) base primes coef has cover
    (by positivity) (by decide +kernel) (by decide +kernel)
  exact ⟨h,adaptive (bits:=341) (menu_card coef) h⟩

/-- The 40-bit coefficient box permits almost 2^82 choices, even input-dependent.
Each choice receives every divisor of its resultant at zero cost. -/
theorem fraction40 {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {menu : Finset (ℤ × ℤ)}
    {population : ℕ} (base : 2^1023*first.card < 44331*population)
    (primes : ∀ p∈first, 1<p ∧ p<2^1024)
    (coef : ∀ c∈menu, |c.1|<2^40 ∧ |c.2|<2^40) (has : menu.Nonempty)
    (cover : Admits pairs first menu) :
    2^370*pairs.card < menu.card*population ∧ 2^288*pairs.card<population := by
  have h := fraction (t:=40) (bits:=370) (cap:=17*2^633) base primes coef has cover
    (by positivity) (by decide +kernel) (by decide +kernel)
  exact ⟨h,adaptive (bits:=288) (menu_card coef) h⟩

end PrimeFactors.AffineInverseGap
