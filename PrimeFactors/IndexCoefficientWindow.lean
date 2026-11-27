import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-!
# Isolating an index coefficient with a positive frequency window

Csirik, Wetherell and Zieve, *On the genera of X₀(N)*, §§2 and 5,
https://arxiv.org/pdf/math/0006096, express the normalized index at n as the sum of
1/d over squarefree divisors d of n. We remove all divisors through Y, and study
the remaining coefficient at N using the nonnegative sinc-squared kernel on Re(s)=2.

A nearby multiple of a prime above the cutoff creates a lower bound on the total bias.
The theorems describe weighted coefficient sums. The triangular Fourier transform
identifying the continuous average with that sum is given in the companion note.
-/
namespace PrimeFactors.IndexCoefficientWindow

/-- The surviving squarefree divisor terms in the normalized subgroup index, after removing
    the contribution of every divisor at most Y. -/
noncomputable def terms (Y n : ℕ) := n.divisors.filter (fun d => Y < d ∧ Squarefree d)

noncomputable def coefficient (Y n : ℕ) : ℝ := ∑ d ∈ terms Y n, 1/(d : ℝ)

theorem coefficient_nonneg (Y n : ℕ) : 0 ≤ coefficient Y n :=
  Finset.sum_nonneg (fun i _ => by positivity)

theorem prime_term {Y n R : ℕ} (n0 : 0 < n) (prime : R.Prime) (cut : Y < R)
    (divides : R ∣ n) : 1/(R:ℝ) ≤ coefficient Y n := by
  apply Finset.single_le_sum (f := fun i : ℕ => 1/(i:ℝ)) (fun i _ => by positivity)
  exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨divides, n0.ne'⟩,
    cut, prime.squarefree⟩

/-- For a product of distinct primes the cutoff leaves exactly three divisor terms. -/
theorem semiprime {Y p q : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (one : 1≤Y) (cut : Y<p) :
    coefficient Y (p*q) = ((p:ℝ)+q+1)/((p:ℝ)*q) := by
  have raw : (p*q).divisors = {1,p,q,p*q} := by
    ext z
    rw [Nat.divisors_mul, hp.divisors, hq.divisors, Finset.mem_mul]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
    · rintro (h|h|h|h) <;> subst z
      · exact ⟨1, Or.inl rfl, 1, Or.inl rfl, one_mul _⟩
      · exact ⟨p, Or.inr rfl, 1, Or.inl rfl, mul_one _⟩
      · exact ⟨1, Or.inl rfl, q, Or.inr rfl, one_mul _⟩
      · exact ⟨p, Or.inr rfl, q, Or.inr rfl, rfl⟩
  have ppq : p<p*q := by nlinarith [hp.two_le, hq.two_le, Nat.mul_le_mul_left p hq.two_le]
  have qpq : q<p*q := by nlinarith [hq.two_le, Nat.mul_le_mul_right q hp.two_le]
  have pqSq := (Nat.squarefree_mul ((Nat.coprime_primes hp hq).mpr lt.ne)).mpr ⟨hp.squarefree,hq.squarefree⟩
  have inds : terms Y (p*q) = {p,q,p*q} := by
    simp [terms, raw, Finset.filter_insert, Finset.filter_singleton, not_lt_of_ge one, cut, cut.trans lt, cut.trans ppq,
      hp.squarefree, hq.squarefree, pqSq]
  rw [coefficient, inds]
  simp [lt.ne, ppq.ne, qpq.ne]
  field_simp [hp.ne_zero,hq.ne_zero]
  ring

def firstMultiple (N R : ℕ) := R*(N/R+1)

/-- This multiple lies in the right half-open search range (N, N+R]. -/
theorem firstMultiple_spec (N : ℕ) {R : ℕ} (pos : 0 < R) :
    N < firstMultiple N R ∧ firstMultiple N R ≤ N+R ∧ R ∣ firstMultiple N R := by
  refine ⟨Nat.lt_mul_div_succ N pos, ?_, dvd_mul_right _ _⟩
  unfold firstMultiple
  rw [Nat.mul_add, Nat.mul_one]
  exact Nat.add_le_add_right (Nat.mul_div_le N R) R

noncomputable def sinc (x : ℝ) := if x = 0 then 1 else Real.sin x/x

theorem sinc_at_least {x : ℝ} (lo : 0 ≤ x) (hi : x ≤ 1/2) : 15/16 ≤ sinc x := by
  rcases lo.eq_or_lt with zero | pos
  · simp [← zero, sinc]
    norm_num
  unfold sinc
  rw [if_neg pos.ne', le_div_iff₀ pos]
  have h := Real.sin_gt_sub_cube pos (by linarith)
  have sq : x^2 ≤ 1/4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1/2-x) (by linarith : 0 ≤ 1/2+x)]
  nlinarith [mul_le_mul_of_nonneg_right sq lo]

/-- The nonnegative coefficient kernel of the triangular vertical frequency window;
    the square here is on the sinc, separately from the Dirichlet weight. -/
noncomputable def weight (T : ℝ) (N m : ℕ) :=
  ((N:ℝ)/m)^2 * sinc (T * Real.log ((m:ℝ)/N) / 2)^2

theorem weight_nonneg (T : ℝ) (N m : ℕ) : 0 ≤ weight T N m := by
  unfold weight
  positivity

theorem weight_self {N : ℕ} (n0 : 0<N) (T : ℝ) : weight T N N = 1 := by
  simp [weight, sinc, show (N:ℝ)≠0 by exact_mod_cast n0.ne']

private theorem phase_bounds {T : ℝ} {N m H : ℕ} (n0 : 0<N) (nearby : N≤m)
    (offset : m≤N+H) (height0 : 0≤T) (height : T*H≤N) :
    0 ≤ T*Real.log ((m:ℝ)/N)/2 ∧ T*Real.log ((m:ℝ)/N)/2 ≤ 1/2 := by
  have np : 0 < (N:ℝ) := by exact_mod_cast n0
  have nm : (N:ℝ) ≤ m := by exact_mod_cast nearby
  have mp : 0 < (m:ℝ) := np.trans_le nm
  have off : (m:ℝ) ≤ (N:ℝ)+H := by exact_mod_cast offset
  have lg0 : 0 ≤ Real.log ((m:ℝ)/N) := Real.log_nonneg ((one_le_div np).mpr nm)
  have lg : Real.log ((m:ℝ)/N) ≤ H/N := by
    apply (Real.log_le_sub_one_of_pos (div_pos mp np)).trans
    rw [sub_le_iff_le_add]
    calc
      (m:ℝ)/N ≤ ((N:ℝ)+H)/N := div_le_div_of_nonneg_right off np.le
      _ = H/N+1 := by field_simp [np.ne']; ring
  have unit : T*Real.log ((m:ℝ)/N) ≤ 1 := by
    calc
      _ ≤ T*((H:ℝ)/N) := mul_le_mul_of_nonneg_left lg height0
      _ = (T*H)/N := (mul_div_assoc ..).symm
      _ ≤ 1 := (div_le_one np).mpr height
  exact ⟨by positivity, by linarith⟩

/-- If the neighbor is within H and T H ≤ N, its normalized weight exceeds one half. -/
theorem close_weight {T : ℝ} {N m H : ℕ} (n0 : 0<N) (nearby : N≤m)
    (offset : m≤N+H) (near : 4*H≤N) (height0 : 0≤T) (height : T*H≤N) :
    1/2 < weight T N m := by
  have np : 0 < (N:ℝ) := by exact_mod_cast n0
  have nm : (N:ℝ) ≤ m := by exact_mod_cast nearby
  have mp : 0 < (m:ℝ) := np.trans_le nm
  have off : (m:ℝ) ≤ (N:ℝ)+H := by exact_mod_cast offset
  have small : 4*(H:ℝ) ≤ (N:ℝ) := by exact_mod_cast near
  have rat : (4:ℝ)/5 ≤ N/m := (le_div_iff₀ mp).mpr (by linarith)
  have ⟨lo,hi⟩ := phase_bounds n0 nearby offset height0 height
  have sincLo := sinc_at_least lo hi
  have prod := mul_le_mul (pow_le_pow_left₀ (by norm_num) rat 2)
    (pow_le_pow_left₀ (by norm_num) sincLo 2) (sq_nonneg _) (sq_nonneg _)
  exact lt_of_lt_of_le (by norm_num) prod

theorem one_neighbor {T : ℝ} {Y N R m H : ℕ} (n0 : 0<N) (prime : R.Prime) (cut : Y<R)
    (nearby : N<m) (offset : m≤N+H) (near : 4*H≤N) (divides : R∣m)
    (height0 : 0≤T) (height : T*H≤N) :
    1/(2*(R:ℝ)) < coefficient Y m * weight T N m := by
  have b := prime_term (n0.trans nearby) prime cut divides
  have w := close_weight n0 nearby.le offset near height0 height
  have rp : 0 < (R:ℝ) := by exact_mod_cast prime.pos
  calc
    _ = (1/(R:ℝ))*(1/2) := by ring
    _ < (1/(R:ℝ))*weight T N m := mul_lt_mul_of_pos_left w (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right b (weight_nonneg ..)

noncomputable def estimate (Y N : ℕ) (T : ℝ) (s : Finset ℕ) :=
  ∑ m ∈ s, coefficient Y m * weight T N m

theorem finite_bias_of_neighbor {Y N R m H : ℕ} {T : ℝ} {s : Finset ℕ} (n0 : 0<N)
    (prime : R.Prime) (cut : Y<R) (nearby : N<m) (offset : m≤N+H) (near : 4*H≤N)
    (divides : R∣m) (height0 : 0≤T) (height : T*H≤N) (target : N ∈ s) (neighbor : m ∈ s) :
    coefficient Y N + 1/(2*(R:ℝ)) < estimate Y N T s := by
  have bump := one_neighbor n0 prime cut nearby offset near divides height0 height
  have mem : m ∈ s.erase N := Finset.mem_erase.mpr ⟨nearby.ne', neighbor⟩
  have subtotal := Finset.single_le_sum (s := s.erase N)
    (f := fun m => coefficient Y m * weight T N m)
    (fun i _ => mul_nonneg (coefficient_nonneg ..) (weight_nonneg ..)) mem
  unfold estimate
  rw [← Finset.sum_erase_add _ _ target, weight_self n0, mul_one]
  exact (add_lt_add_left (bump.trans_le subtotal) _).trans_eq (add_comm ..)

theorem finite_bias {Y N R : ℕ} {T : ℝ} {s : Finset ℕ} (n0 : 0<N)
    (prime : R.Prime) (cut : Y<R) (near : 4*R≤N) (height0 : 0≤T) (height : T*R≤N)
    (target : N ∈ s) (neighbor : firstMultiple N R ∈ s) :
    coefficient Y N + 1/(2*(R:ℝ)) < estimate Y N T s := by
  obtain ⟨strict,offset,divides⟩ := firstMultiple_spec N prime.pos
  exact finite_bias_of_neighbor n0 prime cut strict offset near divides height0 height target neighbor

/-- A convergent majorant for the actual surviving coefficients on Re(s)=2. -/
theorem coefficient_sqrt (Y m : ℕ) : coefficient Y m ≤ 2*Real.sqrt m := by
  rcases Nat.eq_zero_or_pos m with rfl|mp
  · simp [coefficient, terms]
  have sub : terms Y m ⊆ Finset.Icc 1 m := by
    intro d h
    have divisor := (Finset.mem_filter.mp h).1
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors divisor, Nat.le_of_dvd mp (Nat.mem_divisors.mp divisor).1⟩
  have upper : coefficient Y m ≤ (harmonic m : ℝ) := by
    unfold coefficient
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    exact Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
  have rt : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast mp)
  have logbound := Real.log_le_sub_one_of_pos rt
  rw [Real.log_sqrt (by positivity : 0≤(m:ℝ))] at logbound
  linarith [harmonic_le_one_add_log m]

theorem sinc_sq_le_one (x : ℝ) : sinc x ^ 2 ≤ 1 := by
  by_cases z : x = 0
  · simp [sinc, z]
  have habs := Real.abs_sin_le_abs (x:=x)
  have le1 : |sinc x| ≤ 1 := by
    rw [sinc, if_neg z, abs_div, div_le_one (abs_pos.mpr z)]
    exact habs
  nlinarith [sq_abs (sinc x), mul_nonneg (sub_nonneg.mpr le1) (by positivity : 0≤1+|sinc x|)]

theorem summable (Y N : ℕ) (T : ℝ) : Summable (fun m : ℕ => coefficient Y m * weight T N m) := by
  have major := (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1:ℝ)<3/2)).mul_left (2*(N:ℝ)^2)
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (coefficient_nonneg ..) (weight_nonneg ..)) ?_ major
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | mp
  · simp [coefficient, terms, weight]
  have castpos : 0 < (m:ℝ) := by exact_mod_cast mp
  have rt : 0 < Real.sqrt m := Real.sqrt_pos.mpr castpos
  have poweq : (m:ℝ)^(3/2:ℝ) = m*Real.sqrt m := by
    rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add castpos, Real.rpow_one, ←Real.sqrt_eq_rpow]
  have weightBound : weight T N m ≤ ((N:ℝ)/m)^2 := by
    unfold weight
    exact (mul_le_mul_of_nonneg_left (sinc_sq_le_one _) (sq_nonneg _)).trans_eq (mul_one _)
  apply (mul_le_mul (coefficient_sqrt Y m) weightBound (weight_nonneg ..) (by positivity)).trans
  dsimp
  rw [poweq]
  apply le_of_eq
  field_simp [castpos.ne',rt.ne']
  ring_nf
  rw [Real.sq_sqrt castpos.le]
  ring

theorem series_bias_of_neighbor {Y N R m H : ℕ} {T : ℝ} (n0 : 0<N)
    (prime : R.Prime) (cut : Y<R) (nearby : N<m) (offset : m≤N+H) (near : 4*H≤N)
    (divides : R∣m) (height0 : 0≤T) (height : T*H≤N) :
    coefficient Y N + 1/(2*(R:ℝ)) < ∑' k : ℕ, coefficient Y k * weight T N k := by
  let s : Finset ℕ := {N,m}
  have hit := finite_bias_of_neighbor (s:=s) n0 prime cut nearby offset near divides height0 height
    (by simp [s]) (by simp [s])
  exact hit.trans_le (Summable.sum_le_tsum s
    (fun k _ => mul_nonneg (coefficient_nonneg ..) (weight_nonneg ..)) (summable Y N T))

/-- Unconditional bias of the whole convergent series, using the next multiple of R. -/
theorem series_bias {Y N R : ℕ} {T : ℝ} (n0 : 0<N) (prime : R.Prime) (cut : Y<R)
    (near : 4*R≤N) (height0 : 0≤T) (height : T*R≤N) :
    coefficient Y N + 1/(2*(R:ℝ)) < ∑' m : ℕ, coefficient Y m * weight T N m := by
  obtain ⟨strict,offset,divides⟩ := firstMultiple_spec N prime.pos
  exact series_bias_of_neighbor n0 prime cut strict offset near divides height0 height

/-- If the cutoff and height are both small, some prime between Y and 2Y forces a
    positive bias. Even granting exact evaluation of the divisor correction leaves this term. -/
theorem cutoff_height {Y N : ℕ} {T : ℝ} (pos : 0<Y) (big : 8*Y≤N)
    (lo : 0≤T) (small : 2*T*Y≤N) :
    coefficient Y N + 1/(4*(Y:ℝ)) < ∑' k : ℕ, coefficient Y k * weight T N k := by
  obtain ⟨R,prime,cut,bound⟩ := Nat.exists_prime_lt_and_le_two_mul Y pos.ne'
  have bound' : (R:ℝ) ≤ 2*(Y:ℝ) := by exact_mod_cast bound
  have h := series_bias (N:=N) (Y:=Y) (T:=T) (by omega) prime cut (by omega) lo
    (by nlinarith [mul_le_mul_of_nonneg_left bound' lo])
  have rp : 0<(R:ℝ) := by exact_mod_cast prime.pos
  have yp : 0<(Y:ℝ) := by exact_mod_cast pos
  have denom : 1/(4*(Y:ℝ)) ≤ 1/(2*(R:ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  exact (add_le_add_left denom _).trans_lt h

/-- The error is above the largest project half-grid for every full-width target at these heights. -/
theorem full_size {N : ℕ} {T : ℝ} (big : 2^2047≤N) (lo : 0≤T) (small : T≤2^2037) :
    coefficient 1000 N + 12/(N:ℝ) < ∑' k : ℕ, coefficient 1000 k * weight T N k := by
  have r : (1009:ℕ).Prime := by norm_num
  have width : 2^2047 ≤ (N:ℝ) := by exact_mod_cast big
  have eps : 12/(N:ℝ) ≤ 1/(2*1009) := by
    rw [div_le_div_iff₀ (lt_of_lt_of_le (by norm_num) width) (by norm_num)]
    linarith
  have height : T*1009 ≤ (N:ℝ) :=
    (mul_le_mul_of_nonneg_right small (by norm_num)).trans ((by norm_num : (2:ℝ)^2037*1009 ≤ 2^2047).trans width)
  have h := series_bias (N:=N) (Y:=1000) (T:=T) (by omega) r (by decide)
    ((by norm_num : 4*1009 ≤ (2:ℕ)^2047).trans big) lo (by simpa using height)
  exact (add_le_add_left eps _).trans_lt (by simpa using h)

/-- A sparse positive squared-amplitude window with arbitrary nonnegative normalized weights.
    Frequencies lie within [-1,1] before rescaling by T/2. -/
noncomputable def sparseMass {ι : Type*} (s : Finset ι) (w f : ι → ℝ) (x : ℝ) :=
  (∑ j ∈ s, w j*Real.cos (f j*x))^2 + (∑ j ∈ s, w j*Real.sin (f j*x))^2

theorem sparse_at_least {ι : Type*} {s : Finset ι} {w f : ι → ℝ} {x : ℝ}
    (nonneg : ∀ j∈s, 0≤w j) (normed : ∑ j∈s, w j=1) (band : ∀ j∈s, |f j|≤1)
    (lo : 0≤x) (hi : x≤1/2) : (7/8:ℝ)^2 ≤ sparseMass s w f x := by
  have re : 7/8 ≤ ∑ j∈s, w j*Real.cos (f j*x) := by
    calc
      (7/8:ℝ) = ∑ j∈s, w j*(7/8) := by rw [←Finset.sum_mul, normed, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (by
        have radius : |f j*x| ≤ 1/2 := by
          rw [abs_mul, abs_of_nonneg lo]
          exact ((mul_le_mul_of_nonneg_right (band j hj) lo).trans_eq (one_mul x)).trans hi
        have sq := pow_le_pow_left₀ (abs_nonneg _) radius 2
        rw [sq_abs] at sq
        linarith [Real.one_sub_sq_div_two_le_cos (x:=f j*x)]) (nonneg j hj))
  unfold sparseMass
  exact (pow_le_pow_left₀ (by norm_num) re 2).trans (le_add_of_nonneg_right (sq_nonneg _))

/-- The single-neighbor lower bound also applies to these sparse, positive windows. -/
theorem sparse_neighbor {ι : Type*} {s : Finset ι} {w f : ι → ℝ} {Y N R m H : ℕ} {T : ℝ}
    (nonneg : ∀ j∈s, 0≤w j) (normed : ∑ j∈s, w j=1) (band : ∀ j∈s, |f j|≤1)
    (n0 : 0<N) (prime : R.Prime) (cut : Y<R) (nearby : N<m) (offset : m≤N+H)
    (near : 5*H≤N) (divides : R∣m) (height0 : 0≤T) (height : T*H≤N) :
    1/(2*(R:ℝ)) < coefficient Y m *
      (((N:ℝ)/m)^2 * sparseMass s w f (T*Real.log ((m:ℝ)/N)/2)) := by
  have om : (m:ℝ) ≤ (N:ℝ)+H := by exact_mod_cast offset
  have nh : 5*(H:ℝ) ≤ N := by exact_mod_cast near
  have mp : 0<(m:ℝ) := by exact_mod_cast (n0.trans nearby)
  have rat : (5:ℝ)/6 ≤ (N:ℝ)/m := (le_div_iff₀ mp).mpr (by linarith)
  obtain ⟨phase0,phase1⟩ := phase_bounds n0 nearby.le offset height0 height
  have sm := sparse_at_least nonneg normed band phase0 phase1
  have prod := mul_le_mul (pow_le_pow_left₀ (by norm_num) rat 2) sm (sq_nonneg _) (sq_nonneg _)
  have gt := lt_of_lt_of_le (by norm_num : (1:ℝ)/2<(5/6)^2*(7/8)^2) prod
  have rp : 0<(R:ℝ) := by exact_mod_cast prime.pos
  calc
    _ = (1/(R:ℝ))*(1/2) := by ring
    _ < _ := mul_lt_mul_of_pos_left gt (by positivity : 0<1/(R:ℝ))
    _ ≤ _ := mul_le_mul_of_nonneg_right (prime_term (n0.trans nearby) prime cut divides) (by linarith)

/-- 528, the nearest multiple of 11, lies only one above the target.
    At every height up to 527 its contribution already violates the generous half-grid 12/527. -/
theorem toy : coefficient 7 527 = 49/527 ∧
    ∀ T : ℝ, 0≤T → T≤527 →
      coefficient 7 527 + 12/527 < ∑' m : ℕ, coefficient 7 m * weight T 527 m := by
  constructor
  · have eqn := semiprime (Y:=7) (p:=17) (q:=31) (by decide) (by decide) (by decide) (by decide) (by decide)
    norm_num at eqn ⊢
    exact eqn
  intro T lo hi
  have hit := series_bias_of_neighbor (Y:=7) (N:=527) (R:=11) (m:=528) (H:=1) (T:=T)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) lo (by simpa)
  linarith

end PrimeFactors.IndexCoefficientWindow
