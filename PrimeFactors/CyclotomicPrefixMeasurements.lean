import PrimeFactors.BalancedCyclotomicPrefix

/-!
# Measuring the odd coefficients of a binary cyclotomic polynomial

Moree, *Numerical semigroups, cyclotomic polynomials and Bernoulli numbers*,
Theorem 1, identifies the binary cyclotomic polynomial with the semigroup
polynomial (https://arxiv.org/pdf/1308.3972#page=2). The six-term expansion
on the short prefix is already proved in `BalancedCyclotomicPrefix`.

In a known interval `[B,2B)` containing both odd primes, the odd coefficient
positions mark precisely the two primes. This file evaluates weighted sums
over arbitrary subwindows and counts the entries in a full direct scan.
-/

namespace PrimeFactors.CyclotomicPrefixMeasurements

open Polynomial Finset

/-- Odd positions in the publicly specified interval. -/
noncomputable def odds (B : ℕ) : Finset ℕ := (Ico B (2*B)).filter (fun k => k%2=1)

/-- The same positions up to and including a supplied cutoff. -/
noncomputable def upto (B t : ℕ) : Finset ℕ := (odds B).filter (·≤t)

@[simp] theorem mem_odds {B k : ℕ} : k∈odds B ↔ B≤k ∧ k<2*B ∧ k%2=1 := by
  simp [odds, and_assoc]

@[simp] theorem mem_upto {B t k : ℕ} : k∈upto B t ↔ k∈odds B ∧ k≤t := by
  simp only [upto, mem_filter]

theorem odds_card (b : ℕ) : (odds (2*b)).card=b := by
  let f := fun i : ℕ => 2*b+2*i+1
  have eq : odds (2*b)=(range b).image f := by
    ext k
    rw [mem_odds, mem_image]
    constructor
    · rintro ⟨lo,hi,odd⟩
      refine ⟨(k-2*b)/2,mem_range.mpr (by omega),?_⟩
      dsimp [f]
      omega
    · rintro ⟨i,hi,rfl⟩
      have := mem_range.mp hi
      dsimp [f]
      omega
  rw [eq, card_image_of_injective _ (show Function.Injective f by intro i j h; dsimp [f] at h; omega),
    card_range]

theorem odd_coefficient {p q B k : ℕ} (pp : p.Prime) (qp : q.Prime) (ordered : p<q)
    (start : 3≤B) (lo : B≤p) (hk : k∈odds B) :
    (cyclotomic (p*q) ℤ).coeff k=(if k=p then 1 else 0)+(if k=q then 1 else 0) := by
  obtain ⟨kl,ku,ko⟩ := mem_odds.mp hk
  have po := Nat.odd_iff.mp (pp.odd_of_ne_two (by omega))
  have qo := Nat.odd_iff.mp (qp.odd_of_ne_two (by omega))
  rw [BalancedCyclotomicPrefix.coefficient pp qp ordered lo ku]
  simp [show k≠0 by omega, show k≠1 by omega, show k≠p+1 by omega, show k≠q+1 by omega]

/-- Any supplied odd-position measurement with arbitrary integer weights
returns the sum of the weights of the factors in that window. -/
theorem weighted {p q B : ℕ} (pp : p.Prime) (qp : q.Prime) (ordered : p<q)
    (start : 3≤B) (lo : B≤p) (J : Finset ℕ) (window : J⊆odds B) (f : ℕ→ℤ) :
    ∑ k∈J, f k*(cyclotomic (p*q) ℤ).coeff k =
      (if p∈J then f p else 0)+(if q∈J then f q else 0) := by
  calc
    _ = ∑ k∈J, ((if k=p then f k else 0)+(if k=q then f k else 0)) := by
      apply sum_congr rfl
      intro k hk
      rw [odd_coefficient pp qp ordered start lo (window hk)]
      simp only [mul_add, mul_ite, mul_one, mul_zero]
    _ = _ := by rw [sum_add_distrib]; simp

private theorem in_window {p q B : ℕ} (pp : p.Prime) (qp : q.Prime) (ordered : p<q)
    (start : 3≤B) (lo : B≤p) (hi : q<2*B) : p∈odds B ∧ q∈odds B := by
  have po := Nat.odd_iff.mp (pp.odd_of_ne_two (by omega))
  have qo := Nat.odd_iff.mp (qp.odd_of_ne_two (by omega))
  simp only [mem_odds]
  omega

private theorem roots {p q : ℕ} (ord : p<q) : p≤(p*q).sqrt ∧ (p*q).sqrt<q :=
  ⟨Nat.le_sqrt'.mpr (by rw [sq]; exact Nat.mul_le_mul_left p ord.le),
   Nat.sqrt_lt'.mpr (by rw [sq]; exact Nat.mul_lt_mul_of_pos_right ord (by omega))⟩

/-- Before the square root the odd-position cumulative measurement is one
exact threshold bit for the smaller prime. -/
theorem threshold {p q B t : ℕ} (pp : p.Prime) (qp : q.Prime) (ordered : p<q)
    (start : 3≤B) (lo : B≤p) (hi : q<2*B) (cut : t≤(p*q).sqrt) :
    ∑ k∈upto B t, (cyclotomic (p*q) ℤ).coeff k = if p≤t then 1 else 0 := by
  obtain ⟨ip,iq⟩ := in_window pp qp ordered start lo hi
  have tq := cut.trans_lt (roots ordered).2
  simpa [ip,iq,not_le.mpr tq] using
    (weighted pp qp ordered start lo (upto B t) (filter_subset _ _) (fun _ => 1))

theorem smaller_moment {p q B : ℕ} (pp : p.Prime) (qp : q.Prime) (ordered : p<q)
    (start : 3≤B) (lo : B≤p) (hi : q<2*B) :
    ∑ k∈upto B (p*q).sqrt, (k:ℤ)*(cyclotomic (p*q) ℤ).coeff k=p := by
  obtain ⟨ip,iq⟩ := in_window pp qp ordered start lo hi
  obtain ⟨hp,hq⟩ := roots ordered
  simpa [ip,iq,hp,not_le.mpr hq] using
    (weighted pp qp ordered start lo (upto B (p*q).sqrt) (filter_subset _ _) (fun k => k))

theorem sum_moment {p q B : ℕ} (pp : p.Prime) (qp : q.Prime) (ordered : p<q)
    (start : 3≤B) (lo : B≤p) (hi : q<2*B) :
    ∑ k∈odds B, (k:ℤ)*(cyclotomic (p*q) ℤ).coeff k=(p:ℤ)+q := by
  obtain ⟨ip,iq⟩ := in_window pp qp ordered start lo hi
  simpa [ip,iq] using (weighted pp qp ordered start lo (odds B) (fun _ h => h) (fun k => k))

/-- Including both negative shifts gives three finite differences for an
ordinary signed moment. The endpoint `2*B` is included to cover `q+1`. -/
theorem signed_weighted {p q B : ℕ} (pp : p.Prime) (qp : q.Prime) (ordered : p<q)
    (lo : B<p) (hi : q<2*B) (f : ℕ→ℤ) :
    ∑ k∈Icc 0 (2*B), f k*(cyclotomic (p*q) ℤ).coeff k =
      f 0-f 1+f p-f (p+1)+f q-f (q+1) := by
  have at_idx (k : ℕ) (hk : k∈Icc 0 (2*B)) : k<2*p := by
    have := (mem_Icc.mp hk).2
    omega
  calc
    _ = ∑ k∈Icc 0 (2*B), ((if k=0 then f k else 0)-(if k=1 then f k else 0)+
          (if k=p then f k else 0)-(if k=p+1 then f k else 0)+
          (if k=q then f k else 0)-(if k=q+1 then f k else 0)) := by
      apply sum_congr rfl
      intro k hk
      rw [BalancedCyclotomicPrefix.coefficient pp qp ordered le_rfl (at_idx k hk)]
      simp only [mul_sub, mul_add, mul_ite, mul_one, mul_zero]
    _ = _ := by
      simp only [sum_sub_distrib, sum_add_distrib, sum_ite_eq', mem_Icc, Nat.zero_le, true_and]
      simp [show 1≤2*B by omega, show p≤2*B by omega, show p+1≤2*B by omega,
        show q≤2*B by omega, show q+1≤2*B by omega]

/-- Raw signed mass and its first moment are constant. The second moment
recovers the sum if someone supplies its value on this prefix. -/
theorem signed_moments {p q B : ℕ} (pp : p.Prime) (qp : q.Prime) (ordered : p<q)
    (lo : B<p) (hi : q<2*B) :
    (∑ k∈Icc 0 (2*B), (cyclotomic (p*q) ℤ).coeff k)=0 ∧
    (∑ k∈Icc 0 (2*B), (k:ℤ)*(cyclotomic (p*q) ℤ).coeff k)= -3 ∧
    (∑ k∈Icc 0 (2*B), (k:ℤ)^2*(cyclotomic (p*q) ℤ).coeff k)= -2*((p:ℤ)+q)-3 := by
  refine ⟨?_,?_,?_⟩
  · simpa using signed_weighted pp qp ordered lo hi (fun _ => 1)
  · convert signed_weighted pp qp ordered lo hi (fun k => (k:ℤ)) using 1
    push_cast
    ring
  · convert signed_weighted pp qp ordered lo hi (fun k => (k:ℤ)^2) using 1
    push_cast
    ring

/-- A direct product-only evaluation at one odd position tests its gcd with N. -/
theorem gcd_read {p q B k : ℕ} (pp : p.Prime) (qp : q.Prime) (ordered : p<q)
    (start : 3≤B) (lo : B≤p) (hk : k∈odds B) :
    (cyclotomic (p*q) ℤ).coeff k=if k.gcd (p*q)=1 then 0 else 1 := by
  rw [odd_coefficient pp qp ordered start lo hk]
  obtain ⟨kl,ku,_⟩ := mem_odds.mp hk
  have divp : p∣k ↔ k=p := ⟨fun h => Nat.eq_of_dvd_of_lt_two_mul (by omega) h (by omega),
    by rintro rfl; rfl⟩
  have divq : q∣k ↔ k=q := ⟨fun h => Nat.eq_of_dvd_of_lt_two_mul (by omega) h (by omega),
    by rintro rfl; rfl⟩
  have eq : k.gcd (p*q)=1 ↔ k≠p ∧ k≠q :=
    Nat.coprime_mul_iff_right.trans (and_congr
      (Nat.coprime_comm.trans (pp.coprime_iff_not_dvd.trans divp.not))
      (Nat.coprime_comm.trans (qp.coprime_iff_not_dvd.trans divq.not)))
  rw [if_congr eq rfl rfl]
  by_cases a : k=p <;> by_cases b : k=q <;> simp_all

/-- All odd factor pairs obey a known spacing of four in their possible
sum. Absolute error strictly below two determines the sum uniquely. -/
theorem unique_nearby_sum {p q t : ℕ} (po : Odd p) (qo : Odd q)
    (legal : t%4=(p*q+1)%4) (x : ℝ) (actual : |((p+q:ℕ):ℝ)-x|<2)
    (compatible : |(t:ℝ)-x|<2) : t=p+q := by
  obtain ⟨a,rfl⟩ := po
  obtain ⟨b,rfl⟩ := qo
  have eq : (2*a+1)*(2*b+1)+1 = 4*(a*b)+(2*a+1+(2*b+1)) := by ring
  rw [eq,Nat.add_mod] at legal
  simp only [Nat.mul_mod_right, zero_add, Nat.mod_mod] at legal
  have h₁ := (abs_lt.mp actual).1
  have h₂ := (abs_lt.mp actual).2
  have h₃ := (abs_lt.mp compatible).1
  have h₄ := (abs_lt.mp compatible).2
  have left : (t:ℝ)<((2*a+1+(2*b+1):ℕ):ℝ)+4 := by linarith
  have right : ((2*a+1+(2*b+1):ℕ):ℝ)<(t:ℝ)+4 := by linarith
  have left' : t<2*a+1+(2*b+1)+4 := by exact_mod_cast left
  have right' : 2*a+1+(2*b+1)<t+4 := by exact_mod_cast right
  omega

/-- For the ordinary signed second moment the corresponding error margin
is four units, since legal sums are four apart and the moment has slope −2. -/
theorem unique_second_moment {p q B t : ℕ} (pp : p.Prime) (qp : q.Prime) (ordered : p<q)
    (start : 2≤B) (lo : B<p) (hi : q<2*B) (legal : t%4=(p*q+1)%4)
    (x : ℝ)
    (actual : |((∑ k∈Icc 0 (2*B), (k:ℤ)^2*(cyclotomic (p*q) ℤ).coeff k : ℤ):ℝ)-x|<4)
    (compatible : |-2*(t:ℝ)-3-x|<4) : t=p+q := by
  rw [(signed_moments pp qp ordered lo hi).2.2] at actual
  push_cast at actual
  apply unique_nearby_sum (pp.odd_of_ne_two (by omega)) (qp.odd_of_ne_two (by omega)) legal
    ((-x-3)/2)
  · rw [abs_lt] at actual ⊢
    push_cast
    constructor <;> linarith
  · rw [abs_lt] at compatible ⊢
    constructor <;> linarith

/-- The three odd positions are 7, 9, 11. The square-root cut includes
only 7. The signed second moment of the complete short prefix is −39. -/
theorem seventy_seven :
    (∑ k∈odds 6, (k:ℤ)*(cyclotomic 77 ℤ).coeff k)=18 ∧
    (∑ k∈upto 6 8, (k:ℤ)*(cyclotomic 77 ℤ).coeff k)=7 ∧
    (∑ k∈Icc (0:ℕ) 12, (k:ℤ)^2*(cyclotomic 77 ℤ).coeff k)= -39 := by
  have pp : Nat.Prime 7 := by decide
  have qp : Nat.Prime 11 := by decide
  exact ⟨sum_moment (B:=6) pp qp (by decide) (by decide) (by decide) (by decide),
    smaller_moment (B:=6) pp qp (by decide) (by decide) (by decide) (by decide),
    (signed_moments (B:=6) pp qp (by decide) (by decide) (by decide)).2.2⟩

end PrimeFactors.CyclotomicPrefixMeasurements
