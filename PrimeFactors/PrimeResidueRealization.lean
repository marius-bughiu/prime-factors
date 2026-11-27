import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! The unconditional estimate of Bennett, Martin, O’Bryant and Rechnitzer gives
many primes in both of two disjoint intervals in every reduced class modulo
9240. We expose the published theta bound as an explicit input.
Paper: https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf -/
namespace PrimeFactors.PrimeResidueRealization

open Finset Real
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

abbrev M : ℕ := 9240
abbrev B : ℕ := 2^1021

theorem wheel_totient : M.totient = 1920 := by decide +kernel

noncomputable def through (a x : ℕ) : Finset ℕ :=
  (range (x+1)).filter fun p => p.Prime ∧ p%M = a

noncomputable def theta (a x : ℕ) : ℝ :=
  ∑ p ∈ through a x, log p

/-- Theorem 1.2, with (1.10)–(1.11), specialized at q=9240.
Here φ(9240)=1920, c₀=1/840 and x₀=8·10⁹. -/
def BMOR : Prop := ∀ a < M, a.Coprime M → ∀ x : ℕ, 8000000000 ≤ x →
  |theta a x - x/1920| ≤ x/(840*log x)

noncomputable def lane (a l h : ℕ) : Finset ℕ := through a h \ through a l

theorem mem_lane {a l h p : ℕ} : p ∈ lane a l h ↔
    p.Prime ∧ p % M = a ∧ l < p ∧ p ≤ h := by
  simp only [lane, through, mem_sdiff, mem_filter, mem_range, Nat.lt_succ_iff]
  by_cases hp : p.Prime
  · by_cases hm : p%M=a
    · simp [hp,hm]; omega
    · simp [hp,hm]
  · simp [hp]

private theorem log_bounds {x : ℕ} (lo : 2^1023 ≤ x) (hi : x ≤ 2^1024) :
    (700:ℝ) ≤ log x ∧ log x ≤ 710 := by
  have xp : (0:ℝ)<x := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<2^1023) lo)
  have low := log_le_log (by positivity : 0<(2:ℝ)^1023) (by exact_mod_cast lo : (2:ℝ)^1023≤x)
  have high := log_le_log xp (by exact_mod_cast hi : (x:ℝ)≤2^1024)
  rw [log_pow] at low high
  norm_num only [Nat.cast_ofNat] at low high
  constructor
  · linarith only [low,log_two_gt_d9]
  · linarith only [high,log_two_lt_d9]

private theorem endpoint (bm : BMOR) {a x : ℕ} (ha : a < M) (unit : a.Coprime M)
    (lo : 2^1023 ≤ x) (hi : x ≤ 8*B) :
    |theta a x - x/1920| ≤ (8*(B:ℝ))/588000 := by
  have range : 8000000000 ≤ x := le_trans (by decide) lo
  have l := (log_bounds lo (hi.trans (by decide))).1
  have pos : 0 < 840*log (x:ℝ) := by linarith only [l]
  refine (bm a ha unit x range).trans ?_
  have hx : (x:ℝ) ≤ 8*(B:ℝ) := by exact_mod_cast hi
  apply (div_le_div_iff₀ pos (by norm_num : (0:ℝ)<588000)).mpr
  have b := mul_le_mul_of_nonneg_left l (show (0:ℝ)≤8*B by positivity)
  linarith only [hx,b]

private theorem lane_pop (bm : BMOR) {a l h : ℕ} (ha : a < M) (unit : a.Coprime M)
    (low : 2^1023 ≤ l) (hi : h ≤ 8*B) (width : h=l+B) :
    2^1000 < (lane a l h).card := by
  have lh : l ≤ h := by omega
  have high := (abs_le.mp (endpoint bm ha unit (low.trans lh) hi)).1
  have left := (abs_le.mp (endpoint bm ha unit low (lh.trans hi))).2
  have sub : through a l ⊆ through a h :=
    filter_subset_filter _ (range_mono (Nat.succ_le_succ lh))
  have mass := sum_sdiff sub (f := fun p : ℕ => log p)
  change (∑ p ∈ lane a l h, log p) + theta a l = theta a h at mass
  have cap : (∑ p ∈ lane a l h, log p) ≤ (lane a l h).card * (710:ℝ) := by
    calc
      _ ≤ ∑ _ ∈ lane a l h, (710:ℝ) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨_,_,pl,ph⟩ := mem_lane.mp hp
        exact (log_bounds (low.trans pl.le) (ph.trans (hi.trans (by decide)))).2
      _ = _ := by simp
  have hw : (h:ℝ) = l + (B:ℝ) := by exact_mod_cast width
  have margin : (2:ℝ)^1000*710 < (B:ℝ)/1920 - 2*(8*(B:ℝ))/588000 := by norm_num [B]
  have lower : (B:ℝ)/1920 - 2*(8*(B:ℝ))/588000 ≤ (lane a l h).card * (710:ℝ) := by
    linear_combination cap + left + high + mass.symm + hw.symm / 1920
  have c := lt_of_mul_lt_mul_right (margin.trans_le lower) (by norm_num : (0:ℝ) ≤ 710)
  exact_mod_cast c

theorem left_population (bm : BMOR) {a : ℕ} (ha : a < M) (unit : a.Coprime M) :
    2^1000 < (lane a (6*B) (7*B)).card :=
  lane_pop bm ha unit (by decide) (by decide) (by decide)

theorem right_population (bm : BMOR) {a : ℕ} (ha : a < M) (unit : a.Coprime M) :
    2^1000 < (lane a (7*B) (8*B)).card :=
  lane_pop bm ha unit (by decide) (by decide) (by decide)

attribute [local irreducible] lane through

noncomputable def products (a b : ℕ) : Finset ℕ :=
  ((lane a (6*B) (7*B)) ×ˢ (lane b (7*B) (8*B))).image fun x => x.1*x.2

private theorem unique_products {A D : Finset ℕ} {m : ℕ}
    (left : ∀ p ∈ A, p.Prime ∧ p ≤ m) (right : ∀ q ∈ D, q.Prime ∧ m < q) :
    Set.InjOn (fun x : ℕ × ℕ => x.1*x.2) (↑(A ×ˢ D) : Set (ℕ × ℕ)) := by
  rintro ⟨p,q⟩ h₁ ⟨r,s⟩ h₂ eq
  obtain ⟨P,ph⟩ := left p (mem_product.mp h₁).1
  obtain ⟨R,_⟩ := left r (mem_product.mp h₂).1
  obtain ⟨S,sl⟩ := right s (mem_product.mp h₂).2
  change p*q = r*s at eq
  have d : p ∣ r*s := eq ▸ dvd_mul_right _ _
  have pr : p=r := (P.dvd_mul.mp d).elim ((Nat.prime_dvd_prime_iff_eq P R).mp)
    (fun bad => False.elim ((ph.trans_lt sl).ne ((Nat.prime_dvd_prime_iff_eq P S).mp bad)))
  subst r
  exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left P.pos eq)

/-- This counts distinct semiprimes with the supplied ordered residues. -/
theorem product_population (bm : BMOR) {a b : ℕ}
    (ha : a < M) (ua : a.Coprime M) (hb : b < M) (ub : b.Coprime M) :
    2^2000 < (products a b).card := by
  have left (p : ℕ) (hp : p ∈ lane a (6*B) (7*B)) : p.Prime ∧ p ≤ 7*B := by
    obtain ⟨P,_,_,ph⟩ := (mem_lane (p:=p) (a:=a) (l:=6*B) (h:=7*B)).mp hp
    exact ⟨P,ph⟩
  have right (q : ℕ) (hq : q ∈ lane b (7*B) (8*B)) : q.Prime ∧ 7*B < q := by
    obtain ⟨Q,_,ql,_⟩ := (mem_lane (p:=q) (a:=b) (l:=7*B) (h:=8*B)).mp hq
    exact ⟨Q,ql⟩
  have inject := unique_products left right
  rw [products,card_image_of_injOn inject,card_product,show 2000=1000+1000 by decide,pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (left_population bm ha ua) (right_population bm hb ub)

/-- Primes in the two windows have 1024 bits and their product has 2048 bits. -/
theorem product_properties {n a b : ℕ} (hn : n ∈ products a b) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ 2^1023 ≤ p ∧ q < 2^1024 ∧
      p%M = a ∧ q%M = b ∧ n=p*q ∧ n%M=(a*b)%M ∧ 2^2047 ≤ n ∧ n < 2^2048 := by
  unfold products at hn
  obtain ⟨⟨p,q⟩,mem,eq⟩ := mem_image.mp hn
  obtain ⟨P,pa,pl,ph⟩ := (mem_lane (p:=p) (a:=a) (l:=6*B) (h:=7*B)).mp (mem_product.mp mem).1
  obtain ⟨Q,qb,ql,qh⟩ := (mem_lane (p:=q) (a:=b) (l:=7*B) (h:=8*B)).mp (mem_product.mp mem).2
  change p*q=n at eq
  subst n
  have qt : q < 2^1024 := lt_of_le_of_ne (qh.trans (by decide)) (fun eq =>
    (Nat.Prime.not_prime_pow (by decide : 2 ≤ 1024) (x := 2)) (eq ▸ Q))
  have pq := ph.trans_lt ql
  refine ⟨p,q,P,Q,pq,le_trans (by decide) pl.le,qt,pa,qb,rfl,?_,?_,?_⟩
  · rw [Nat.mul_mod,pa,qb]
  · exact le_trans (by decide : 2^2047 ≤ (6*B)*(7*B)) (Nat.mul_le_mul pl.le ql.le)
  · calc p*q < 2^1024*2^1024 := Nat.mul_lt_mul_of_lt_of_lt (pq.trans qt) qt
         _ = _ := by decide

end PrimeFactors.PrimeResidueRealization
