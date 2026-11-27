import PrimeFactors.Certificate
import PrimeFactors.OppositeSquareScaleBands
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Prime.Basic

/-! Count the integers left by one supplied square divisor of a shifted product.
The candidates obey the basic balanced sum or gap window, the true value modulo
four, and the supplied congruence. They need not give an integral factor pair. -/

namespace PrimeFactors.SquareDivisorClueWindow

open Finset
set_option exponentiation.threshold 4096

/-- A square divisor of a multiple of four can always be extended to the
square of an even integer. The extension uses only the parity of the supplied root. -/
theorem even_lift {F y : ℕ} (yp : 0<y) (four : 4 ∣ F) (given : y^2 ∣ F) :
    ∃ Y : ℕ, 0<Y ∧ y ∣ Y ∧ 4 ∣ Y^2 ∧ Y^2 ∣ F := by
  rcases Nat.even_or_odd y with ⟨k,hk⟩ | odd
  · refine ⟨y,yp,dvd_rfl,⟨k^2,?_⟩,given⟩
    rw [hk]
    ring
  · have cop : (2^2).Coprime (y^2) := (odd.coprime_two_left.pow_left 2).pow_right 2
    refine ⟨2*y,by omega,dvd_mul_left _ _,⟨y^2,by ring⟩,?_⟩
    rw [mul_pow]
    exact cop.mul_dvd_of_dvd_of_dvd four given

private theorem neighbor_even (upper : Bool) {p : ℕ} (odd : Odd p) :
    2 ∣ (if upper then p+1 else p-1) := by
  obtain ⟨k,hk⟩ := odd
  cases upper <;> simp <;> omega

/-- All four shifted products of odd factors satisfy the divisibility
hypothesis used in the lift. -/
theorem four_dvd_neighbors (upperP upperQ : Bool) {p q : ℕ} (hp : Odd p) (hq : Odd q) :
    4 ∣ (if upperP then p+1 else p-1)*(if upperQ then q+1 else q-1) :=
  Nat.mul_dvd_mul (neighbor_even upperP hp) (neighbor_even upperQ hq)

/-- Each shifted-product clue gives a single congruence for the sum or the
positive gap, with a signed representative computed from the product. -/
theorem signed_classes (p q m : ℤ) :
    (m ∣ (p-1)*(q-1) ↔ p+q ≡ p*q+1 [ZMOD m]) ∧
    (m ∣ (p+1)*(q+1) ↔ p+q ≡ -(p*q+1) [ZMOD m]) ∧
    (m ∣ (p-1)*(q+1) ↔ q-p ≡ p*q-1 [ZMOD m]) ∧
    (m ∣ (p+1)*(q-1) ↔ q-p ≡ -(p*q-1) [ZMOD m]) := by
  simp only [Int.modEq_iff_dvd,
    show p*q+1-(p+q)=(p-1)*(q-1) by ring,
    show -(p*q+1)-(p+q)=-((p+1)*(q+1)) by ring,
    show p*q-1-(q-p)=(p-1)*(q+1) by ring,
    show -(p*q-1)-(q-p)=-((p+1)*(q-1)) by ring,dvd_neg,iff_self,and_self]

/-- The reference r is the true even residue representative. This definition
retains both its class modulo four and its class modulo the supplied square. -/
def sameClass (y r s : ℕ) : Prop := Even s ∧ s ≡ r [MOD 4] ∧ s ≡ r [MOD y^2]

noncomputable instance (y r s : ℕ) : Decidable (sameClass y r s) := by unfold sameClass; infer_instance

/-- The interval is exactly 4n < s² and 2s² ≤ 9n. -/
noncomputable def sums (n y r : ℕ) : Finset ℕ :=
  (Ioc (4*n).sqrt (9*n/2).sqrt).filter (sameClass y r)

/-- The interval consists of the positive gaps g with 2g² < n. -/
noncomputable def gaps (n y r : ℕ) : Finset ℕ :=
  (Ioc 0 ((n-1)/2).sqrt).filter (sameClass y r)

theorem mem_sums {n y r s : ℕ} : s ∈ sums n y r ↔
    OppositeSquareScaleBands.InSumWindow n s ∧ sameClass y r s := by
  simp only [sums,mem_filter,mem_Ioc,Nat.sqrt_lt',Nat.le_sqrt',Nat.le_div_iff_mul_le
    (by decide : 0<2),OppositeSquareScaleBands.InSumWindow,mul_comm (s^2) 2]

theorem mem_gaps {n y r g : ℕ} : g ∈ gaps n y r ↔
    (0<g ∧ 2*g^2<n) ∧ sameClass y r g := by
  simp only [gaps,mem_filter,mem_Ioc,Nat.le_sqrt',Nat.le_div_iff_mul_le (by decide : 0<2)]
  rw [Nat.mul_comm (g^2) 2]
  constructor
  · rintro ⟨⟨gp,hi⟩,same⟩
    have positive : 0<g^2 := pow_pos gp _
    exact ⟨⟨gp,by omega⟩,same⟩
  · rintro ⟨⟨gp,hi⟩,same⟩
    exact ⟨⟨gp,by omega⟩,same⟩

/-- Every class has exactly k representatives in any k full periods. -/
theorem full_periods (a k r : ℕ) {m : ℕ} (mp : 0<m) :
    ((Ioc a (a+k*m)).filter (fun s => s ≡ r [MOD m])).card=k := by
  have mq : (m:ℚ)≠0 := by positivity
  have shift : (((a+k*m:ℕ):ℚ)-r)/m=((a:ℚ)-r)/m+k := by
    push_cast
    field_simp
    ring
  have eq := Nat.Ioc_filter_modEq_card a (a+k*m) mp r
  rw [shift,Int.floor_add_natCast] at eq
  simpa using eq

private theorem sameClass_of_lift {y Y s r : ℕ} (lift : y ∣ Y) (four : 4 ∣ Y^2)
    (even : Even r) (same : s ≡ r [MOD Y^2]) : sameClass y r s := by
  have h4 := same.of_dvd four
  have h2 := h4.of_dvd (by decide : 2 ∣ 4)
  change s%2=r%2 at h2
  exact ⟨Nat.even_iff.mpr (h2.trans (Nat.even_iff.mp even)),h4,
    same.of_dvd (pow_dvd_pow_of_dvd lift 2)⟩

/-- A uniform integer interval inside the full-width balanced sum window. -/
theorem sum_slab {n s : ℕ} (large : 2^2047≤n)
    (lo : (4*n).sqrt<s) (hi : s≤(4*n).sqrt+2^1020) :
    OppositeSquareScaleBands.InSumWindow n s := by
  let a := (4*n).sqrt
  let w : ℕ := 2^1020
  have height : 18*w≤a := Nat.le_sqrt'.mpr (calc
    (18*w)^2 ≤ 4*2^2047 := by decide +kernel
    _ ≤ 4*n := Nat.mul_le_mul_left 4 large)
  have scaled : 18*s≤19*a := by change s≤a+w at hi; omega
  have raised := Nat.pow_le_pow_left scaled 2
  have asq : a^2≤4*n := Nat.sqrt_le' _
  exact ⟨Nat.sqrt_lt'.mp lo,by nlinarith only [raised,asq]⟩

/-- A uniform integer interval inside the full-width positive gap window. -/
theorem gap_slab {n g : ℕ} (large : 2^2047≤n) (hi : g<2^1023) :
    2*g^2<n := calc
  2*g^2 < 2*(2^1023)^2 := Nat.mul_lt_mul_of_pos_left
    (Nat.pow_lt_pow_left hi (by decide : 2≠0)) (by decide)
  _ = 2^2047 := by decide +kernel
  _ ≤ n := large

/-- On a full-width input with all roots of square divisors of F below 2^128,
one compatible class still contains at least 2^764 even sums and 2^767 even
gaps in the respective basic windows. F is a multiple of four, as is every
shifted product of two odd primes. The reference r may be any even integer
represented in the naturals, so this bound holds at the actual residue. -/
theorem counts {n F y r : ℕ} (full : 2^2047≤n) (yp : 0<y) (four : 4∣F)
    (given : y^2∣F) (small : ∀ Y : ℕ, Y^2∣F → Y<2^128) (even : Even r) :
    2^764 ≤ (sums n y r).card ∧ 2^767 ≤ (gaps n y r).card := by
  obtain ⟨Y,Yp,lift,fourY,divides⟩ := even_lift yp four given
  have mpos : 0<Y^2 := pow_pos Yp _
  have mt : Y^2<2^256 := (Nat.pow_lt_pow_left (small Y divides) (by decide : 2≠0)).trans_eq
    (by decide +kernel : (2^128)^2=2^256)
  have sum_width : 2^764*Y^2 ≤ 2^1020 := (Nat.mul_le_mul_left (2^764) mt.le).trans_eq
    (by decide +kernel : 2^764*2^256=2^1020)
  have gap_width : 2^767*Y^2 < 2^1023 :=
    (Nat.mul_lt_mul_of_pos_left mt (by decide +kernel : 0<2^767)).trans_eq
      (by decide +kernel : 2^767*2^256=2^1023)
  constructor
  · rw [←full_periods (4*n).sqrt (2^764) r mpos]
    apply card_le_card
    intro s hs
    obtain ⟨inside,same⟩ := mem_filter.mp hs
    obtain ⟨lo,hi⟩ := mem_Ioc.mp inside
    exact mem_sums.mpr ⟨sum_slab full lo (hi.trans (Nat.add_le_add_left sum_width _)),
      sameClass_of_lift lift fourY even same⟩
  · rw [←full_periods 0 (2^767) r mpos]
    apply card_le_card
    intro g hg
    obtain ⟨inside,same⟩ := mem_filter.mp hg
    obtain ⟨lo,hi⟩ := mem_Ioc.mp inside
    exact mem_gaps.mpr ⟨⟨lo,gap_slab full ((by simpa using hi : g≤2^767*Y^2).trans_lt gap_width)⟩,
      sameClass_of_lift lift fourY even same⟩

/-- On the seeded 20-bit prime pair the supplied successor square 288²
already leaves a unique sum in the basic window. -/
theorem seeded_control :
    ExactFactorization 419636024497 [556559,753983] ∧
    288^2 ∣ (556559+1)*(753983+1) ∧
    ∀ s : ℕ, OppositeSquareScaleBands.InSumWindow 419636024497 s →
      288^2 ∣ 419636024497+1+s → s=1310542 := by
  refine ⟨by norm_num [ExactFactorization],by decide +kernel,?_⟩
  intro s window divides
  have low : 1295586<s := by
    by_contra! tiny
    have := Nat.pow_le_pow_left tiny 2
    have := window.1
    omega
  have high : s≤1374176 := by
    by_contra! large
    have := Nat.pow_le_pow_left (show 1374177≤s by omega) 2
    have := window.2
    omega
  change 82944∣419636024498+s at divides
  omega

end PrimeFactors.SquareDivisorClueWindow
