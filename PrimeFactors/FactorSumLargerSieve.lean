import PrimeFactors.IntervalLargerSieve
import PrimeFactors.IntervalSievePrimeWeights
import PrimeFactors.IntervalWheelResidues
import Mathlib.NumberTheory.Primorial

/-! Apply the larger sieve to the possible sums of two unknown factors.
Every test uses the product modulo a small prime. The cardinality bounds
do not give a way to enumerate the survivors in time proportional to their number. -/
namespace PrimeFactors.FactorSumLargerSieve

open Finset Real

noncomputable def survivors (n lo hi : ℕ) (P : Finset ℕ) : Finset ℕ := by
  classical
  exact (Icc lo hi).filter fun s => ∀ ℓ ∈ P, AdmissibleSum (n : ZMod ℓ) (s : ZMod ℓ)

theorem mem_survivors {n lo hi s : ℕ} {P : Finset ℕ} :
    s ∈ survivors n lo hi P ↔ (lo ≤ s ∧ s ≤ hi) ∧
      ∀ ℓ ∈ P, AdmissibleSum (n : ZMod ℓ) (s : ZMod ℓ) := by
  classical
  simp only [survivors,mem_filter,mem_Icc]

theorem contains_sum {p q lo hi : ℕ} (P : Finset ℕ) (low : lo ≤ p+q) (high : p+q ≤ hi) :
    p+q ∈ survivors (p*q) lo hi P :=
  mem_survivors.mpr ⟨⟨low,high⟩,fun ℓ _ => admissibleSum_of_factor_pair ℓ rfl⟩

/-- Every residue occupied by a survivor has modular witnesses. The
injection counts distinct residues regardless of how far apart the sums lie. -/
theorem occupied {S : Finset ℕ} {n ℓ : ℕ} (positive : 0 < ℓ)
    (ok : ∀ s ∈ S, AdmissibleSum (n : ZMod ℓ) (s : ZMod ℓ)) :
    (S.image (fun x => x%ℓ)).card ≤ LocalSumMenu.count n ℓ := by
  classical
  letI : NeZero ℓ := ⟨positive.ne'⟩
  let R := S.image (fun x => x%ℓ)
  have small (a : R) : a.val < ℓ := by
    obtain ⟨x,_,eq⟩ := mem_image.mp a.property
    exact eq ▸ (Nat.mod_lt x positive)
  let lift (a : R) : {r : ZMod ℓ // AdmissibleSum (n : ZMod ℓ) r} := ⟨(a.val:ZMod ℓ),by
    obtain ⟨x,hx,eq⟩ := mem_image.mp a.property
    rw [←eq,ZMod.natCast_mod]
    exact ok x hx⟩
  have inj : Function.Injective lift := by
    intro a b h
    have vals := congrArg (fun z => z.val.val) h
    change (a.val : ZMod ℓ).val=(b.val : ZMod ℓ).val at vals
    rw [ZMod.val_natCast_of_lt (small a),ZMod.val_natCast_of_lt (small b)] at vals
    exact Subtype.ext vals
  simpa only [R,LocalSumMenu.count,Nat.card_eq_fintype_card,Fintype.card_coe] using
    Nat.card_le_card_of_injective lift inj

theorem occupancy {n lo hi ℓ : ℕ} {P : Finset ℕ} (inside : ℓ ∈ P)
    (prime : ℓ.Prime) (odd : ℓ ≠ 2) (unit : ¬ℓ ∣ n) :
    ((survivors n lo hi P).image (fun x => x%ℓ)).card ≤ (ℓ+1)/2 :=
  (occupied prime.pos (fun _ h => (mem_survivors.mp h).2 ℓ inside)).trans
    (IntervalWheelResidues.prime_classes prime odd unit)

/-- The total logarithmic weight of any subset of primes through Q is at
most 2Q log 2, by the elementary binomial bound for the primorial. -/
theorem weight_upper {Q : ℕ} {P : Finset ℕ} (small : ∀ ℓ ∈ P, ℓ.Prime ∧ ℓ ≤ Q) :
    ∑ ℓ ∈ P, Real.log (ℓ:ℝ) ≤ 2*(Q:ℝ)*Real.log 2 := by
  let all := (range (Q+1)).filter Nat.Prime
  have sub : P ⊆ all := by
    intro p h
    exact mem_filter.mpr ⟨mem_range.mpr (by have := (small p h).2; omega),(small p h).1⟩
  have whole : ∑ ℓ ∈ all, Real.log (ℓ:ℝ) = Real.log (primorial Q) := by
    rw [← Real.log_prod all (fun p : ℕ => (p:ℝ)) (fun p hp => by
      have pos := (mem_filter.mp hp).2.pos
      change (p:ℝ) ≠ 0
      exact_mod_cast pos.ne')]
    simp only [primorial,all,Nat.cast_prod]
  have upper := Real.log_le_log (show (0:ℝ) < primorial Q by exact_mod_cast primorial_pos Q)
    (show (primorial Q : ℝ) ≤ (4:ℝ)^Q by exact_mod_cast primorial_le_4_pow Q)
  have subset : ∑ p ∈ P, Real.log (p:ℝ) ≤ ∑ p ∈ all, Real.log (p:ℝ) :=
    sum_le_sum_of_subset_of_nonneg sub (fun p hp _ =>
      Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le))
  rw [whole] at subset
  rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.log_pow,Real.log_pow] at upper
  apply subset.trans
  convert upper using 1
  push_cast
  ring

private theorem class_weight {p : ℕ} (prime : p.Prime) (odd : p ≠ 2) :
    log (p:ℝ) / (((p+1)/2:ℕ):ℝ) = 2*(log (p:ℝ)/((p:ℝ)+1)) := by
  have oddp := Nat.odd_iff.mp (prime.odd_of_ne_two odd)
  have double : ((p+1)/2)*2=p+1 := by omega
  have realDouble : (((p+1)/2:ℕ):ℝ)*2=(p:ℝ)+1 := by exact_mod_cast double
  rw [show (((p+1)/2:ℕ):ℝ)=((p:ℝ)+1)/2 by linarith only [realDouble],div_div_eq_mul_div]
  ring

/-- Clearing Gallagher's denominator keeps the cost of the tested prime
range visible. This applies even if no sum passes all the congruences. -/
theorem weighted_bound {n lo hi H Q : ℕ} {P : Finset ℕ} {D : ℝ}
    (positive : 1 ≤ H) (width : hi ≤ lo+H)
    (small : ∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ ¬p ∣ n ∧ p ≤ Q)
    (weight : D ≤ 2*(∑ p ∈ P, log (p:ℝ)/((p:ℝ)+1))-log H) :
    ((survivors n lo hi P).card:ℝ)*D ≤ 2*(Q:ℝ)*log 2 := by
  let S := survivors n lo hi P
  change (S.card:ℝ)*D ≤ _
  by_cases nonempty : S.Nonempty
  · have bound := IntervalLargerSieve.linear_bound S P (fun p => (p+1)/2) positive
      (fun p hp => (small p hp).1)
      (fun x hx y hy => by
        have a := (mem_survivors.mp hx).1.2
        have b := (mem_survivors.mp hy).1.1
        omega)
      (fun p hp => by change 0 < (p+1)/2; have := (small p hp).1.two_le; omega)
      (fun p hp => occupancy hp (small p hp).1 (small p hp).2.1 (small p hp).2.2.1)
      nonempty
    have rewriteWeight : (∑ p ∈ P, log (p:ℝ) / (((p+1)/2:ℕ):ℝ)) =
        2*(∑ p ∈ P, log (p:ℝ)/((p:ℝ)+1)) := by
      rw [mul_sum]
      exact sum_congr rfl (fun p hp => class_weight (small p hp).1 (small p hp).2.1)
    rw [rewriteWeight] at bound
    have total := weight_upper (fun p hp => ⟨(small p hp).1,(small p hp).2.2.2⟩)
    exact ((mul_le_mul_of_nonneg_left weight (by positivity)).trans bound).trans
      ((sub_le_self _ (Real.log_nonneg (by exact_mod_cast positive))).trans total)
  · rw [not_nonempty_iff_eq_empty.mp nonempty]
    simp only [card_empty,Nat.cast_zero,zero_mul]
    positivity

/-- An interval of diameter 2^(2k) contains at most 2^(k+7) admissible
sums after testing the odd primes through 2^(k+8), for a product coprime
to those primes. No character reading is assumed. -/
theorem dyadic_bound (n lo hi k : ℕ) (width : hi ≤ lo+2^(2*k))
    (unit : ∀ p ∈ IntervalSievePrimeWeights.primes (2^(k+8)), ¬p ∣ n) :
    (survivors n lo hi (IntervalSievePrimeWeights.primes (2^(k+8)))).card ≤ 2^(k+7) := by
  let P := IntervalSievePrimeWeights.primes (2^(k+8))
  have weight := IntervalSievePrimeWeights.dyadic (k:=k+8) (by omega)
  have length : log ((2^(2*k):ℕ):ℝ) = (2*(k:ℝ))*log 2 := by
    simp only [Nat.cast_pow,Nat.cast_ofNat,log_pow,Nat.cast_mul]
  have lower : 4*log 2 ≤ 2*(∑ p ∈ P, log (p:ℝ)/((p:ℝ)+1))-log ((2^(2*k):ℕ):ℝ) := by
    push_cast at weight
    rw [length]
    dsimp only [P]
    linarith only [weight]
  have small (p : ℕ) (hp : p∈P) : p.Prime ∧ p ≠ 2 ∧ ¬p∣n ∧ p≤2^(k+8) := by
    have h := mem_filter.mp hp
    have range := mem_Icc.mp h.1
    exact ⟨h.2,by omega,unit p hp,range.2⟩
  have bound := weighted_bound (n:=n)
    (Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2:ℕ)) (2*k))) width small lower
  have scale : (2:ℝ)^(k+8)=(2:ℝ)^(k+7)*2 := by rw [show k+8=k+7+1 by omega,pow_succ]
  rw [Nat.cast_pow,Nat.cast_ofNat,scale] at bound
  have lg : 0 < log 2 := Real.log_pos (by norm_num)
  apply (Nat.cast_le (α:=ℝ)).mp
  rw [Nat.cast_pow,Nat.cast_ofNat]
  change ((survivors n lo hi P).card:ℝ) ≤ (2:ℝ)^(k+7)
  apply (mul_le_mul_iff_of_pos_right (show 0 < 4*log 2 by positivity)).mp
  linarith only [bound]

set_option exponentiation.threshold 2048 in
/-- A product-only bound for the entire two-1,024-bit-prime search.
No estimate of a character sum or information from the factors is supplied. -/
theorem full_width {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (lower : 2^1023 ≤ p) (order : p ≤ q) (upper : q < 2^1024) :
    let S := survivors (p*q) (2^1024) (2^1025-1) (IntervalSievePrimeWeights.primes (2^520))
    p+q ∈ S ∧ S.card ≤ 2^519 := by
  dsimp only
  have A : (2:ℕ)^1024=2*2^1023 := by decide +kernel
  have B : (2:ℕ)^1025=2*2^1024 := by decide +kernel
  constructor
  · apply contains_sum <;> omega
  · apply dyadic_bound (p*q) _ _ 512 (by omega)
    intro ℓ hℓ
    have small := mem_Icc.mp (mem_filter.mp hℓ).1
    have prime := (mem_filter.mp hℓ).2
    have lt : ℓ < p := small.2.trans_lt ((by decide +kernel : (2:ℕ)^520 < 2^1023).trans_le lower)
    intro divides
    rcases prime.dvd_mul.mp divides with x|x
    · exact lt.ne ((Nat.prime_dvd_prime_iff_eq prime pp).mp x)
    · exact (lt.trans_le order).ne ((Nat.prime_dvd_prime_iff_eq prime qp).mp x)

end PrimeFactors.FactorSumLargerSieve
