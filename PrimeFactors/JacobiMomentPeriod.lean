import PrimeFactors.JacobiMomentRecurrence
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.GroupTheory.Exponent

/-!
# Exact periods of complete Jacobi moments

The index starts at degree one for the full sequence and degree two for
its even subsequence. The degree-zero term has a separate contribution from
the zero residue. Periods here mean shifts preserving every term.
-/

namespace PrimeFactors.JacobiMomentPeriod

open Polynomial Finset Function JacobiMomentRecurrence
open scoped Polynomial

/-- Advance a sequence by one position. -/
def next {α : Type*} (u : ℕ → α) : ℕ → α := fun n => u (n+1)

private theorem iter_next {α : Type*} (u : ℕ → α) (t n : ℕ) : next^[t] u n = u (n+t) := by
  induction t generalizing n with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    change next^[t] u (n+1) = u (n+(t+1))
    rw [ih]; congr 1; omega

private theorem periodic_iff {α : Type*} (u : ℕ → α) (t : ℕ) :
    IsPeriodicPt next t u ↔ Periodic u t := by
  change (next^[t] u = u) ↔ ∀ n, u (n+t) = u n
  rw [funext_iff]
  simp only [iter_next]

private theorem shift_sparse {F : Type*} [Field F] (u : ℕ → F) (t n : ℕ) :
    shift ((X:F[X])^t - C 1) u n = u (n+t) - u n := by
  classical
  by_cases ht : t=0
  · simp [ht,shift]
  calc
    _ = ∑ j ∈ ({0,t} : Finset ℕ), (((X:F[X])^t - C 1).coeff j) * u (n+j) := by
      apply sum_subset
      · intro j hj
        by_contra h
        simp only [mem_insert, mem_singleton, not_or] at h
        have hz : (((X:F[X])^t - C 1).coeff j) = 0 := by
          simp [coeff_sub,coeff_X_pow,coeff_one,coeff_C,h.1,h.2,Ne.symm h.1,Ne.symm h.2]
        exact (Polynomial.mem_support_iff.mp hj) hz
      · intro j _ h
        rw [Polynomial.not_mem_support_iff.mp h,zero_mul]
    _ = _ := by
      rw [sum_pair (Ne.symm ht)]
      simp [coeff_sub,coeff_X_pow,coeff_one,coeff_C,ht,Ne.symm ht]; ring

/-- Positive even moments in a single prime-field component. -/
noncomputable def localEven (p : ℕ) [Fact p.Prime] (j : ℕ) := component p (2*(j+1))

/-- The complete moments at degrees two, four, six, and so on. -/
noncomputable def completeEven (N : ℕ) [NeZero N] (j : ℕ) := ProjectiveWordMoments.moment N (2*(j+1))

/-- At an odd prime the local even period is half the group size, except at five. -/
def localPeriod (p : ℕ) : ℕ := if p=5 then 1 else (p-1)/2

private theorem twice_half {p : ℕ} [Fact p.Prime] (odd : p≠2) : 2*((p-1)/2)=p-1 := by
  have ⟨j,h⟩ := (Fact.out : p.Prime).odd_of_ne_two odd
  omega

private theorem fermat {p : ℕ} [Fact p.Prime] (odd : p≠2) :
    Periodic (localEven p) ((p-1)/2) := by
  intro n
  dsimp only [localEven, component]
  apply congrArg Neg.neg
  apply sum_congr rfl
  intro t _
  suffices h : t^(2*(n+(p-1)/2+1)) = t^(2*(n+1)) by rw [h]
  by_cases zero : t=0
  · simp [zero]
  · rw [show 2*(n+(p-1)/2+1) = 2*(n+1)+(p-1) by have := twice_half odd; omega,
      pow_add, ZMod.pow_card_sub_one_eq_one zero, mul_one]

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem at_five : Periodic (localEven 5) 1 := by
  have one (z : ZMod 5) (hz : z ∈ evenBases 5) : z=1 := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    fin_cases x <;> first | decide | (exfalso; revert hx; decide)
  intro n
  simp only [localEven,component_even (p:=5) (by decide),signal]
  apply sum_congr rfl
  intro z hz
  simp [one z hz]

/-- Exact local period of all the positive even moments. -/
theorem local_iff {p : ℕ} [Fact p.Prime] (odd : p≠2) (t : ℕ) :
    Periodic (localEven p) t ↔ localPeriod p ∣ t := by
  rw [← periodic_iff, isPeriodicPt_iff_minimalPeriod_dvd]
  suffices equality : minimalPeriod next (localEven p) = localPeriod p by rw [equality]
  let d := localPeriod p
  have works : Periodic (localEven p) d := by
    by_cases five : p=5
    · subst p; simpa [d,localPeriod] using at_five
    · simpa [d,localPeriod,five] using fermat odd
  have pp := (Fact.out : p.Prime).two_le
  have dp : 0<d := by simp only [d,localPeriod]; split_ifs <;> omega
  have pt := (periodic_iff _ _).mpr works
  let h := minimalPeriod next (localEven p)
  have hp : 0<h := pt.minimalPeriod_pos dp
  have hd : h ∣ d := pt.minimalPeriod_dvd
  change h = d
  apply le_antisymm (Nat.le_of_dvd dp hd)
  by_cases low : p≤5
  · have only : p=3 ∨ p=5 := by
      have ne : p≠4 := by rintro rfl; exact (show ¬ Nat.Prime 4 by decide) Fact.out
      omega
    rcases only with h | h <;> subst p <;> dsimp [d,localPeriod] <;> omega
  have prime7 : 7≤p := by
    have ne : p≠6 := by rintro rfl; exact (show ¬ Nat.Prime 6 by decide) Fact.out
    omega
  have hperiod : Periodic (localEven p) h :=
    (periodic_iff _ _).mp (isPeriodicPt_minimalPeriod _ _)
  -- A period h gives the monic recurrence polynomial X^h − 1.
  have large : (p-3)/2 ≤ h := by
    let P : (ZMod p)[X] := X^h-C 1
    have fit (i : Fin ((p-3)/2)) :
        shift P (fun k => component p (2*(k+1))) (0+i) = 0 := by
      change shift ((X:(ZMod p)[X])^h-C 1) (localEven p) (0+i) = 0
      rw [shift_sparse, hperiod _, sub_self]
    simpa only [P,natDegree_X_pow_sub_C] using local_even_order odd P (X_pow_sub_C_ne_zero hp 1) 0 fit
  have form : d=(p-1)/2 := if_neg (by omega)
  classical
  by_contra! lt
  -- For p ≥ 7 the recurrence order exceeds half of d, excluding every proper divisor.
  obtain ⟨k,hk⟩ := hd
  have kbig : 2≤k := by
    by_contra! sk
    interval_cases k <;> simp only [Nat.mul_zero,Nat.mul_one] at hk <;> omega
  have two := Nat.mul_le_mul_left h kbig
  omega

/-- A shift preserves all positive even moments modulo the product exactly when
the least common multiple of the two local periods divides the shift. -/
theorem composite_iff {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (t : ℕ) :
    Periodic (completeEven (p*q)) t ↔ (localPeriod p).lcm (localPeriod q) ∣ t := by
  rw [Nat.lcm_dvd_iff, ← local_iff hp, ← local_iff hq]
  let e := ZMod.chineseRemainder cop
  have crt (i : ℕ) : e (completeEven (p*q) i) = (localEven p i, localEven q i) :=
    ProjectiveWordMoments.components cop hp hq _
  constructor
  · intro h
    have equiv (i) := (crt (i+t)).symm.trans ((congrArg e (h i)).trans (crt i))
    exact ⟨fun i => congrArg Prod.fst (equiv i), fun i => congrArg Prod.snd (equiv i)⟩
  · rintro ⟨a,b⟩ i
    apply e.injective
    rw [crt,crt,a i,b i]

private theorem units_exp {p : ℕ} [Fact p.Prime] :
    Monoid.exponent (ZMod p)ˣ = p-1 := by
  rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]

/-- Twice the smallest period equals the exponent of the whole unit group, once
both primes are at least seven. -/
theorem unit_exponent {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 7≤p) (hq : 7≤q) :
    2*(localPeriod p).lcm (localPeriod q) = Monoid.exponent (ZMod (p*q))ˣ := by
  let e := (Units.mapEquiv (ZMod.chineseRemainder cop).toMulEquiv).trans MulEquiv.prodUnits
  rw [Monoid.exponent_eq_of_mulEquiv e, Monoid.exponent_prod,units_exp, units_exp, ← Nat.lcm_mul_left]
  simp only [localPeriod,if_neg (show p≠5 by omega),if_neg (show q≠5 by omega),
    twice_half (show p≠2 by omega), twice_half (show q≠2 by omega)]
  rfl

private theorem interleave {R : Type*} [Zero R] (v e : ℕ → R)
    (a : ∀ j, v (2*j)=0) (b : ∀ j, v (2*j+1)=e j) (nz : e 0≠0) (t : ℕ) :
    Periodic v t ↔ ∃ h, t=2*h ∧ Periodic e h := by
  constructor
  · intro hh
    have et : t%2=0 := by
      by_contra odd
      have h := hh 1
      rw [show 1+t=2*((1+t)/2) by omega, a, show 1=2*0+1 by decide, b] at h
      exact nz h.symm
    refine ⟨t/2, by omega, ?_⟩
    intro j
    have h := hh (2*j+1)
    rw [show 2*j+1+t=2*(j+t/2)+1 by omega, b, b] at h
    exact h
  · rintro ⟨h,rfl,ee⟩ j
    by_cases j0 : j%2=0
    · calc
        v (j+2*h) = v (2*(j/2+h)) := by congr 1; omega
        _ = 0 := a _
        _ = v j := by rw [← a (j/2)]; congr 1; omega
    · calc
        v (j+2*h) = v (2*(j/2+h)+1) := by congr 1; omega
        _ = e (j/2+h) := b _
        _ = e (j/2) := ee _
        _ = v j := by rw [← b (j/2)]; congr 1; omega

/-- The period of all positive moments, including the interleaved zero odd
degrees, equals the full unit group exponent for primes at least seven. -/
theorem ordinary_iff {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 7≤p) (hq : 7≤q) (t : ℕ) :
    Periodic (fun i => ProjectiveWordMoments.moment (p*q) (i+1)) t ↔
      Monoid.exponent (ZMod (p*q))ˣ ∣ t := by
  have oddp : p≠2 := by omega
  have oddq : q≠2 := by omega
  let v := fun i => ProjectiveWordMoments.moment (p*q) (i+1)
  have zeros (j) : v (2*j) = 0 :=
    ProjectiveWordMoments.odd_moment cop oddp oddq _ ⟨j,rfl⟩
  have evens (j) : v (2*j+1) = completeEven (p*q) j := by
    dsimp [v,completeEven]; congr 1
  have nz : completeEven (p*q) 0≠0 := by
    change ProjectiveWordMoments.moment (p*q) 2 ≠ 0
    rw [ProjectiveWordMoments.jacobi_moment cop oddp oddq _ (by omega) (by omega)]
    change ((2:ℕ):ZMod (p*q))≠0
    rw [ne_eq,ZMod.natCast_zmod_eq_zero_iff_dvd]
    apply Nat.not_dvd_of_pos_of_lt (by decide)
    nlinarith
  rw [interleave v _ zeros evens nz, ← unit_exponent cop hp hq]
  constructor
  · rintro ⟨h,rfl,period⟩
    exact Nat.mul_dvd_mul_left 2 ((composite_iff cop oddp oddq _).mp period)
  · rintro ⟨j,rfl⟩
    exact ⟨_,Nat.mul_assoc .., (composite_iff cop oddp oddq _).mpr (dvd_mul_right _ _)⟩

set_option exponentiation.threshold 2048 in
/-- Bounds on the integer period for two primes of bit length 1,024. -/
theorem full_size {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lp : 2^1023≤p) (lq : 2^1023≤q) (rp : p<2^1024) (rq : q<2^1024) :
    2^1022 ≤ (localPeriod p).lcm (localPeriod q) ∧
    (localPeriod p).lcm (localPeriod q) < 2^2046 := by
  have wp : localPeriod p = (p-1)/2 := if_neg (by omega)
  have wq : localPeriod q = (q-1)/2 := if_neg (by omega)
  have oq := twice_half (p:=q) (by omega)
  have div := Nat.dvd_lcm_right (localPeriod p) (localPeriod q)
  have pos := Nat.lcm_pos (show 0<localPeriod p by omega) (show 0<localPeriod q by omega)
  have lb := Nat.le_of_dvd pos div
  have ub := Nat.le_of_dvd (Nat.mul_pos (show 0<localPeriod p by omega) (show 0<localPeriod q by omega))
    (Nat.lcm_dvd_mul (localPeriod p) (localPeriod q))
  have small := Nat.mul_lt_mul_of_lt_of_le (show localPeriod p < 2^1023 by omega)
    (show localPeriod q ≤ 2^1023 by omega) (show 0<2^1023 by decide)
  constructor
  · omega
  · exact ub.trans_lt (by simpa [←pow_add] using small)

/-- Certified prime factorizations of the two additional controls at 21 and 65.
The other five inputs have certificates in ProjectiveWordMoments.toy_factorizations. -/
theorem additional_toy_factorizations :
    ExactFactorization 21 [3,7] ∧ ExactFactorization 65 [5,13] := by
  norm_num [ExactFactorization]

end PrimeFactors.JacobiMomentPeriod
