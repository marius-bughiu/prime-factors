import PrimeFactors.JacobiMomentZeros
import PrimeFactors.JacobiPeriodProbe
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Periodic

/-!
# Two consecutive moments determine a shared period

Within one local period, consecutive central binomial coefficients obey a
first-order relation. Substituting the pair (2,6) forces the first coefficient
to be at half-degree one. The two possible boundary positions never give that
pair. Chinese remaindering transfers the criterion to the public product.
-/

namespace PrimeFactors.JacobiTwoMomentPeriod

open JacobiMomentPeriod JacobiMomentRecurrence JacobiMomentZeros ProjectiveWordMoments

/-- Local component at even degree 2j. -/
noncomputable def halfMoment (p : ℕ) [Fact p.Prime] (j : ℕ) : ZMod p := component p (2*j)

/-- Before the positive boundary at half-degree (p−1)/2, the moment is the
ordinary central binomial coefficient. -/
theorem interior_value {p j : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (positive : 0 < j)
    (small : j < (p-1)/2) : halfMoment p j = (j.centralBinom : ZMod p) := by
  have low : 2*j<p-1 := by omega
  rw [halfMoment,at_remainder (by omega) (by omega) (Nat.not_dvd_of_pos_of_lt (by omega) low),
    Nat.mod_eq_of_lt low, central, if_pos (by omega), Nat.mul_div_cancel_left _ (by decide : 0<2)]
  rfl

/-- All such interior moments are nonzero in the prime field. -/
theorem interior_ne_zero {p j : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (positive : 0 < j)
    (small : j < (p-1)/2) : halfMoment p j ≠ 0 := by
  intro zero
  have h := (local_zero_iff (show p≠2 by omega) (show 0<2*j by omega) (by omega)).mp zero
  exact Nat.not_dvd_of_pos_of_lt (by omega) (show 2*j<p-1 by omega) h.2

/-- Two interior half-degrees satisfy the central binomial recurrence in
the prime field. No coefficient division is required. -/
theorem interior_recurrence {p j : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (positive : 0 < j)
    (small : j+1 < (p-1)/2) :
    ((j : ZMod p)+1)*halfMoment p (j+1) = (4*(j : ZMod p)+2)*halfMoment p j := by
  rw [interior_value hp (by omega) small, interior_value hp positive (by omega)]
  have h := congrArg (fun n : ℕ => (n : ZMod p)) (Nat.succ_mul_centralBinom_succ j)
  push_cast at h
  linear_combination h

/-- On two interior half-degrees, subtracting four times the first moment
from the next leaves a nonzero field element. -/
theorem interior_difference_ne_zero {p j : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (positive : 0 < j) (small : j+1 < (p-1)/2) :
    halfMoment p (j+1) - 4*halfMoment p j ≠ 0 := by
  have relation : ((j : ZMod p)+1) * (halfMoment p (j+1) - 4*halfMoment p j) =
      -2*halfMoment p j := by
    linear_combination interior_recurrence hp positive small
  have two : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
  intro zero
  rw [zero,mul_zero] at relation
  exact mul_ne_zero (neg_ne_zero.mpr two) (interior_ne_zero hp positive (by omega)) relation.symm

private theorem cast_inj {p u v : ℕ} (lu : u<p) (lv : v<p) (h : (u : ZMod p)=v) : u=v := by
  have rel := (ZMod.natCast_eq_natCast_iff' u v p).mp h
  simpa only [Nat.mod_eq_of_lt lu,Nat.mod_eq_of_lt lv] using rel

/-- The pair (2,6) occurs at precisely the starts of full local periods. -/
theorem local_pair {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (d : ℕ) :
    localPeriod p ∣ d ↔ localEven p d=2 ∧ localEven p (d+1)=6 := by
  let a := (p-1)/2
  have ha : 3≤a := by dsimp [a]; omega
  have period : localPeriod p=a := if_neg (by omega)
  obtain ⟨u,hu⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hpred : 2*a=p-1 := by dsimp [a]; omega
  have first : halfMoment p 1=2 := by
    simpa only [show Nat.centralBinom 1=2 by decide,Nat.cast_ofNat] using
      interior_value (j:=1) hp (by decide) (by omega)
  have second : halfMoment p 2=6 := by
    simpa only [show Nat.centralBinom 2=6 by decide,Nat.cast_ofNat] using
      interior_value (j:=2) hp (by decide) (by omega)
  have base : localEven p 0=2 := first
  have after : localEven p 1=6 := second
  have cyc : Function.Periodic (localEven p) a :=
    (local_iff (by omega) a).mpr (period ▸ dvd_rfl)
  have nextCyc : Function.Periodic (fun k => localEven p (k+1)) a := by
    intro k
    change localEven p (k+a+1)=localEven p (k+1)
    rw [Nat.add_right_comm k a 1,cyc (k+1)]
  let r := d%a
  have rlt : r<a := Nat.mod_lt _ (by omega)
  have at0 : localEven p r=localEven p d := cyc.map_mod_nat d
  have at1 : localEven p (r+1)=localEven p (d+1) := nextCyc.map_mod_nat d
  rw [←at0,←at1,period]
  constructor
  · intro div
    have zero : r=0 := Nat.mod_eq_zero_of_dvd div
    rw [zero]; exact ⟨base,after⟩
  · rintro ⟨val,adj⟩
    have distinct : (2 : ZMod p)≠6 := fun eqn =>
      (by decide : (2:ℕ)≠6) (cast_inj (by omega : 2<p) (by omega : 6<p) eqn)
    have small : r+2<a := by
      by_contra no
      have boundaries : r+1=a ∨ r+2=a := by omega
      rcases boundaries with edge | edge
      · rw [edge,show a=0+a by omega,cyc 0] at adj
        exact distinct (base.symm.trans adj)
      · change halfMoment p (r+2)=6 at adj
        rw [edge,halfMoment,hpred,value_at_multiple (by omega) (by omega) dvd_rfl] at adj
        rcases neg_one_pow_eq_or (ZMod p) ((p-1)/2) with sign | sign
        · rw [sign, one_add_one_eq_two] at adj
          exact distinct adj
        · rw [sign,add_neg_cancel] at adj
          exact (by decide : (0:ℕ)≠6) (cast_inj (by omega : 0<p) (by omega : 6<p) (by simpa only [Nat.cast_zero,Nat.cast_ofNat] using adj))
    change halfMoment p (r+1)=2 at val
    change halfMoment p (r+1+1)=6 at adj
    have rel := interior_recurrence (j:=r+1) hp (by omega) small
    rw [val,adj] at rel
    have two : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
    have index : ((r+1 : ℕ) : ZMod p) = 1 := by
      apply mul_left_cancel₀ two
      linear_combination -rel
    have one : r+1=1 := cast_inj (by omega) (by omega : 1<p) (by simpa only [Nat.cast_one] using index)
    exact Nat.dvd_of_mod_eq_zero (show r=0 by omega)

private theorem crt_value {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 7 ≤ p) (hq : 7 ≤ q) (j v : ℕ) :
    completeEven (p*q) j=(v : ZMod (p*q)) ↔ localEven p j=(v : ZMod p) ∧ localEven q j=(v : ZMod q) := by
  let e := ZMod.chineseRemainder cop
  have pair : e (completeEven (p*q) j) = (localEven p j,localEven q j) :=
    components cop (by omega) (by omega) _
  rw [←e.injective.eq_iff, pair, map_natCast, Prod.ext_iff]
  rfl

/-- Two evaluations at the public degrees 2(d+1) and 2(d+2) decide whether
a shift preserves every complete positive even Jacobi moment. -/
theorem two_moments {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 7 ≤ p) (hq : 7 ≤ q) (d : ℕ) :
    Function.Periodic (completeEven (p*q)) d ↔
      completeEven (p*q) d=2 ∧ completeEven (p*q) (d+1)=6 := by
  have x := crt_value cop hp hq d 2
  have y := crt_value cop hp hq (d+1) 6
  simp only [Nat.cast_ofNat] at x y
  rw [composite_iff cop (by omega) (by omega),Nat.lcm_dvd_iff,local_pair hp,local_pair hq,x,y]
  tauto

/-- The same two moments, with d=s*t, test a proposed repeat at every
starting offset of an arbitrary stride s. -/
theorem all_offsets {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 7 ≤ p) (hq : 7 ≤ q) (s t : ℕ) :
    JacobiPeriodProbe.AllOffsets (completeEven (p*q)) s t ↔
      completeEven (p*q) (s*t)=2 ∧ completeEven (p*q) (s*t+1)=6 := by
  rw [JacobiPeriodProbe.allOffsets_iff, two_moments cop hp hq]

/-- The same product witnesses that either test can pass alone. At the
false shifts three and twelve, respectively, only the first or only the
second comparison passes. -/
theorem sharp119 :
    (completeEven 119 3=2 ∧ ¬Function.Periodic (completeEven 119) 3) ∧
    (completeEven 119 13=6 ∧ ¬Function.Periodic (completeEven 119) 12) := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  have cop : (7:ℕ).Coprime 17 := by decide
  have per (d : ℕ) := composite_iff cop (by decide) (by decide) d
  have v2 := crt_value cop (by decide) (by decide) 3 2
  have v6 := crt_value cop (by decide) (by decide) 13 6
  simp only [Nat.cast_ofNat] at v2 v6
  refine ⟨⟨v2.mpr ⟨?_,?_⟩,fun h => (by decide : ¬24∣3) ((per 3).mp h)⟩,
    ⟨v6.mpr ⟨?_,?_⟩,fun h => (by decide : ¬24∣12) ((per 12).mp h)⟩⟩
  all_goals
    unfold localEven
    rw [at_remainder (by decide) (by decide) (by decide)]
    decide +kernel

end PrimeFactors.JacobiTwoMomentPeriod
