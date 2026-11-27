import PrimeFactors.JacobiMomentPeriod
import PrimeFactors.JacobiSparseSupport

/-!
# Three-term recurrences for the positive even Jacobi moments

For three unit coefficients, vanishing sums in each exponent class force
the support into one class at each prime. Thus every offset difference is a
global period. Four shifts allow two different pairings at the two primes.
-/

namespace PrimeFactors.JacobiThreeTerms

open Finset JacobiMomentPeriod JacobiMomentRecurrence
open scoped Polynomial

/-- Three nonzero weights cannot form two or more nonempty buckets of sum zero.
The argument works in any additive commutative monoid. -/
theorem three_one_residue {R : Type*} [AddCommMonoid R] {S : Finset ℕ}
    (d : ℕ) (pos : 0<d) (count : S.card=3) (w : ℕ → R)
    (active : ∀ j ∈ S, w j ≠ 0)
    (cancel : ∀ r < d, (∑ j ∈ S.filter (fun k => k%d=r), w j) = 0) :
    ∀ i ∈ S, ∀ j ∈ S, i ≡ j [MOD d] := by
  classical
  have no_single (a b c : ℕ) (set : S = {a,b,c}) : a%d=b%d ∨ a%d=c%d := by
    by_contra! h
    have only : S.filter (fun k => k%d=a%d) = {a} := by
      ext k
      simp only [set, mem_filter,mem_insert,mem_singleton]
      constructor
      · rintro ⟨(rfl|rfl|rfl),eqn⟩
        · rfl
        · exact False.elim (h.1 eqn.symm)
        · exact False.elim (h.2 eqn.symm)
      · rintro rfl
        exact ⟨Or.inl rfl,rfl⟩
    have eqn := cancel (a%d) (Nat.mod_lt _ pos)
    rw [only,sum_singleton] at eqn
    exact active a (by simp [set]) eqn
  obtain ⟨a,b,c,_,_,_,eqn⟩ := card_eq_three.mp count
  have ha := no_single a b c eqn
  have hb := no_single b a c (by rw [eqn,Finset.insert_comm])
  have hc := no_single c a b (by rw [eqn]; ext k; simp only [mem_insert,mem_singleton]; tauto)
  have ab : a%d=b%d := by omega
  have ac : a%d=c%d := by omega
  have all (i : ℕ) (hi : i∈S) : i%d=a%d := by
    rw [eqn] at hi
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with h|h|h <;> subst i <;> omega
  exact fun i hi j hj => (all i hi).trans (all j hj).symm

private theorem at_prime {N p : ℕ} [NeZero N] [Fact p.Prime] (large : 11≤p)
    (f : ZMod N →+* ZMod p)
    (project : ∀ k, f (ProjectiveWordMoments.moment N k) = component p k)
    (P : (ZMod N)[X]) (three : P.support.card = 3)
    (units : ∀ j ∈ P.support, IsUnit (P.coeff j))
    (fit : ∀ n, shift P (completeEven N) n = 0) :
    ∀ i ∈ P.support, ∀ j ∈ P.support, i ≡ j [MOD localPeriod p] := by
  rw [show localPeriod p = (p-1)/2 from if_neg (by omega)]
  apply three_one_residue _ (by omega) three (fun j => f (P.coeff j))
  · exact fun j hj => ((units j hj).map f).ne_zero
  · exact fun _ hr => JacobiSparseSupport.projected_buckets (by omega) f project P (by omega) fit hr

/-- At two distinct primes at least eleven, all three unit-coefficient exponents
in a recurrence lie in one congruence class modulo the true even period. -/
theorem composite {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 11≤p) (hq : 11≤q) (P : (ZMod (p*q))[X]) (three : P.support.card = 3)
    (units : ∀ j ∈ P.support, IsUnit (P.coeff j))
    (fit : ∀ n, shift P (completeEven (p*q)) n = 0) :
    ∀ i ∈ P.support, ∀ j ∈ P.support, i ≡ j [MOD (localPeriod p).lcm (localPeriod q)] := by
  let e := ZMod.chineseRemainder cop
  have crt := ProjectiveWordMoments.components cop (show p≠2 by omega) (show q≠2 by omega)
  have left := at_prime hp ((RingHom.fst _ _).comp e.toRingHom)
    (fun k => congrArg Prod.fst (crt k)) P three units fit
  have right := at_prime hq ((RingHom.snd _ _).comp e.toRingHom)
    (fun k => congrArg Prod.snd (crt k)) P three units fit
  exact fun i hi j hj => Nat.mod_lcm (left i hi j hj) (right i hi j hj)

/-- The difference between any two ordered offsets already preserves every
positive even Jacobi moment modulo the product. -/
theorem periodic_gaps {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 11≤p) (hq : 11≤q) (P : (ZMod (p*q))[X]) (three : P.support.card = 3)
    (units : ∀ j ∈ P.support, IsUnit (P.coeff j))
    (fit : ∀ n, shift P (completeEven (p*q)) n = 0)
    {i j : ℕ} (hi : i ∈ P.support) (hj : j ∈ P.support) (ordered : i≤j) :
    Function.Periodic (completeEven (p*q)) (j-i) := by
  apply (composite_iff cop (by omega) (by omega) _).mpr
  exact (Nat.modEq_iff_dvd' ordered).mp (composite cop hp hq P three units fit i hi j hj)

/-- The three distinct shifts, in increasing order, span at least two full periods. -/
theorem two_periods_le_span {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 11≤p) (hq : 11≤q) (P : (ZMod (p*q))[X]) (three : P.support.card = 3)
    (units : ∀ j ∈ P.support, IsUnit (P.coeff j))
    (fit : ∀ n, shift P (completeEven (p*q)) n = 0) {a b c : ℕ}
    (ha : a ∈ P.support) (hb : b ∈ P.support) (hc : c ∈ P.support)
    (ab : a < b) (bc : b < c) :
    2*(localPeriod p).lcm (localPeriod q) ≤ c-a := by
  have offsets := composite cop hp hq P three units fit
  have first := Nat.le_of_dvd (Nat.sub_pos_of_lt ab) ((Nat.modEq_iff_dvd' ab.le).mp (offsets a ha b hb))
  have second := Nat.le_of_dvd (Nat.sub_pos_of_lt bc) ((Nat.modEq_iff_dvd' bc.le).mp (offsets b hb c hc))
  omega

/-- The two local binomials give a four-term global relation, even when none
of the four shift differences are global periods. -/
theorem four_terms {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (i : ℕ) :
    completeEven (p*q) (i+localPeriod p+localPeriod q) + completeEven (p*q) i =
      completeEven (p*q) (i+localPeriod p) + completeEven (p*q) (i+localPeriod q) := by
  let e := ZMod.chineseRemainder cop
  have crt (j : ℕ) : e (completeEven (p*q) j) = (localEven p j, localEven q j) :=
    ProjectiveWordMoments.components cop hp hq _
  have lp := (local_iff hp (localPeriod p)).mpr dvd_rfl
  have lq := (local_iff hq (localPeriod q)).mpr dvd_rfl
  apply e.injective
  rw [map_add,map_add,crt,crt,crt,crt]
  apply Prod.ext
  · change localEven p _ + localEven p _ = localEven p _ + localEven p _
    rw [Nat.add_right_comm i (localPeriod p) (localPeriod q),lp _,lp _,add_comm]
  · change localEven q _ + localEven q _ = localEven q _ + localEven q _
    rw [lq _,lq _]

local instance prime11 : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance prime13 : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance prime7 : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- At 143, all four offsets are different modulo the true even period of 30. -/
theorem sharp143 :
    (∀ i, completeEven 143 (i+11) + completeEven 143 i =
      completeEven 143 (i+5) + completeEven 143 (i+6)) ∧
    (∀ t, Function.Periodic (completeEven 143) t ↔ 30 ∣ t) ∧
    (({0,5,6,11} : Finset ℕ).image (· % 30)).card = 4 := by
  refine ⟨?_,?_,by decide⟩
  · intro i
    have h := four_terms (p:=11) (q:=13) (by decide) (by decide) (by decide) i
    change completeEven 143 (i+5+6) + _ = _ at h
    simpa only [Nat.add_assoc] using h
  · exact fun t => composite_iff (p:=11) (q:=13) (by decide) (by decide) (by decide) t

private theorem signal_three {F : Type*} [Field F] (S : Finset F) (w : F → F)
    (A B : F) (k l i : ℕ) (roots : ∀ z ∈ S, z^k+A*z^l+B=0) :
    signal S w (i+k) + A*signal S w (i+l) + B*signal S w i = 0 := by
  simp only [signal, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro z hz
  rw [pow_add,pow_add]
  linear_combination w z * z^i * roots z hz

/-- The lower threshold matters. This genuine three-unit relation at 77
uses three distinct offsets modulo its even period of 15. -/
theorem below_threshold77 :
    (∀ i, completeEven 77 (i+10) + 23*completeEven 77 (i+5) + 53*completeEven 77 i = 0) ∧
    (∀ t, Function.Periodic (completeEven 77) t ↔ 15 ∣ t) ∧
    IsUnit (23 : ZMod 77) ∧ IsUnit (53 : ZMod 77) ∧
    (({0,5,10} : Finset ℕ).image (· % 15)).card = 3 := by
  have roots7 : ∀ z ∈ evenBases 7, z^(10:ℕ)+23*z^(5:ℕ)+53=0 := by decide +kernel
  have roots11 : ∀ z ∈ evenBases 11, z^(10:ℕ)+23*z^(5:ℕ)+53=0 := by decide +kernel
  have cop : Nat.Coprime 7 11 := by decide
  have crt (j : ℕ) : ZMod.chineseRemainder cop (completeEven 77 j) =
      (localEven 7 j, localEven 11 j) :=
    ProjectiveWordMoments.components cop (by decide) (by decide) _
  refine ⟨?_,fun t => composite_iff cop (by decide) (by decide) t,?_,?_,by decide⟩
  · intro i
    apply (ZMod.chineseRemainder cop).injective
    simp only [map_add,map_mul,map_ofNat,map_zero,crt]
    apply Prod.ext
    · change localEven 7 (i+10) + 23*localEven 7 (i+5) + 53*localEven 7 i = 0
      simp only [localEven,component_even (p:=7) (by decide)]
      exact signal_three _ _ _ _ _ _ _ roots7
    · change localEven 11 (i+10) + 23*localEven 11 (i+5) + 53*localEven 11 i = 0
      simp only [localEven,component_even (p:=11) (by decide)]
      exact signal_three _ _ _ _ _ _ _ roots11
  · exact (ZMod.isUnit_iff_coprime 23 77).mpr (by decide)
  · exact (ZMod.isUnit_iff_coprime 53 77).mpr (by decide)

end PrimeFactors.JacobiThreeTerms
