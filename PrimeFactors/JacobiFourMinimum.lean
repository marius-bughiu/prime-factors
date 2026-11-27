import PrimeFactors.JacobiFourSpan
import PrimeFactors.JacobiFourUpper
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Data.Finset.Sort

/-!
# Least span of four unit coefficients in a Jacobi recurrence

The span measures the distance from the first to the last nonzero coefficient.
Vanishing of the projected coefficient sums prevents either half-order modulus
from having a singleton class. The matching upper bounds use four signed terms.
-/

namespace PrimeFactors.JacobiFourMinimum

open Finset Polynomial JacobiMomentRecurrence JacobiMomentPeriod JacobiFourSpan

/-- Spans of four-term unit-coefficient recurrences for all positive even moments. -/
def actualSpans (N : ℕ) [NeZero N] : Set ℕ :=
  {d | ∃ P : (ZMod N)[X], P.support.card = 4 ∧
    (∀ j ∈ P.support, IsUnit (P.coeff j)) ∧
    (∀ i, shift P (completeEven N) i = 0) ∧
    P.natDegree - P.natTrailingDegree = d}

private theorem at_prime {N p : ℕ} [NeZero N] [Fact p.Prime] (large : 11 ≤ p)
    (f : ZMod N →+* ZMod p) (project : ∀ k, f (ProjectiveWordMoments.moment N k) = component p k)
    (P : (ZMod N)[X]) (four : P.support.card = 4)
    (units : ∀ j ∈ P.support, IsUnit (P.coeff j))
    (fit : ∀ i, shift P (completeEven N) i = 0) : NoSingleton ((p-1)/2) P.support :=
  noSingleton_of_zero_buckets (by omega) P.support (fun j => f (P.coeff j))
    (fun j hj => ((units j hj).map f).ne_zero)
    (fun _ hr => JacobiSparseSupport.projected_buckets (by omega) f project P (by omega) fit hr)

/-- Both hidden half-order moduli have a partner for every exponent. -/
theorem paired_support {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 11 ≤ p) (hq : 11 ≤ q) (P : (ZMod (p*q))[X]) (four : P.support.card = 4)
    (units : ∀ j ∈ P.support, IsUnit (P.coeff j))
    (fit : ∀ i, shift P (completeEven (p*q)) i = 0) :
    NoSingleton ((p-1)/2) P.support ∧ NoSingleton ((q-1)/2) P.support := by
  have crt := ProjectiveWordMoments.components cop (show p ≠ 2 by omega) (show q ≠ 2 by omega)
  let e := ZMod.chineseRemainder cop
  exact ⟨at_prime hp ((RingHom.fst _ _).comp e.toRingHom) (fun k => congrArg Prod.fst (crt k))
    P four units fit,
    at_prime hq ((RingHom.snd _ _).comp e.toRingHom) (fun k => congrArg Prod.snd (crt k))
    P four units fit⟩

private theorem sorted_four (S : Finset ℕ) (four : S.card = 4) :
    ∃ l x y z : ℕ, l < x ∧ x < y ∧ y < z ∧ S = {l,x,y,z} := by
  let f := S.orderEmbOfFin four
  refine ⟨f 0, f 1, f 2, f 3, f.strictMono (by decide : (0 : Fin 4) < 1),
    f.strictMono (by decide : (1 : Fin 4) < 2), f.strictMono (by decide : (2 : Fin 4) < 3), ?_⟩
  ext t
  constructor
  · intro ht
    have mem : t ∈ Set.range f := by rwa [Finset.range_orderEmbOfFin]
    obtain ⟨i,rfl⟩ := mem
    fin_cases i <;> simp
  · intro ht
    simp only [mem_insert,mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> exact orderEmbOfFin_mem _ _ _

private theorem span_of_support {R : Type*} [Semiring R] (P : R[X]) {l x y z : ℕ}
    (lx : l < x) (xy : x < y) (yz : y < z) (support : P.support = {l,x,y,z}) :
    P.natDegree - P.natTrailingDegree = z-l := by
  have hmin : l ∈ P.support := by simp [support]
  have hmax : z ∈ P.support := by simp [support]
  have nz := nonempty_support_iff.mp ⟨l,hmin⟩
  have top := natDegree_mem_support_of_nonzero nz
  have first := natTrailingDegree_mem_support_of_nonzero nz
  rw [support] at top first
  simp only [mem_insert,mem_singleton] at top first
  have lower := natTrailingDegree_le_of_mem_supp _ hmin
  have upper := le_natDegree_of_mem_supp _ hmax
  omega

/-- A bound for any actual recurrence, including translated supports. -/
theorem lower {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : 11 ≤ p) (hq : 11 ≤ q)
    (ab : (p-1)/2 < (q-1)/2) (ba : (q-1)/2 < 2*((p-1)/2))
    {D : ℕ} (actual : D ∈ actualSpans (p*q)) :
    (if 2*((q-1)/2) = 3*((p-1)/2) then 2*((p-1)/2) else (p-1)/2 + (q-1)/2) ≤ D := by
  obtain ⟨P, four, units, fit, rfl⟩ := actual
  obtain ⟨pa,pb⟩ := paired_support cop hp hq P four units fit
  obtain ⟨l,x,y,z,lx,xy,yz,hs⟩ := sorted_four P.support four
  rw [span_of_support P lx xy yz hs]
  rw [hs] at pa pb
  by_cases short : z-l < (p-1)/2 + (q-1)/2
  · obtain ⟨ratio,_,_,last⟩ := four_short_from ab ba lx xy yz short pa pb
    simp [ratio,last]
  · split_ifs <;> omega

private theorem realized {N : ℕ} [NeZero N] {x y z : ℕ} (xp : 0 < x) (xy : x < y) (yz : y < z)
    (witness : ∃ P : (ZMod N)[X], P.Monic ∧ P.support = {0,x,y,z} ∧
      (∀ j ∈ P.support, IsUnit (P.coeff j)) ∧ ∀ i, shift P (completeEven N) i = 0) :
    z ∈ actualSpans N := by
  obtain ⟨P,_,hs,units,fit⟩ := witness
  refine ⟨P, ?_, units, fit, ?_⟩
  · simp [hs, show x ≠ y by omega, show x ≠ z by omega, show y ≠ z by omega,
      show 0 ≠ x by omega, show 0 ≠ y by omega, show 0 ≠ z by omega]
  · simpa using span_of_support P xp xy yz hs

/-- The stated minimum has an explicit monic witness, including its support. -/
theorem attaining {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : 11 ≤ p) (hq : 11 ≤ q) (ab : (p-1)/2 < (q-1)/2) :
    let a := (p-1)/2
    let b := (q-1)/2
    ∃ P : (ZMod (p*q))[X], P.Monic ∧
      P.support = (if 2*b = 3*a then {0,b-a,b,2*a} else {0,a,b,a+b}) ∧
      (∀ j ∈ P.support, IsUnit (P.coeff j)) ∧ ∀ i, shift P (completeEven (p*q)) i = 0 := by
  dsimp only
  let a := (p-1)/2
  let b := (q-1)/2
  have left : localPeriod p = a := if_neg (by omega)
  have right : localPeriod q = b := if_neg (by omega)
  change a < b at ab
  by_cases ratio : 2*b = 3*a
  · rw [if_pos ratio]
    let h := b-a
    have ah : a = 2*h := by dsimp [h]; omega
    have bh : b = 3*h := by dsimp [h]; omega
    obtain ⟨P, mon, supp, units, fit⟩ := JacobiFourUpper.exceptional_witness cop
      (by omega) (by omega) (show 0 < h by dsimp [h]; omega) (left.trans ah) (right.trans bh)
    refine ⟨P,mon,?_,units,fit⟩
    change P.support = {0,h,b,2*a}
    rw [supp,bh,show 2*a=4*h by omega]
  · rw [if_neg ratio]
    exact JacobiFourUpper.generic_witness cop (by omega) (by omega) left right
      (show 0 < (p-1)/2 by omega) ab

/-- The exact least span over all four-term unit-coefficient recurrences,
with arbitrary starting exponent and all positive even moments. -/
theorem least_span {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : 11 ≤ p) (hq : 11 ≤ q)
    (ab : (p-1)/2 < (q-1)/2) (ba : (q-1)/2 < 2*((p-1)/2)) :
    let a := (p-1)/2
    let b := (q-1)/2
    IsLeast (actualSpans (p*q)) (if 2*b = 3*a then 2*a else a+b) := by
  dsimp only
  refine ⟨?_, fun _ h => lower cop hp hq ab ba h⟩
  have found := attaining cop hp hq ab
  dsimp only at found
  split_ifs with ratio
  · rw [if_pos ratio] at found
    exact realized (by omega) (by omega) (by omega) found
  · rw [if_neg ratio] at found
    exact realized (by omega) ab (by omega) found

/-- Distinct odd primes in the same interval [2h,4h) automatically meet
the ratio hypotheses in the exact formula. -/
theorem same_width {p q h : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : 11 ≤ p) (hq : 11 ≤ q)
    (ordered : p < q) (lo : 2*h ≤ p) (hi : q < 4*h) :
    let a := (p-1)/2
    let b := (q-1)/2
    IsLeast (actualSpans (p*q)) (if 2*b = 3*a then 2*a else a+b) := by
  obtain ⟨i, he⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨j, hf⟩ := (Fact.out : q.Prime).odd_of_ne_two (by omega)
  exact least_span cop hp hq (by omega) (by omega)

end PrimeFactors.JacobiFourMinimum
