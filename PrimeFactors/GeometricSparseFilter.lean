import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! A polynomial with few nonzero coefficients cannot mark an isolated long
run of consecutive powers. The propagation argument also works with zero
divisors. Eliminating all competing terms gives the column-wise Vandermonde
product and an explicit alternative over a composite modulus. -/

namespace PrimeFactors.GeometricSparseFilter
open Finset Polynomial
variable {R : Type*} [CommRing R]

/-- Exponential sum in the index i, with labeled weights c and frequencies u. -/
noncomputable def reading (S : Finset ℕ) (c u : ℕ → R) (i : ℕ) : R :=
  ∑ k ∈ S, c k*(u k)^i

/-- The difference F(i+1)−u(b)F(i) removes one frequency without division. -/
private theorem step {S : Finset ℕ} {b : ℕ} (fresh : b∉S) (c u : ℕ → R) (i : ℕ) :
    reading (insert b S) c u (i+1) - u b*reading (insert b S) c u i =
      reading S (fun k => c k*(u k-u b)) u i := by
  simp only [reading, sum_insert fresh, pow_succ, mul_add, mul_sum]
  have tail : (∑ k ∈ S, c k*((u k)^i*u k)) - ∑ k ∈ S, u b*(c k*(u k)^i) =
      ∑ k ∈ S, c k*(u k-u b)*(u k)^i := by
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    ring
  rw [←tail]
  ring

/-- s consecutive zero readings of an s-term exponential sum propagate to
all following indices, with no distinctness or nonzero assumptions. -/
theorem propagate (S : Finset ℕ) (c u : ℕ → R)
    (zeros : ∀ i < S.card, reading S c u i = 0) : ∀ i, reading S c u i = 0 := by
  induction S using Finset.induction_on generalizing c with
  | empty => simp [reading]
  | @insert b S fresh ih =>
    have old (k : ℕ) (hk : k<S.card+1) : reading (insert b S) c u k=0 :=
      zeros k (by rwa [card_insert_of_not_mem fresh])
    have reduced := ih (fun k => c k*(u k-u b)) (fun i hi => by
      rw [←step fresh c u, old _ (by omega), old _ (by omega), mul_zero, sub_zero])
    intro i
    induction i with
    | zero => exact old 0 (by omega)
    | succ i hi =>
      have next := (step fresh c u i).trans (reduced i)
      rwa [hi, mul_zero, sub_zero] at next

/-- Isolating one column of the Vandermonde system needs only its own
product of frequency differences. This form is valid over composite moduli. -/
theorem column {j : ℕ} (T : Finset ℕ) (absent : j∉T) (c u : ℕ → R)
    (zeros : ∀ i < T.card+1, reading (insert j T) c u i=0) :
    c j*(∏ k ∈ T, (u j-u k))=0 := by
  induction T using Finset.induction_on generalizing c with
  | empty => simpa [reading] using zeros 0 (by simp)
  | @insert b T fresh ih =>
    have jb : j≠b := fun e => absent (e ▸ mem_insert_self b T)
    have jt : j∉T := fun h => absent (mem_insert_of_mem h)
    have bt : b∉insert j T := by simpa [jb.symm] using fresh
    have old (k : ℕ) (hk : k<T.card+2) : reading (insert b (insert j T)) c u k=0 :=
      insert_comm b j T ▸ zeros k (by rwa [card_insert_of_not_mem fresh])
    have eq := ih jt (fun k => c k*(u k-u b)) (fun i hi => by
      rw [←step bt c u, old _ (by omega), old _ (by omega), mul_zero, sub_zero])
    simpa only [prod_insert fresh, mul_assoc] using eq

/-- Evaluation on a geometric progression has exactly the polynomial's
support as labeled terms, regardless of the degree of its largest exponent. -/
theorem eval_reading (P : R[X]) (a g : R) (i : ℕ) :
    P.eval (a*g^i) = reading P.support (fun k => P.coeff k*a^k) (fun k => g^k) i := by
  rw [eval_eq_sum, Polynomial.sum_def]
  apply sum_congr rfl
  intro k _
  rw [mul_pow, ←pow_mul, Nat.mul_comm i k, pow_mul, mul_assoc]

/-- An exact zero/nonzero boundary following L zero points costs at least
L+1 nonzero monomials. The claim is about sparse representations, not the
complexity of evaluating a succinctly represented dense polynomial. -/
theorem support_bound (P : R[X]) (a g : R) {L : ℕ}
    (block : ∀ i<L, P.eval (a*g^i)=0) (next : P.eval (a*g^L)≠0) : L+1≤P.support.card := by
  by_contra! few
  have zero := propagate P.support (fun k => P.coeff k*a^k) (fun k => g^k)
    (fun i hi => (eval_reading P a g i).symm.trans (block i (by omega))) L
  exact next ((eval_reading P a g L).trans zero)

/-- The explicit block polynomial attains the support bound whenever the next
point is distinct from every preceding point in an integral domain. -/
theorem sharp {K : Type*} [CommRing K] [IsDomain K] (a g : K) (L : ℕ)
    (separate : ∀ i<L, a*g^L≠a*g^i) :
    let P := ∏ i ∈ range L, (X-C (a*g^i))
    (∀ i<L, P.eval (a*g^i)=0) ∧ P.eval (a*g^L)≠0 ∧ P.support.card=L+1 := by
  let P := ∏ i ∈ range L, (X-C (a*g^i))
  have val (k : ℕ) : P.eval (a*g^k)=∏ i ∈ range L, (a*g^k-a*g^i) := by
    simp only [P,eval_prod,eval_sub,eval_X,eval_C]
  have block (i : ℕ) (hi : i<L) : P.eval (a*g^i)=0 := by
    rw [val]; exact prod_eq_zero (mem_range.mpr hi) (sub_self _)
  have next : P.eval (a*g^L)≠0 := by
    rw [val]; exact prod_ne_zero_iff.mpr (fun k hk => sub_ne_zero.mpr (separate k (mem_range.mp hk)))
  have deg : P.natDegree=L := (natDegree_finset_prod_X_sub_C_eq_card _ _).trans (card_range L)
  have limit : P.support ⊆ range (L+1) := fun i hi => mem_range.mpr
    (Nat.lt_succ_of_le ((le_natDegree_of_mem_supp i hi).trans_eq deg))
  exact ⟨block,next,Nat.le_antisymm ((card_le_card limit).trans_eq (card_range _)) (support_bound P a g block next)⟩

/-- A nonzero residue which is a nonunit yields a proper gcd. -/
private theorem proper {n : ℕ} [NeZero n] {x : ZMod n} (nz : x≠0) (bad : ¬IsUnit x) :
    1 < x.val.gcd n ∧ x.val.gcd n < n := by
  have one : x.val.gcd n≠1 := by
    intro coprime
    exact bad (ZMod.natCast_zmod_val x ▸ (ZMod.isUnit_iff_coprime x.val n).mpr coprime)
  have pos := Nat.gcd_pos_of_pos_right x.val (NeZero.pos n)
  have xv : 0<x.val := Nat.pos_of_ne_zero (fun h => nz ((ZMod.val_eq_zero x).mp h))
  exact ⟨by omega,(Nat.le_of_dvd xv (Nat.gcd_dvd_left ..)).trans_lt (ZMod.val_lt x)⟩

/-- If the distinguished weight is nonzero and its frequency is distinct
from every competitor modulo N, a long zero run exposes a proper factor in
that weight or in one of its frequency differences. -/
theorem factor_or_alias {n : ℕ} [NeZero n] (large : 1<n) {j : ℕ} (T : Finset ℕ)
    (absent : j∉T) (c u : ℕ → ZMod n) (nz : c j≠0)
    (zeros : ∀ i < T.card+1, reading (insert j T) c u i=0) :
    (∃ k∈T, u j=u k) ∨ (1<(c j).val.gcd n ∧ (c j).val.gcd n<n) ∨
      ∃ k∈T, 1<(u j-u k).val.gcd n ∧ (u j-u k).val.gcd n<n := by
  by_cases same : ∃ k∈T, u j=u k
  · exact Or.inl same
  right
  by_cases cu : IsUnit (c j)
  · right
    haveI : Fact (1<n) := ⟨large⟩
    by_contra! failure
    have diffs : ∀ k∈T, IsUnit (u j-u k) := by
      intro k hk
      by_contra bad
      obtain ⟨lo,hi⟩ := proper (sub_ne_zero.mpr (fun e => same ⟨k,hk,e⟩)) bad
      exact (Nat.not_le_of_lt hi) (failure k hk lo)
    exact (cu.mul (IsUnit.prod_iff.mpr diffs)).ne_zero (column T absent c u zeros)
  · exact Or.inl (proper nz cu)

/-- The dense geometric sum at a dyadic order can be evaluated by successive
squaring and one multiplication per level. -/
noncomputable def binarySum (s : ℕ) (x : R) : R := ∏ i ∈ range s, (1+x^(2^i))

theorem binary_identity (s : ℕ) (x : R) : (x-1)*binarySum s x = x^(2^s)-1 := by
  induction s with
  | zero => simp [binarySum]
  | succ s ih =>
    rw [show binarySum (s+1) x = binarySum s x*(1+x^(2^s)) by simp [binarySum,prod_range_succ],
      ←mul_assoc,ih,pow_succ 2 s,pow_mul]
    ring

/-- Known dyadic torsion gives a short arithmetic circuit despite the support
bound: among the 2^s-th roots, only the identity has a nonzero reading. -/
theorem known_period {K : Type*} [CommRing K] [IsDomain K] (s : ℕ) {x : K}
    (period : x^(2^s)=1) (odd : (2:K)≠0) : binarySum s x≠0 ↔ x=1 := by
  constructor
  · intro nonzero
    have h := binary_identity s x
    rw [period,sub_self,mul_eq_zero] at h
    exact sub_eq_zero.mp (h.resolve_right nonzero)
  · rintro rfl
    simpa [binarySum, one_add_one_eq_two] using pow_ne_zero s odd

end PrimeFactors.GeometricSparseFilter
