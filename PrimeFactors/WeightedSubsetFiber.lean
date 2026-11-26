import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-! Count the products compatible with one fixed positive weighted square excess.
A square dependency of any length can force its squarefree part to divide the
same integer `M`. Counting positive square multiples separately for each
squarefree part gives an Euler product in place of a uniform divisor count. -/

namespace PrimeFactors.WeightedSubsetFiber
open Finset

/-- The squarefree part of a positive excess divides `M`, and the excess is at
most `U²`. The label and the weight are fixed for every product in the fiber. -/
def InFiber (r A M U n : ℕ) : Prop :=
  ∃ m u : ℕ, Squarefree m ∧ m ∣ M ∧ 0 < u ∧ m*u^2 ≤ U^2 ∧ A^2 = m*u^2+4*r*n

/-- If every prime outside the public support has even multiplicity, the
positive excess belongs to one of the squarefree classes counted by `fiber`. -/
theorem of_even_outside {r A M U n D : ℕ} (mp : 0 < M) (dp : 0 < D)
    (size : D ≤ U^2) (eq : A^2 = D+4*r*n)
    (outside : ∀ p : ℕ, p.Prime → ¬p ∣ M → Even (D.factorization p)) :
    InFiber r A M U n := by
  obtain ⟨m,u,mpos,upos,form,free⟩ := Nat.sq_mul_squarefree_of_pos dp
  have sub : m.primeFactors ⊆ M.primeFactors := by
    intro p hp
    obtain ⟨prime,dvd,_⟩ := Nat.mem_primeFactors.mp hp
    refine Nat.mem_primeFactors.mpr ⟨prime,?_,mp.ne'⟩
    by_contra missing
    obtain ⟨k,hk⟩ := outside p prime missing
    rw [←form,Nat.factorization_mul (pow_ne_zero _ upos.ne') mpos.ne',
      Nat.factorization_pow,Finsupp.add_apply,Finsupp.smul_apply,
      Nat.factorization_eq_one_of_squarefree free prime dvd,smul_eq_mul] at hk
    omega
  have mdvd := (Finset.prod_dvd_prod_of_subset _ _ id sub).trans (Nat.prod_primeFactors_dvd M)
  change (∏ p ∈ m.primeFactors, p) ∣ M at mdvd
  rw [Nat.prod_primeFactors_of_squarefree free] at mdvd
  have same : m*u^2 = D := by simpa only [Nat.mul_comm] using form
  exact ⟨m,u,free,mdvd,upos,same.trans_le size,by rwa [same]⟩

/-- Any integer lower approximations to square roots of primes give a rigorous
Euler product bound. Summing floors can only reduce the count. -/
theorem fiber_product {r A M U : ℕ} (rp : 0 < r) (mp : 0 < M) (c : ℕ → ℕ)
    (positive : ∀ p ∈ M.primeFactors, 0 < c p)
    (under : ∀ p ∈ M.primeFactors, c p ^ 2 ≤ p)
    (S : Finset ℕ) (inside : ∀ n ∈ S, InFiber r A M U n) :
    (S.card : ℚ) ≤ U * ∏ p ∈ M.primeFactors, (1+(c p : ℚ)⁻¹) := by
  classical
  let cell (t : Finset ℕ) := (Icc 1 (U / ∏ p ∈ t, c p)).image
    (fun u => (A^2 - (∏ p ∈ t, p)*u^2)/(4*r))
  have cover : S ⊆ M.primeFactors.powerset.biUnion cell := by
    intro n hn
    obtain ⟨m,u,free,dvd,up,size,eq⟩ := inside n hn
    have sub := Nat.primeFactors_mono dvd mp.ne'
    have rad := Nat.prod_primeFactors_of_squarefree free
    refine mem_biUnion.mpr ⟨m.primeFactors,mem_powerset.mpr sub,mem_image.mpr ⟨u,?_,?_⟩⟩
    · refine mem_Icc.mpr ⟨up,(Nat.le_div_iff_mul_le (prod_pos fun p h => positive p (sub h))).mpr ?_⟩
      apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
      rw [mul_pow,←Finset.prod_pow]
      have hprod := Finset.prod_le_prod' (fun p (h : p ∈ m.primeFactors) => under p (sub h))
      rw [rad] at hprod
      exact (Nat.mul_le_mul_left _ hprod).trans (by simpa [Nat.mul_comm] using size)
    · rw [rad,eq,Nat.add_sub_cancel_left,Nat.mul_div_cancel_left _ (by positivity)]
  have count : S.card ≤ ∑ t ∈ M.primeFactors.powerset, U/(∏ p ∈ t, c p) :=
    (card_le_card cover).trans <| card_biUnion_le.trans <| sum_le_sum fun t _ =>
      (card_image_le (f:=_)).trans (by simp [Nat.card_Icc])
  rw [Finset.prod_one_add,Finset.mul_sum]
  refine (Nat.cast_le.mpr count).trans ?_
  push_cast
  apply Finset.sum_le_sum
  intro t ht
  have hp : 0 < ∏ p ∈ t, c p := prod_pos fun p h => positive p (mem_powerset.mp ht h)
  rw [Finset.prod_inv_distrib,←Nat.cast_prod,←div_eq_mul_inv]
  apply (le_div_iff₀ (by exact_mod_cast hp)).mpr
  exact_mod_cast Nat.div_mul_le_self U (∏ p ∈ t, c p)

/-- A three-level lower bound for the square root of each prime. -/
def weight (p : ℕ) : ℕ := if p < 16 then 1 else if p < 256 then 4 else 16

/-- The numerical Euler product uses only the prime support of `M`. -/
noncomputable def correction (M : ℕ) : ℚ :=
  ∏ p ∈ M.primeFactors, (1+(weight p : ℚ)⁻¹)

set_option exponentiation.threshold 20000

/-- The first two brackets contain at most six and forty-eight primes. The
number of larger primes is bounded by their product, which divides `M`. -/
theorem correction_lt {M : ℕ} (mp : 0 < M) (small : M < 2^(15*1037)) :
    correction M < 2^193 := by
  classical
  let low := M.primeFactors.filter (fun p => p<16)
  let rest := M.primeFactors.filter (fun p => ¬p<16)
  let mid := rest.filter (fun p => p<256)
  let high := rest.filter (fun p => ¬p<256)
  have low_card : low.card ≤ 6 := by
    have sub : low ⊆ (range 16).filter Nat.Prime := fun _ h =>
      mem_filter.mpr ⟨mem_range.mpr (mem_filter.mp h).2,Nat.prime_of_mem_primeFactors (mem_filter.mp h).1⟩
    exact (card_le_card sub).trans (by decide +kernel)
  have mid_card : mid.card ≤ 48 := by
    have sub : mid ⊆ (Ico 16 256).filter Nat.Prime := by
      intro p hp
      obtain ⟨hr,hi⟩ := mem_filter.mp hp
      obtain ⟨prime,lo⟩ := mem_filter.mp hr
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.le_of_not_gt lo,hi⟩, Nat.prime_of_mem_primeFactors prime⟩
    exact (card_le_card sub).trans (by decide +kernel)
  have high_sub : high ⊆ M.primeFactors := fun _ h => (mem_filter.mp (mem_filter.mp h).1).1
  have high_card : high.card ≤ 1945 := by
    have geom : 256^high.card ≤ ∏ p ∈ high, p := by
      simpa using Finset.prod_le_prod' (fun p (h : p ∈ high) => Nat.le_of_not_gt (mem_filter.mp h).2)
    have d : (∏ p ∈ high, p) ∣ M := (Finset.prod_dvd_prod_of_subset high M.primeFactors id high_sub).trans (Nat.prod_primeFactors_dvd M)
    have h := (geom.trans (Nat.le_of_dvd mp d)).trans_lt small
    rw [show (256:ℕ)=2^8 by decide,←pow_mul] at h
    have h' := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h
    omega
  let f (p : ℕ) : ℚ := 1+(weight p : ℚ)⁻¹
  have low_prod : ∏ p ∈ low, f p = 2^low.card := by
    convert prod_congr rfl (fun p (h : p ∈ low) => show f p = (2:ℚ) by
      dsimp [f,weight]; rw [if_pos (mem_filter.mp h).2]; norm_num) using 1
    simp
  have mid_prod : ∏ p ∈ mid, f p = (5/4)^mid.card := by
    convert prod_congr rfl (fun p (h : p ∈ mid) => show f p = (5/4:ℚ) by
      dsimp [f,weight]; rw [if_neg (mem_filter.mp (mem_filter.mp h).1).2,if_pos (mem_filter.mp h).2]; norm_num) using 1
    simp [div_pow]
  have high_prod : ∏ p ∈ high, f p = (17/16)^high.card := by
    convert prod_congr rfl (fun p (h : p ∈ high) => show f p = (17/16:ℚ) by
      dsimp [f,weight]; rw [if_neg (mem_filter.mp (mem_filter.mp h).1).2,if_neg (mem_filter.mp h).2]; norm_num) using 1
    simp [div_pow]
  have eq : correction M = (∏ p ∈ low, f p)*((∏ p ∈ mid, f p)*(∏ p ∈ high, f p)) := by
    change (∏ p ∈ M.primeFactors, f p) = _
    rw [show (∏ p ∈ mid, f p)*(∏ p ∈ high, f p) = ∏ p ∈ rest, f p from
      prod_filter_mul_prod_filter_not rest _ f]
    exact (prod_filter_mul_prod_filter_not M.primeFactors _ f).symm
  rw [eq,low_prod,mid_prod,high_prod]
  calc
    _ ≤ (2:ℚ)^6*((5/4)^48*(17/16)^1945) := by gcongr <;> norm_num
    _ < _ := by decide +kernel

/-- Uniform fixed-label population bound under the fifteen-differences cap. -/
theorem fiber {r A M U : ℕ} (rp : 0 < r) (mp : 0 < M) (small : M < 2^(15*1037))
    (S : Finset ℕ) (inside : ∀ n ∈ S, InFiber r A M U n) : S.card ≤ U*2^193 := by
  have h := fiber_product rp mp weight (by intro p _; unfold weight; split_ifs <;> decide)
    (by
      intro p hp
      have hp' := (Nat.prime_of_mem_primeFactors hp).two_le
      unfold weight
      split_ifs <;> omega) S inside
  change (S.card : ℚ) ≤ U*correction M at h
  exact_mod_cast h.trans (mul_le_mul_of_nonneg_left (correction_lt mp small).le (by positivity))

end PrimeFactors.WeightedSubsetFiber
