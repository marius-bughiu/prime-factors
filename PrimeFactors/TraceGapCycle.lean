import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! If a half-size set in an odd prime field misses a difference, its translate
and the original set cover everything except a single residue. Summing over that
partition imposes an exact relation between the second and fourth moments. -/
namespace PrimeFactors.TraceGapCycle
open Finset

/-- Sum of any transition observable on the two copies and their unique uncovered point. -/
private theorem missing_point {ℓ k : ℕ} [Fact ℓ.Prime] (A : Finset (ZMod ℓ)) (t : ZMod ℓ)
    (size : ℓ=2*k+1) (card : A.card=k) (sep : ∀ x∈A, x+t∉A) :
    ∃ h : ZMod ℓ, h∉A ∧ h-t∉A ∧ ∀ f : ZMod ℓ → ZMod ℓ,
      (∑ x∈A, f x)+(∑ x∈A, f (x+t))+f h=∑ x, f x := by
  let B := A.image (fun x => x+t)
  have disjoint : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro y ya yb
    obtain ⟨x,xa,rfl⟩ := mem_image.mp yb
    exact sep x xa ya
  have bc : B.card=k := (card_image_of_injective A (fun _ _ eq => add_right_cancel eq)).trans card
  have holes : (A∪B)ᶜ.card=1 := by
    rw [card_compl,ZMod.card,card_union_of_disjoint disjoint,card,bc,size]; omega
  obtain ⟨h,hole⟩ := card_eq_one.mp holes
  have hm : h∈(A∪B)ᶜ := by rw [hole]; simp
  have ha : h∉A := fun z => (mem_compl.mp hm) (mem_union_left B z)
  have hb : h-t∉A := by
    intro z
    apply (mem_compl.mp hm) (mem_union_right A (mem_image.mpr ⟨h-t,z,sub_add_cancel h t⟩))
  refine ⟨h,ha,hb,fun f => ?_⟩
  have eq := sum_add_sum_compl (A∪B) f
  rw [hole,sum_singleton,sum_union disjoint] at eq
  simpa only [B,sum_image (fun _ _ _ _ eq => add_right_cancel eq)] using eq

private theorem square_shift {K : Type*} [CommRing K] (A : Finset K) (t : K) :
    ∑ x∈A, (x+t)^2 = (∑ x∈A,x^2)+2*t*(∑ x∈A,x)+A.card*t^2 := by
  calc ∑ x∈A, (x+t)^2 = ∑ x∈A, (x^2+2*t*x+t^2) := sum_congr rfl fun _ _ => by ring
       _ = _ := by simp only [sum_add_distrib,mul_sum,sum_const,nsmul_eq_mul]

private theorem fourth_shift {K : Type*} [CommRing K] (A : Finset K) (t : K) :
    ∑ x∈A, (x+t)^4 = (∑ x∈A,x^4)+4*t*(∑ x∈A,x^3)+6*t^2*(∑ x∈A,x^2)+
      4*t^3*(∑ x∈A,x)+A.card*t^4 := by
  calc ∑ x∈A, (x+t)^4 = ∑ x∈A, (x^4+4*t*x^3+6*t^2*x^2+4*t^3*x+t^4) :=
         sum_congr rfl fun _ _ => by ring
       _ = _ := by simp only [sum_add_distrib,mul_sum,sum_const,nsmul_eq_mul]

/-- A missing difference determines the hole and both even moments. The sums over the
entire field are assumptions, so the result also covers small characteristics whenever
those assumptions hold. -/
theorem hole_moments {ℓ k : ℕ} [Fact ℓ.Prime] (A : Finset (ZMod ℓ)) (t : ZMod ℓ)
    (size : ℓ=2*k+1) (card : A.card=k) (sep : ∀ x∈A, x+t∉A)
    (one : (∑ x∈A,x)=0) (three : (∑ x∈A,x^3)=0)
    (full1 : (∑ x : ZMod ℓ,x)=0) (full2 : (∑ x : ZMod ℓ,x^2)=0)
    (full4 : (∑ x : ZMod ℓ,x^4)=0) :
    ∃ h : ZMod ℓ, h∉A ∧ h-t∉A ∧ 2*h=t ∧ 8*(∑ x∈A,x^2)=t^2 ∧
      32*(∑ x∈A,x^4) = -5*t^4 ∧ (∑ x∈A,x^4) = -10*(∑ x∈A,x^2)^2 := by
  obtain ⟨h,ha,hb,split⟩ := missing_point A t size card sep
  have char : 2*(k : ZMod ℓ)+1=0 := calc
    _ = ((2*k+1 : ℕ) : ZMod ℓ) := by simp
    _ = 0 := by rw [←size,ZMod.natCast_self]
  have first := split (fun x => x)
  simp only [sum_add_distrib,one,zero_add,sum_const,nsmul_eq_mul,full1,card] at first
  have twice : 2*h=t := by linear_combination 2*first - t*char
  have h2 : 4*h^2=t^2 := by linear_combination (2*h+t)*twice
  have h4 : 16*h^4=t^4 := by linear_combination (4*h^2+t^2)*h2
  have second := split (fun x => x^2)
  simp only [square_shift,one,mul_zero,add_zero,card,full2] at second
  have m2 : 8*(∑ x∈A,x^2)=t^2 := by linear_combination 4*second - 2*t^2*char - h2
  have fourth := split (fun x => x^4)
  simp only [fourth_shift,three,one,mul_zero,add_zero,card,full4] at fourth
  have m4 : 32*(∑ x∈A,x^4) = -5*t^4 := by
    linear_combination 16*fourth - 12*t^2*m2 - 8*t^4*char - h4
  refine ⟨h,ha,hb,twice,m2,m4,?_⟩
  have nz : (2 : ZMod ℓ)≠0 := by intro z; rw [z,zero_mul,zero_add] at char; exact one_ne_zero char
  have nz32 : (32 : ZMod ℓ)≠0 := by rw [show (32 : ZMod ℓ)=2^5 by ring]; exact pow_ne_zero _ nz
  have final : 32*((∑ x∈A,x^4)+10*(∑ x∈A,x^2)^2)=0 := by
    linear_combination m4 + 5*(8*(∑ x∈A,x^2)+t^2)*m2
  linear_combination (mul_eq_zero.mp final).resolve_left nz32

/-- A single identity useful for disproving a proposed missing difference. -/
theorem moment_identity {ℓ k : ℕ} [Fact ℓ.Prime] (A : Finset (ZMod ℓ)) (t : ZMod ℓ)
    (size : ℓ=2*k+1) (card : A.card=k) (sep : ∀ x∈A, x+t∉A)
    (one : (∑ x∈A,x)=0) (three : (∑ x∈A,x^3)=0)
    (full1 : (∑ x : ZMod ℓ,x)=0) (full2 : (∑ x : ZMod ℓ,x^2)=0)
    (full4 : (∑ x : ZMod ℓ,x^4)=0) : (∑ x∈A,x^4) = -10*(∑ x∈A,x^2)^2 := by
  obtain ⟨_,_,_,_,_,_,result⟩ := hole_moments A t size card sep one three full1 full2 full4
  exact result

/-- At primes at least seven the three sums over the full field vanish. -/
theorem prime_moment_identity {ℓ k : ℕ} [Fact ℓ.Prime] (large : 7≤ℓ)
    (A : Finset (ZMod ℓ)) (t : ZMod ℓ) (size : ℓ=2*k+1) (card : A.card=k)
    (sep : ∀ x∈A, x+t∉A) (one : (∑ x∈A,x)=0) (three : (∑ x∈A,x^3)=0) :
    (∑ x∈A,x^4) = -10*(∑ x∈A,x^2)^2 := by
  have vanish (i : ℕ) (hi : i≤4) : (∑ x : ZMod ℓ,x^i)=0 :=
    FiniteField.sum_pow_lt_card_sub_one (ZMod ℓ) i (by rw [ZMod.card]; omega)
  exact moment_identity A t size card sep one three (by simpa using vanish 1 (by decide))
    (vanish 2 (by decide)) (vanish 4 (by decide))

end PrimeFactors.TraceGapCycle
