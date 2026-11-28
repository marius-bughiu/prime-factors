import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic

/-! The first two moments of square-root counts when the product is
uniform in a finite commutative group. -/
namespace PrimeFactors.SquareFiberMoments

open Finset
open scoped Classical
variable {G : Type*} [CommGroup G] [Fintype G]

noncomputable def roots (n : G) := (univ.filter (fun x : G => x^2=n)).card

private def fiberEquiv (a : G) (n : G) (ha : a^2=n) :
    {x : G // x^2=n} ≃ {x : G // x^2=1} where
  toFun x := ⟨x.val/a, by rw [div_pow,x.property,ha,div_self']⟩
  invFun y := ⟨y.val*a, by rw [mul_pow,y.property,one_mul,ha]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

/-- Every occupied fiber of squaring has exactly as many elements as
the kernel of squaring. -/
theorem share_kernel (n : G) : roots n=0 ∨ roots n=roots (1:G) := by
  by_cases h : ∃ a : G,a^2=n
  · obtain ⟨a,ha⟩ := h
    right
    simpa only [roots,Fintype.card_subtype] using Fintype.card_congr (fiberEquiv a n ha)
  · left
    exact card_eq_zero.mpr (filter_false_of_mem (fun a _ ha => h ⟨a,ha⟩))

theorem first : (∑ n : G,roots n)=Fintype.card G := by
  have all := card_eq_sum_card_fiberwise (s:=(univ:Finset G)) (t:=univ)
    (f:=fun a : G => a^2) (fun _ _ => mem_univ _)
  simpa only [card_univ,roots] using all.symm

theorem second : (∑ n : G,roots n^2)=Fintype.card G*roots (1:G) := by
  have each (n:G) : roots n^2=roots n*roots (1:G) := by
    rcases share_kernel n with eq|eq <;> rw [eq] <;> simp [sq]
  simp_rw [each]
  rw [←sum_mul,first]

end PrimeFactors.SquareFiberMoments
