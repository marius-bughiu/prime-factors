import PrimeFactors.QuarticFactorLane
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.LinearCombination

namespace PrimeFactors.QuarticUnitLabels
open QuarticFactorLane

private abbrev Tag (a b c d : ℕ) := ZMod a × ZMod b × ZMod c × ZMod d

/-- Separate Newton residues on the dyadic lane, the 3-adic units and the 5-adic units. -/
abbrev Labels (R : ℕ) := Tag (8*R^4) (8*R^3) (4*R^2) (4*R) ×
  Tag 9 9 3 3 × Tag 5 5 5 5

theorem card_labels (R : ℕ) [NeZero R] :
    Fintype.card (Labels R) = 466560000*R^10 := by
  simp [Labels, Tag, ZMod.card]
  ring

private def b₁ (w : Weights) (N A B : ℤ) :=
  w.b*N+w.e*(A+B)+w.a*(A^2+A*B+B^2)+w.c*(A^3+A^2*B+A*B^2+B^3)
private def b₂ (w : Weights) (A B C : ℤ) :=
  w.e+w.a*(A+B+C)+w.c*(A^2+B^2+C^2+A*B+A*C+B*C)
private def b₃ (w : Weights) (A B C D : ℤ) := w.a+w.c*(A+B+C+D)

private noncomputable def tag (m₀ m₁ m₂ m₃ : ℕ) (A B C D N : ℤ) (w : Weights) :
    Tag m₀ m₁ m₂ m₃ :=
  (value w N A, b₁ w N A B, b₂ w A B C, b₃ w A B C D)

noncomputable def label (R : ℕ) (u N : ℤ) (w : Weights) : Labels R :=
  (tag _ _ _ _ u (u+R) (u+2*R) (u+3*R) N w,
   tag _ _ _ _ 1 2 4 5 N w, tag _ _ _ _ 1 2 3 4 N w)

private theorem dvd_from_tag {m₀ m₁ m₂ m₃ : ℕ} {A B C D N x M : ℤ} {w v : Weights}
    (same : tag m₀ m₁ m₂ m₃ A B C D N w = tag m₀ m₁ m₂ m₃ A B C D N v)
    (h₀ : M ∣ m₀) (h₁ : M ∣ m₁*(x-A)) (h₂ : M ∣ m₂*((x-A)*(x-B)))
    (h₃ : M ∣ m₃*((x-A)*(x-B)*(x-C))) (h₄ : M ∣ (x-A)*(x-B)*(x-C)*(x-D)) :
    M ∣ value w N x - value v N x := by
  have E₀ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ m₀).mp (congrArg Prod.fst same.symm)
  have E₁ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ m₁).mp
    (congrArg (fun t => t.2.1) same.symm)
  have E₂ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ m₂).mp
    (congrArg (fun t => t.2.2.1) same.symm)
  have E₃ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ m₃).mp
    (congrArg (fun t => t.2.2.2) same.symm)
  change (m₀ : ℤ) ∣ value w N A - value v N A at E₀
  change (m₁ : ℤ) ∣ b₁ w N A B - b₁ v N A B at E₁
  change (m₂ : ℤ) ∣ b₂ w A B C - b₂ v A B C at E₂
  change (m₃ : ℤ) ∣ b₃ w A B C D - b₃ v A B C D at E₃
  obtain ⟨k₁,hk₁⟩ := E₁
  obtain ⟨k₂,hk₂⟩ := E₂
  obtain ⟨k₃,hk₃⟩ := E₃
  have combine := dvd_add (dvd_add (dvd_add (dvd_add (h₀.trans E₀)
    (dvd_mul_of_dvd_left h₁ k₁)) (dvd_mul_of_dvd_left h₂ k₂))
    (dvd_mul_of_dvd_left h₃ k₃)) (dvd_mul_of_dvd_left h₄ (w.c-v.c))
  convert combine using 1
  simp only [value,b₁,b₂,b₃] at *
  linear_combination (x-A)*hk₁ + ((x-A)*(x-B))*hk₂ + ((x-A)*(x-B)*(x-C))*hk₃

private theorem falling (k : ℤ) :
    (2:ℤ) ∣ k*(k-1) ∧ (8:ℤ) ∣ k*(k-1)*(k-2)*(k-3) := by
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    push_cast
    exact (by decide +kernel : ∀ a : ZMod 2, a*(a-1)=0) _
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
    push_cast
    exact (by decide +kernel : ∀ a : ZMod 8, a*(a-1)*(a-2)*(a-3)=0) _

private theorem dyadic {R : ℕ} {w v : Weights} {x u N : ℤ}
    (same : tag (8*R^4) (8*R^3) (4*R^2) (4*R) u (u+R) (u+2*R) (u+3*R) N w =
      tag _ _ _ _ u (u+R) (u+2*R) (u+3*R) N v)
    (lane : x ≡ u [ZMOD (R:ℤ)]) : (8*(R:ℤ)^4) ∣ value w N x - value v N x := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp lane.symm
  have replaceX : x=u+R*k := by linarith
  obtain ⟨⟨h,hh⟩,⟨s,hs⟩⟩ := falling k
  apply dvd_from_tag same <;> push_cast
  · exact dvd_refl _
  · exact ⟨k, by rw [replaceX]; ring⟩
  · exact ⟨h, by rw [replaceX]; linear_combination 4*(R:ℤ)^4*hh⟩
  · exact ⟨h*(k-2), by rw [replaceX]; linear_combination 4*(R:ℤ)^4*(k-2)*hh⟩
  · exact ⟨s, by rw [replaceX]; linear_combination (R:ℤ)^4*hs⟩

private theorem at_three {w v : Weights} {x N : ℤ}
    (same : tag 9 9 3 3 1 2 4 5 N w = tag _ _ _ _ 1 2 4 5 N v)
    (unit : IsCoprime x 30) : (9:ℤ) ∣ value w N x - value v N x := by
  obtain ⟨a,b,hab⟩ := unit
  have reduced := congrArg (fun i : ℤ => (i : ZMod 9)) hab
  push_cast at reduced
  have all : ∀ x a b : ZMod 9, a*x+b*30=1 →
      3*((x-1)*(x-2)) = 0 ∧ (x-1)*(x-2)*(x-4)*(x-5) = 0 := by decide +kernel
  have facts := all x a b reduced
  have pair : (9:ℤ) ∣ 3*((x-1)*(x-2)) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mp
    push_cast
    exact facts.1
  apply dvd_from_tag same
  · exact dvd_refl _
  · exact dvd_mul_right _ _
  · exact pair
  · simpa only [mul_assoc] using dvd_mul_of_dvd_left pair (x-4)
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mp
    push_cast
    exact facts.2

private theorem at_five {w v : Weights} {x N : ℤ}
    (same : tag 5 5 5 5 1 2 3 4 N w = tag _ _ _ _ 1 2 3 4 N v)
    (unit : IsCoprime x 30) : (5:ℤ) ∣ value w N x - value v N x := by
  obtain ⟨a,b,hab⟩ := unit
  have reduced := congrArg (fun i : ℤ => (i : ZMod 5)) hab
  push_cast at reduced
  have all : ∀ x a b : ZMod 5, a*x+b*30=1 → (x-1)*(x-2)*(x-3)*(x-4) = 0 := by decide +kernel
  apply dvd_from_tag same
  · exact dvd_refl _
  · exact dvd_mul_right _ _
  · exact dvd_mul_right _ _
  · exact dvd_mul_right _ _
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
    push_cast
    exact all x a b reduced

/-- A collision of the twelve public labels forces divisibility everywhere
on the proposed factor lane, at every x coprime to 30. -/
theorem divides_of_label_eq {w v : Weights} {x u N : ℤ}
    (same : label (2^614) u N w = label (2^614) u N v)
    (lane : x ≡ u [ZMOD (2:ℤ)^614]) (unit : IsCoprime x 30) :
    (360*((2:ℤ)^614)^4) ∣ value w N x - value v N x := by
  have atTwo := dyadic (congrArg Prod.fst same) (by exact_mod_cast lane)
  have atNine := at_three (congrArg (fun z => z.2.1) same) unit
  have atFive := at_five (congrArg (fun z => z.2.2) same) unit
  have copOdd : IsCoprime (9:ℤ) 5 := Int.isCoprime_iff_gcd_eq_one.mpr (by decide)
  have odd : (45:ℤ) ∣ value w N x - value v N x := copOdd.mul_dvd atNine atFive
  have cop : IsCoprime (8*((2:ℤ)^614)^4) 45 :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)
  have full := cop.mul_dvd (by exact_mod_cast atTwo) odd
  have reorder (T : ℤ) : 360*T = (8*T)*45 := by ring
  rw [reorder]
  exact full

end PrimeFactors.QuarticUnitLabels
