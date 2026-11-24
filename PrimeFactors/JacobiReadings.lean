import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Tactic.Ring

namespace PrimeFactors

private theorem signChar_sum_zero {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℤ) (nontrivial : χ ≠ 1) : ∑ x, χ x = 0 := by
  classical
  obtain ⟨g,hg⟩ : ∃ g, χ g ≠ 1 := by
    by_contra! all
    exact nontrivial (MonoidHom.ext all)
  have perm := Equiv.sum_comp (Equiv.mulLeft g) (fun x => χ x)
  change (∑ x, χ (g*x)) = ∑ x, χ x at perm
  simp only [map_mul,← Finset.mul_sum] at perm
  exact (mul_eq_zero.mp (show (χ g-1)*(∑ x, χ x)=0 by rw [sub_mul,one_mul,perm,sub_self])).resolve_left
    (sub_ne_zero.mpr hg)

/-- Two independent integer-valued multiplicative characters on a finite
group realize each of the four sign pairs on exactly a quarter of the group.
Their ranges are automatically contained in the two units of the integers. -/
theorem signPair_quarter {G : Type*} [Group G] [Fintype G] (χ ψ : G →* ℤ)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ*ψ ≠ 1) {a b : ℤ}
    (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) :
    4*(Finset.univ.filter fun x => χ x=a ∧ ψ x=b).card=Fintype.card G := by
  classical
  have shape (x : G) :
      4*(if χ x=a ∧ ψ x=b then 1 else 0)=
        1+a*χ x+b*ψ x+(a*b)*(χ*ψ) x := by
    have hc := Int.isUnit_eq_one_or ((Group.isUnit x).map χ)
    have hd := Int.isUnit_eq_one_or ((Group.isUnit x).map ψ)
    rw [MonoidHom.mul_apply]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      rcases hc with hc | hc <;> rcases hd with hd | hd <;> norm_num [hc,hd]
  have total := Finset.sum_congr (s₁ := (Finset.univ : Finset G)) rfl (fun x _ => shape x)
  simp only [← Finset.mul_sum,Finset.sum_boole,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,mul_one,signChar_sum_zero χ hχ,
    signChar_sum_zero ψ hψ,signChar_sum_zero (χ*ψ) hχψ,mul_zero,add_zero] at total
  exact_mod_cast total

/-- A perfect-square numerator gives a positive Jacobi reading at every
coprime odd denominator. Mathlib's extension also covers even denominators. -/
theorem jacobi_square_reading {x : ℤ} {m : ℕ} (cop : x.gcd m=1) :
    jacobiSym (x^2) m=1 := jacobiSym.sq_one' cop

end PrimeFactors
