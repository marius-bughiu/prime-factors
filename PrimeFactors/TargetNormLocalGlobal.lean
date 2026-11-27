import PrimeFactors.TargetNormConic
import PrimeFactors.ShortRootNormPositive
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-! Exact primitive solvability of X²=A Y²+2T² for odd squarefree A>1.
The construction from a root already works with Y=1. -/
namespace PrimeFactors.TargetNormLocalGlobal

private theorem crt_two {a b : ℕ} (cop : a.Coprime b) (ha : IsSquare (2 : ZMod a))
    (hb : IsSquare (2 : ZMod b)) : IsSquare (2 : ZMod (a*b)) := by
  obtain ⟨r,hr⟩ := ha
  obtain ⟨s,hs⟩ := hb
  let e := ZMod.chineseRemainder cop
  refine ⟨e.symm (r,s),e.injective ?_⟩
  rw [map_ofNat,map_mul,e.apply_symm_apply]
  exact Prod.ext hr hs

private theorem from_local (A : ℕ) (sf : Squarefree A)
    (all : ∀ p, p.Prime → p ∣ A → IsSquare (2 : ZMod p)) : IsSquare (2 : ZMod A) := by
  induction A using Nat.recOnPosPrimePosCoprime with
  | h0 => exact (not_squarefree_zero sf).elim
  | h1 => exact ⟨0,Subsingleton.elim _ _⟩
  | hp p n hp hn =>
    have one : n=1 := by
      by_contra n1
      have dvd : p^2 ∣ p^n := pow_dvd_pow p (by omega)
      exact Nat.squarefree_iff_prime_squarefree.mp sf p hp (by simpa [sq] using dvd)
    subst n
    have root := all p hp (by simp)
    exact (congrArg (fun m : ℕ => IsSquare (2 : ZMod m)) (pow_one p)).mpr root
  | h a b _ _ cop ia ib =>
    apply crt_two cop
    · exact ia (sf.squarefree_of_dvd (dvd_mul_right ..))
        (fun p hp dv => all p hp (dv.trans (dvd_mul_right ..)))
    · exact ib (sf.squarefree_of_dvd (dvd_mul_left ..))
        (fun p hp dv => all p hp (dv.trans (dvd_mul_left ..)))

/-- Complete list of prime obstructions. Each local congruence has two
roots modulo its odd prime. The Chinese remainder argument uses one of them. -/
theorem root_iff_split {A : ℕ} (sf : Squarefree A) (odd : Odd A) :
    IsSquare (2 : ZMod A) ↔ ∀ p, p.Prime → p ∣ A → p%8=1 ∨ p%8=7 := by
  have localTest (p : ℕ) (pr : p.Prime) (dvd : p ∣ A) :
      IsSquare (2 : ZMod p) ↔ p%8=1 ∨ p%8=7 := by
    letI : Fact p.Prime := ⟨pr⟩
    have ne : p ≠ 2 := fun e => odd.not_two_dvd_nat (e ▸ dvd)
    have po := pr.odd_of_ne_two ne
    have nz : ((2 : ℕ) : ZMod p) ≠ 0 := fun z =>
      Nat.not_dvd_of_pos_of_lt (by decide : 0<2) (lt_of_le_of_ne pr.two_le ne.symm)
        ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp z)
    have eqv := legendreSym.eq_one_iff' p nz
    rw [Nat.cast_ofNat,Nat.cast_ofNat,legendreSym.at_two ne,ZMod.χ₈_nat_eq_if_mod_eight,
      Nat.odd_iff.mp po] at eqv
    by_cases r : p%8=1 ∨ p%8=7 <;> simpa [r] using eqv.symm
  constructor
  · intro sq p pr dvd
    apply (localTest p pr dvd).mp
    simpa only [map_ofNat] using sq.map (ZMod.castHom dvd (ZMod p))
  · intro residues
    exact from_local A sf fun p pr dvd => (localTest p pr dvd).mpr (residues p pr dvd)

/-- Primitive solvability of the conic is equivalent to the prime residue
test. Clearing denominators is unnecessary in the constructive direction. -/
theorem primitive_iff {A : ℕ} (size : 2≤A) (sf : Squarefree A) (odd : Odd A) :
    (∃ X Y T : ℕ, 0<X ∧ 0<Y ∧ 0<T ∧ X.Coprime Y ∧ X^2=A*Y^2+2*T^2) ↔
    ∀ p, p.Prime → p ∣ A → p%8=1 ∨ p%8=7 := by
  rw [← root_iff_split sf odd]
  constructor
  · rintro ⟨X,Y,T,_,_,_,cop,norm⟩
    have root := TargetNormConic.root_from_point (N:=A) (k:=1) sf (by simp)
      (by simpa only [one_mul] using norm) cop
    exact ⟨_,by simpa only [pow_two,Nat.cast_ofNat] using root.symm⟩
  · intro square
    obtain ⟨x,t,xp,tp,point⟩ := ShortRootNormPositive.two size square
    exact ⟨x,1,t,xp,by decide,tp,by simp,by simpa using point⟩

end PrimeFactors.TargetNormLocalGlobal
