import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

namespace PrimeFactors.WeightSlopeCover
open Finset
noncomputable section

/-- One fixed right-hand side has at most gcd(R,a) preimages in a complete period. -/
noncomputable def fiber (R a : ℕ) (b : ℤ) : Finset ℕ :=
  (range R).filter (fun s => (a:ℤ)*s ≡ b [ZMOD R])

theorem fiber_bound {R a : ℕ} (pos : 0<R) (b : ℤ) : (fiber R a b).card ≤ R.gcd a := by
  let g := R.gcd a
  let m := R/g
  have product : m*g=R := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have mp : 0<m := Nat.div_pos (Nat.le_of_dvd pos (Nat.gcd_dvd_left ..))
    (Nat.gcd_pos_of_pos_left a pos)
  calc
    _ ≤ (range g).card := by
      apply card_le_card_of_injOn (fun s => s/m)
      · intro s hs
        have small := mem_range.mp (mem_filter.mp hs).1
        exact mem_range.mpr ((Nat.div_lt_iff_lt_mul mp).mpr (by simpa [mul_comm g m,product] using small))
      · intro x hx y hy same
        have hxy := (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
        have hcast : ((a*x : ℕ):ℤ) ≡ ((a*y : ℕ):ℤ) [ZMOD R] := by simpa using hxy
        have rel : x % m = y % m := (Int.natCast_modEq_iff.mp hcast).cancel_left_div_gcd pos
        dsimp at same
        rw [← Nat.mod_add_div x m, ← Nat.mod_add_div y m, rel, same]
    _ = _ := card_range _

noncomputable def coefficients (B g : ℕ) : Finset ℤ :=
  (Icc (-((B/g : ℕ):ℤ)) ((B/g : ℕ):ℤ)).erase 0

theorem coefficients_card (B g : ℕ) : (coefficients B g).card = 2*(B/g) := by
  have nonneg : (0:ℤ) ≤ (B/g : ℕ) := Int.natCast_nonneg _
  have hz : (0:ℤ) ∈ Icc (-((B/g : ℕ):ℤ)) ((B/g : ℕ):ℤ) := mem_Icc.mpr ⟨neg_nonpos.mpr nonneg,nonneg⟩
  rw [coefficients, card_erase_of_mem hz, Int.card_Icc]
  omega

noncomputable def fixed (R B a : ℕ) : Finset ℕ :=
  (coefficients B (R.gcd a)).biUnion (fun j => fiber R a (R.gcd a*j))

theorem fixed_bound {R B a : ℕ} (pos : 0<R) : (fixed R B a).card ≤ 2*B := by
  calc
    _ ≤ (coefficients B (R.gcd a)).card * (R.gcd a) :=
      card_biUnion_le_card_mul _ _ _ (fun j _ => fiber_bound pos _)
    _ ≤ _ := by rw [coefficients_card, mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.div_mul_le_self ..)

theorem mem_fixed {R B s a : ℕ} {b : ℤ} (pos : 0<R) (hs : s<R) (nz : b≠0)
    (cap : b.natAbs≤B) (rel : (a:ℤ)*s ≡ b [ZMOD R]) : s ∈ fixed R B a := by
  let g := R.gcd a
  have gp : 0<g := Nat.gcd_pos_of_pos_left a pos
  have dgR : (g:ℤ) ∣ R := by exact_mod_cast Nat.gcd_dvd_left R a
  have dga : (g:ℤ) ∣ a := by exact_mod_cast Nat.gcd_dvd_right R a
  have db : (g:ℤ) ∣ b := Int.modEq_zero_iff_dvd.mp
    ((rel.of_dvd dgR).symm.trans (Int.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left dga _)))
  obtain ⟨j,hj⟩ := db
  have jcap : j.natAbs ≤ B/g := (Nat.le_div_iff_mul_le gp).mpr (by
    simpa [hj,Int.natAbs_mul,mul_comm] using cap)
  have jc : |j| ≤ ((B/g : ℕ):ℤ) := by exact_mod_cast (show (j.natAbs : ℤ) ≤ _ by exact_mod_cast jcap)
  apply mem_biUnion.mpr
  refine ⟨j,mem_erase.mpr ⟨fun h => nz (by simp [hj,h]),mem_Icc.mpr (abs_le.mp jc)⟩,?_⟩
  exact mem_filter.mpr ⟨mem_range.mpr hs,by simpa [hj] using rel⟩

/-- Any collection of slopes admitting two bounded nonzero signed weights
contains at most 2 B² residues, independent of the radix's divisor count. -/
theorem bounded_slopes {R B : ℕ} (pos : 0<R) (S : Finset ℕ)
    (cover : ∀ s ∈ S, s<R ∧ ∃ a b : ℤ, a≠0 ∧ b≠0 ∧ a.natAbs≤B ∧ b.natAbs≤B ∧
      a*s ≡ b [ZMOD R]) : S.card ≤ 2*B^2 := by
  have into : S ⊆ (Icc 1 B).biUnion (fixed R B) := by
    intro s hs
    obtain ⟨small,a,b,an,bn,ac,bc,rel⟩ := cover s hs
    apply mem_biUnion.mpr
    refine ⟨a.natAbs,mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr an),ac⟩,?_⟩
    by_cases ap : 0 ≤ a
    · apply mem_fixed pos small bn bc
      simpa [Int.natCast_natAbs,abs_of_nonneg ap] using rel
    · apply mem_fixed pos small (neg_ne_zero.mpr bn) (by simpa using bc : (-b).natAbs≤B)
      simpa [Int.natCast_natAbs,abs_of_neg (lt_of_not_ge ap),neg_mul] using rel.neg
  calc
    _ ≤ _ := card_le_card into
    _ ≤ (Icc 1 B).card * (2*B) := card_biUnion_le_card_mul _ _ _ (fun a _ => fixed_bound pos)
    _ = _ := by rw [Nat.card_Icc]; cases B <;> simp; ring

/-- For unit slopes and a bound strictly smaller than the modulus, a nonzero
weight vector automatically has two nonzero coordinates. -/
theorem unit_slopes {R B : ℕ} (small : B<R) (S : Finset ℕ)
    (cover : ∀ s ∈ S, s<R ∧ R.Coprime s ∧ ∃ a b : ℤ, (a≠0 ∨ b≠0) ∧
      a.natAbs≤B ∧ b.natAbs≤B ∧ a*s ≡ b [ZMOD R]) : S.card ≤ 2*B^2 := by
  apply bounded_slopes (by omega : 0<R) S
  intro s hs
  obtain ⟨h,cop,a,b,nonzero,ac,bc,rel⟩ := cover s hs
  have vanishes {z : ℤ} (hcap : z.natAbs ≤ B) (d : (R:ℤ) ∣ z) : z=0 := by
    apply Int.eq_zero_of_abs_lt_dvd d
    rw [← Int.natCast_natAbs]
    exact_mod_cast (hcap.trans_lt small)
  have an : a≠0 := by
    rintro rfl
    have bd : (R:ℤ) ∣ b := Int.modEq_zero_iff_dvd.mp (by simpa using rel.symm)
    exact nonzero.elim (fun h => h rfl) (fun h => h (vanishes bc bd))
  have bn : b≠0 := by
    rintro rfl
    have ad := Int.dvd_of_dvd_mul_left_of_gcd_one (Int.modEq_zero_iff_dvd.mp rel)
      (by exact_mod_cast cop.gcd_eq_one : Int.gcd (R : ℤ) s = 1)
    exact an (vanishes ac ad)
  exact ⟨h,a,b,an,bn,ac,bc,rel⟩

end
end PrimeFactors.WeightSlopeCover
