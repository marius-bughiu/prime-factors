import PrimeFactors.GapStride
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace PrimeFactors

/-- Two first factors in a fixed congruence class cannot give different
products in a short interval when the half-gap is fixed. -/
theorem advice_factor_unique {x y X D L M : ℕ} (hx : X ≤ x) (hy : X ≤ y)
    (bx : L ≤ x*(x+2*D) ∧ x*(x+2*D) < L+2*X*M)
    (by' : L ≤ y*(y+2*D) ∧ y*(y+2*D) < L+2*X*M)
    (same : x ≡ y [MOD M]) : x = y := by
  have exclude {p q : ℕ} (low : X ≤ p) (ord : p < q) (lo : L ≤ p*(p+2*D))
      (hi : q*(q+2*D) < L+2*X*M) (cong : p ≡ q [MOD M]) : False := by
    have gap := Nat.le_of_dvd (Nat.sub_pos_of_lt ord) ((Nat.modEq_iff_dvd' ord.le).mp cong)
    obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le ord.le
    have mz : M ≤ z := by omega
    have mul := Nat.mul_le_mul (show 2*X ≤ 2*p from by omega) mz
    have spread : q*(q+2*D) = p*(p+2*D)+2*p*z+z*(z+2*D) := by rw [hz]; ring
    omega
  rcases lt_trichotomy x y with lt | eq | gt
  · exact (exclude hx lt bx.1 by'.2 same).elim
  · exact eq
  · exact (exclude hy gt by'.1 bx.2 same.symm).elim

/-- For a given product suffix and residual half-gap c, the shifted first
factor must occupy one of these square-root classes. -/
noncomputable def adviceRootClasses (Q a m c : ℕ) : Finset ℕ :=
  (Finset.range Q).filter fun y => y^2 ≡ a+(m*c)^2 [MOD Q]

/-- Count pairs (residual half-gap, first factor) in one prefix/suffix cell.
Each root class occurs at most W times if the product interval has width
at most 2*X*Q*W. This is an integer count, without a prime-density assumption. -/
theorem advice_cell_card {s : Finset (ℕ × ℕ)} {cofactors : Finset ℕ} {X L Q W m a : ℕ}
    (hq : 0 < Q) (hw : 0 < W)
    (inside : ∀ t ∈ s, t.1 ∈ cofactors ∧ X ≤ t.2 ∧
      L ≤ t.2*(t.2+2*(m*t.1)) ∧ t.2*(t.2+2*(m*t.1)) < L+2*X*(Q*W) ∧
      t.2*(t.2+2*(m*t.1)) ≡ a [MOD Q]) :
    s.card ≤ ∑ c ∈ cofactors, (adviceRootClasses Q a m c).card * W := by
  let key (t : ℕ × ℕ) : Σ _ : ℕ, ℕ × ℕ :=
    ⟨t.1, (t.2+m*t.1)%Q, (t.2/Q)%W⟩
  let bins := cofactors.sigma fun c => (adviceRootClasses Q a m c) ×ˢ Finset.range W
  have count : bins.card = ∑ c ∈ cofactors, (adviceRootClasses Q a m c).card*W := by
    simp [bins, Finset.card_sigma]
  rw [← count]
  apply Finset.card_le_card_of_injOn key
  · intro t ht
    obtain ⟨hc,_,_,_,last⟩ := inside t ht
    have sq : (t.2+m*t.1)^2 = t.2*(t.2+2*(m*t.1))+(m*t.1)^2 := by ring
    have root := ((Nat.mod_modEq (t.2+m*t.1) Q).pow 2).trans
      (sq ▸ last.add_right ((m*t.1)^2) : (t.2+m*t.1)^2 ≡ a+(m*t.1)^2 [MOD Q])
    exact Finset.mem_sigma.mpr ⟨hc, Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq),root⟩,
        Finset.mem_range.mpr (Nat.mod_lt _ hw)⟩⟩
  · rintro ⟨c,x⟩ ht ⟨d,y⟩ ht' eq
    have cd : c=d := congrArg Sigma.fst eq
    subst d
    have root : (x+m*c)%Q=(y+m*c)%Q := congrArg (fun v : Σ _ : ℕ, ℕ × ℕ => v.2.1) eq
    have digit : x/Q%W=y/Q%W := congrArg (fun v : Σ _ : ℕ, ℕ × ℕ => v.2.2) eq
    have low : x%Q=y%Q := Nat.ModEq.add_right_cancel' (m*c) root
    have congr : x ≡ y [MOD Q*W] := by
      unfold Nat.ModEq; rw [Nat.mod_mul, Nat.mod_mul, low, digit]
    obtain ⟨_,hx,lx,ux,_⟩ := inside _ ht
    obtain ⟨_,hy,ly,uy,_⟩ := inside _ ht'
    exact Prod.ext rfl (advice_factor_unique hx hy ⟨lx,ux⟩ ⟨ly,uy⟩ congr)

end PrimeFactors
