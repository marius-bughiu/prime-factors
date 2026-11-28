import PrimeFactors.FractionalBalancedLifts

/-! Sharp additive bound at the one-eighth modulus cutoff when both pairs are
balanced and consist of distinct primes above three. The bounds classify
compatible products and supply no procedure for locating a prime pair. -/

namespace PrimeFactors.FractionalPrimeLiftCutoff

open FractionalBalancedLifts

/-- For a lift by exactly one positive period, an offset below seventeen
would force twin primes. Their product is minus one modulo nine. -/
theorem positive_period {n m x y : ℕ} (hx : x.Prime) (hy : y.Prime)
    (large : 3<x) (ord : x<y) (upper : 2*(x+y)^2<9*n) (prod : x*y=n+m) :
    8*m+17≤n := by
  by_contra! near
  obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le ord.le
  have small : 2*a^2<17 := by nlinarith only [upper,prod,near]
  have bound : a≤2 := by
    by_contra! h
    have three : 3≤a := by omega
    nlinarith only [small, Nat.mul_le_mul three three]
  obtain ⟨i,hi⟩ := hx.odd_of_ne_two (by omega)
  obtain ⟨j,hj⟩ := hy.odd_of_ne_two (by omega)
  have twin : a=2 := by omega
  subst a
  have xd : ¬3∣x := by
    intro d
    have := (Nat.dvd_prime hx).mp d
    omega
  have yd : ¬3∣x+2 := by
    intro d
    have := (Nat.dvd_prime hy).mp d
    omega
  have mid : 3∣x+1 := by
    rw [Nat.dvd_iff_mod_eq_zero] at xd yd ⊢
    have r := Nat.mod_lt x (by decide : 0<3)
    rcases (show x%3=0 ∨ x%3=1 ∨ x%3=2 by omega) with hr | hr | hr
    · exact (xd hr).elim
    · exact (yd (by rw [Nat.add_mod,hr])).elim
    · rw [Nat.add_mod,hr]
  obtain ⟨k,hk⟩ := mid
  have square : x*(x+2)+1=9*(k*k) := by
    calc
      _ = (x+1)*(x+1) := by ring
      _ = _ := by rw [hk]; ring
  have lower : 8*m+8<n := by nlinarith only [upper,prod]
  omega

/-- Classification of the small genuine products needed for negative lifts. -/
theorem small_products {x y : ℕ} (hx : x.Prime) (hy : y.Prime) (large : 3<x)
    (ord : x<y) (bal : y<2*x) (small : x*y≤135) : x*y=35 ∨ x*y=77 ∨ x*y=91 := by
  have xb : x<12 := by
    by_contra! h
    have hh : 12≤y := by omega
    have := Nat.mul_le_mul h hh
    omega
  have yb : y<24 := by omega
  have table : ∀ a : Fin 12, ∀ b : Fin 24, 3<a.val → a.val.Prime → b.val.Prime →
      a.val<b.val → b.val<2*a.val → a.val*b.val≤135 →
      a.val*b.val=35 ∨ a.val*b.val=77 ∨ a.val*b.val=91 := by decide +kernel
  exact table ⟨x,xb⟩ ⟨y,yb⟩ large hx hy ord bal small

/-- Every unequal compatible product requires at least seventeen units of
slack below the scaled one-eighth threshold. The conclusion includes lifts
by any number of periods, in either direction. -/
theorem false_lift_gap {p q x y m : ℕ} (hp : p.Prime) (hq : q.Prime) (pl : 3<p)
    (po : p<q) (pb : q<2*p) (hx : x.Prime) (hy : y.Prime) (xl : 3<x)
    (xo : x<y) (xb : y<2*x) (win : InWindow (p*q) (x+y))
    (same : x*y ≡ p*q [MOD m]) (different : x*y ≠ p*q) : 8*m+17≤p*q := by
  by_contra! near
  obtain ⟨lo,hi⟩ := product_bounds xo.le xb win
  have op := hp.odd_of_ne_two (by omega)
  have oq := hq.odd_of_ne_two (by omega)
  obtain ⟨k,hk⟩ := op.mul oq
  have p5 : 5≤p := by obtain ⟨i,hl⟩ := op; omega
  have q7 : 7≤q := by obtain ⟨i,hl⟩ := oq; omega
  have wide : 35≤p*q := Nat.mul_le_mul p5 q7
  rcases lt_or_gt_of_ne different with below | above
  · have span : x*y+m≤p*q := by
      by_contra! close
      exact (not_le_of_gt below) (same.symm.le_of_lt_add (by omega))
    have small : p*q≤135 := by omega
    have orig := small_products hp hq pl po pb small
    have cand := small_products hx hy xl xo xb (below.le.trans small)
    omega
  · have span : p*q+m≤x*y := by
      by_contra! close
      exact (not_le_of_gt above) (same.le_of_lt_add (by omega))
    have step : p*q+m ≡ p*q [MOD m] := Nat.add_modEq_right
    have back : x*y≤p*q+m := (same.trans step.symm).le_of_lt_add (by omega)
    exact (not_le_of_gt near) (positive_period hx hy xl xo win.2 (le_antisymm back span))

/-- The ten-bit control realizes every hypothesis of the gap theorem with
equality. All four entries are least representatives below the modulus. -/
theorem attained :
    ∃ p q x y m : ℕ, p.Prime ∧ q.Prime ∧ 3<p ∧ p<q ∧ q<2*p ∧
      x.Prime ∧ y.Prime ∧ 3<x ∧ x<y ∧ y<2*x ∧ InWindow (p*q) (x+y) ∧
      x*y ≡ p*q [MOD m] ∧ x*y≠p*q ∧ 8*m+17=p*q ∧ q<m ∧ y<m := by
  obtain ⟨hp,hq,hx,hy,_⟩ := ten_bit_prime_control
  refine ⟨643,907,809,811,72898,hp,hq,?_,?_,?_,hx,hy,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    decide +kernel

end PrimeFactors.FractionalPrimeLiftCutoff
