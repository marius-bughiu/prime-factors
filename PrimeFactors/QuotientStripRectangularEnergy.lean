import PrimeFactors.QuotientStripDiscriminantMultiplicity
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Tactic

namespace PrimeFactors.QuotientStripRectangularEnergy

open Finset QuotientStripDiscriminantMultiplicity
set_option exponentiation.threshold 4096
set_option maxRecDepth 8000

private def rect (A B : ℕ) : Finset Pair := Icc 1 A ×ˢ Icc 1 B

private theorem mem_rect {A B a b : ℕ} :
    (a,b) ∈ rect A B ↔ (0<a ∧ a≤A) ∧ (0<b ∧ b≤B) := by simp [rect, Nat.succ_le_iff]
private theorem rect_card (A B : ℕ) : (rect A B).card = A*B := by simp [rect]

private def codes (U V : ℕ) : ℕ → Finset (Pair × Pair)
  | 0 => rect 1 1 ×ˢ rect U V
  | k+1 =>
    let K := 2^k
    codes U V k ∪ ((rect (2*K) (2*K) \ rect K K) ×ˢ rect (U/K) (V/K))

private theorem code_count (U V k : ℕ) :
    (codes U V k).card ≤ U*V*(1+3*k) := by
  induction k with
  | zero => simp [codes,card_product,rect_card]
  | succ k ih =>
    let K := 2^k
    have sub : rect K K ⊆ rect (2*K) (2*K) := by
      rintro ⟨a,b⟩ h
      rw [mem_rect] at h ⊢
      omega
    have binCount : (rect (2*K) (2*K) \ rect K K).card = 3*(K*K) := by
      rw [card_sdiff sub,rect_card,rect_card]
      have eqn : (2*K)*(2*K) = 3*(K*K)+K*K := by ring
      rw [eqn,Nat.add_sub_cancel]
    have cu := Nat.div_mul_le_self U K
    have cv := Nat.div_mul_le_self V K
    have bin : (3*(K*K))*((U/K)*(V/K)) ≤ 3*(U*V) := calc
      _ = 3*((U/K*K)*(V/K*K)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul cu cv)
    change ((codes U V k) ∪ ((rect (2*K) (2*K) \ rect K K) ×ˢ rect (U/K) (V/K))).card ≤ _
    apply (card_union_le ..).trans
    rw [card_product,binCount,rect_card]
    exact (Nat.add_le_add ih bin).trans_eq (by ring)

private theorem coded {a b g h U V k : ℕ}
    (ap : 0<a) (bp : 0<b) (gp : 0<g) (hp : 0<h)
    (ga : g*a≤U) (gb : g*b≤U) (ha : h*a≤V) (hb : h*b≤V)
    (ac : a≤2^k) (bc : b≤2^k) : ((a,b),(g,h)) ∈ codes U V k := by
  induction k with
  | zero =>
    have au := (Nat.le_mul_of_pos_right g ap).trans ga
    have ah := (Nat.le_mul_of_pos_right h ap).trans ha
    exact mem_product.mpr ⟨mem_rect.mpr ⟨⟨ap,ac⟩,⟨bp,bc⟩⟩,
      mem_rect.mpr ⟨⟨gp,au⟩,⟨hp,ah⟩⟩⟩
  | succ k ih =>
    let K := 2^k
    change _∈codes U V k ∪ ((rect (2*K) (2*K) \ rect K K) ×ˢ rect (U/K) (V/K))
    by_cases small : a≤K ∧ b≤K
    · exact mem_union_left _ (ih small.1 small.2)
    · have gt : K≤a ∨ K≤b := by omega
      have kp : 0<K := by dsimp only [K]; positivity
      have gfit : g≤U/K := (Nat.le_div_iff_mul_le kp).mpr (gt.elim
        (fun lt => (Nat.mul_le_mul_left g lt).trans ga) (fun lt => (Nat.mul_le_mul_left g lt).trans gb))
      have hfit : h≤V/K := (Nat.le_div_iff_mul_le kp).mpr (gt.elim
        (fun lt => (Nat.mul_le_mul_left h lt).trans ha) (fun lt => (Nat.mul_le_mul_left h lt).trans hb))
      apply mem_union_right _
      refine mem_product.mpr ⟨mem_sdiff.mpr ⟨mem_rect.mpr ⟨⟨ap,?_⟩,⟨bp,?_⟩⟩,?_⟩,
        mem_rect.mpr ⟨⟨gp,gfit⟩,⟨hp,hfit⟩⟩⟩
      · simpa [K,pow_succ,Nat.mul_comm] using ac
      · simpa [K,pow_succ,Nat.mul_comm] using bc
      · intro mem
        exact small ⟨(mem_rect.mp mem).1.2,(mem_rect.mp mem).2.2⟩

private def decode (x : Pair × Pair) : Pair × Pair :=
  let (a,b) := x.1
  let (g,h) := x.2
  ((g*a,h*b),(g*b,h*a))

private theorem decompose {x y w t : ℕ} (xp : 0<x) (yp : 0<y)
    (wp : 0<w) (eqn : x*y=w*t) :
    ∃ a b g h, 0<a ∧ 0<b ∧ 0<g ∧ 0<h ∧ g*a=x ∧ g*b=w ∧ h*b=y ∧ h*a=t := by
  let g := x.gcd w
  let a := x/g
  let b := w/g
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ xp
  have gx : g*a=x := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have gw : g*b=w := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have ap : 0<a := Nat.pos_of_mul_pos_left (gx.symm ▸ xp)
  have bp : 0<b := Nat.pos_of_mul_pos_left (gw.symm ▸ wp)
  have cop : a.Coprime b := Nat.gcd_div_gcd_div_gcd_of_pos_left xp
  have cross : a*y=b*t := Nat.eq_of_mul_eq_mul_left gp (by
    rw [←Nat.mul_assoc,←Nat.mul_assoc,gx,gw,eqn])
  have divides : b∣y := cop.symm.dvd_of_dvd_mul_left (cross ▸ dvd_mul_right b t)
  obtain ⟨h,yh⟩ := divides
  have hp : 0<h := Nat.pos_of_mul_pos_left (yh ▸ yp)
  refine ⟨a,b,g,h,ap,bp,gp,hp,gx,gw,by rw [yh,Nat.mul_comm],?_⟩
  apply Nat.eq_of_mul_eq_mul_left bp
  rw [←cross,yh]
  ring

/-- Rectangular multiplication energy. Splitting equal-product pairs by the
dyadic size of the larger reduced coordinate costs at most 3UV per scale. -/
theorem rectangle (U V k : ℕ) (cap : V≤2^k) :
    mulEnergy (Icc 1 U) (Icc 1 V) ≤ U*V*(1+3*k) := by
  rw [mulEnergy_eq_card_filter]
  have cover : ((rect U V ×ˢ rect U V).filter (fun r => r.1.1*r.1.2=r.2.1*r.2.2)) ⊆
      (codes U V k).image decode := by
    rintro ⟨⟨x,y⟩,w,t⟩ h
    obtain ⟨mem,eqn⟩ := mem_filter.mp h
    obtain ⟨xy,wt⟩ := mem_product.mp mem
    obtain ⟨⟨xp,xu⟩,⟨yp,yv⟩⟩ := mem_rect.mp xy
    obtain ⟨⟨wp,wu⟩,⟨_,tv⟩⟩ := mem_rect.mp wt
    obtain ⟨a,b,g,h,ap,bp,gp,hp,gx,gw,hy,ht⟩ := decompose xp yp wp eqn
    have aV := (Nat.le_mul_of_pos_left a hp).trans (ht.le.trans tv)
    have bV := (Nat.le_mul_of_pos_left b hp).trans (hy.le.trans yv)
    exact mem_image.mpr ⟨((a,b),(g,h)),coded ap bp gp hp (gx.le.trans xu) (gw.le.trans wu)
      (ht.le.trans tv) (hy.le.trans yv) (aV.trans cap) (bV.trans cap),by simp [decode,gx,gw,hy,ht]⟩
  exact (card_le_card cover).trans (card_image_le.trans (code_count U V k))

/-- Arbitrary subsets of the rectangle inherit the complete rectangle's
energy budget, regardless of how the slopes and their labels were chosen. -/
theorem subset_energy (rows : Finset Pair) {U V k : ℕ}
    (box : ∀ s∈rows, 0<s.1 ∧ s.1≤U ∧ 0<s.2 ∧ s.2≤V) (cap : V≤2^k) :
    rows.card^2 ≤ (rows.image weight).card * (U*V*(1+3*k)) := by
  let R := rect U V
  let P := rows.image weight
  have sub : rows ⊆ R.filter (fun s => s.1*s.2 ∈ P) := by
    intro a ha
    obtain ⟨ap,au,bp,bv⟩ := box a ha
    exact mem_filter.mpr ⟨mem_rect.mpr ⟨⟨ap,au⟩,⟨bp,bv⟩⟩,mem_image_of_mem weight ha⟩
  calc
    _ ≤ (R.filter (fun s => s.1*s.2 ∈ P)).card^2 := Nat.pow_le_pow_left (card_le_card sub) 2
    _ ≤ P.card*mulEnergy (Icc 1 U) (Icc 1 V) := card_sq_le_card_mul_mulEnergy _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _ (rectangle U V k cap)

/-- Bound after allowing all label and weight-product collisions in the
complete box, using distinct prime factors solely for the four-root bound. -/
theorem target {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (rows : Finset Pair) (z : Pair → ℤ) (many : 2^653 ≤ rows.card)
    (box : ∀ s∈rows, 0<s.1 ∧ s.1≤9*2^327 ∧ 0<s.2 ∧ s.2≤7*2^327)
    (bounds : ∀ s∈rows, 0≤z s ∧ z s<(p*q:ℕ)) :
    2^634 < (rows.image (discriminant (p*q) z)).card := by
  have en := subset_energy rows box (show 7*2^327≤(2:ℕ)^330 by decide +kernel)
  have mult := four_fold hp hq hne rows z bounds
  by_contra! bad
  have bound := Nat.mul_le_mul_right (9*2^327*(7*2^327)*(1+3*330)) (mult.trans (Nat.mul_le_mul_left 4 bad))
  have left := (Nat.pow_le_pow_left many 2).trans (en.trans bound)
  exact (by decide +kernel : ¬ (2^653:ℕ)^2 ≤ 4*2^634*(9*2^327*(7*2^327)*(1+3*330))) left

end PrimeFactors.QuotientStripRectangularEnergy
