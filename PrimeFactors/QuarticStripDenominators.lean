import PrimeFactors.QuarticDenominatorSplit
import PrimeFactors.ScaledQuarticMenuBound

/-! Necessary primitive denominators for the two fourth-root recognition
intervals at full width, allowing every initial denominator through 2048. -/
namespace PrimeFactors.QuarticStripDenominators

open RecognizingQuarticProducts
open private PrimeFactors.ScaledQuarticMenuBound.boxes from PrimeFactors.ScaledQuarticMenuBound

set_option maxRecDepth 8192
set_option exponentiation.threshold 4096

theorem coordinate_bounds {n a b d : ℕ} (large : 2^2047≤n) (small : n<2^2048)
    (dp : 0<d) (fit : d≤2048) (point : d^4*n=a^4+4*b^4) :
    (d^4*n<(a+1)^4 → 2^511≤a ∧ b<2^393) ∧
    (d^4*n<4*(b+1)^4 → a<2^394 ∧ 2^511≤b) := by
  have start : 2^2047≤d^4*n := large.trans (by
    simpa only [one_mul] using Nat.mul_le_mul_right n (show 1≤d^4 from pow_pos dp 4))
  have top : d^4*n<2^2092 := calc
    _ ≤ 2048^4*n := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left fit 4)
    _ < 2048^4*2^2048 := Nat.mul_lt_mul_of_pos_left small (by decide)
    _ = _ := by decide +kernel
  have both := PrimeFactors.ScaledQuarticMenuBound.boxes top point
  have edge : 4*((2:ℕ)^511)^4<2^2047 := by decide +kernel
  constructor
  · intro gap
    refine ⟨?_,((both.1 gap).2)⟩
    by_contra! below
    have := Nat.pow_le_pow_left (show a+1≤2^511 by omega) 4
    omega
  · intro gap
    refine ⟨(both.2 gap).1,?_⟩
    by_contra! below
    have := Nat.pow_le_pow_left (show b+1≤2^511 by omega) 4
    omega

/-- The larger quartic factor is at most nine eighths of the smaller one
inside either public recognition interval. -/
theorem close_factors {n a b d : ℕ} (large : 2^2047≤n) (small : n<2^2048)
    (dp : 0<d) (fit : d≤2048) (point : d^4*n=a^4+4*b^4)
    (gap : d^4*n<(a+1)^4 ∨ d^4*n<4*(b+1)^4) : 8*(factors a b).2≤9*(factors a b).1 := by
  have box := coordinate_bounds large small dp fit point
  have sep : 17*(2*a*b)≤a^2+2*b^2 := by
    rcases gap with low|high
    · obtain ⟨big,tiny⟩ := box.1 low
      have h := Nat.mul_le_mul_right a (show 34*b≤a by omega)
      nlinarith only [h,Nat.zero_le (b^2)]
    · obtain ⟨tiny,big⟩ := box.2 high
      have h := Nat.mul_le_mul_right b (show 17*a≤b by omega)
      nlinarith only [h,Nat.zero_le (a^2)]
  have diff := Nat.sub_add_cancel (show 2*a*b≤a^2+2*b^2 by omega)
  dsimp [factors]
  omega

private theorem ratio_parts {U V r s : ℕ} (rp : 0<r) (sp : 0<s)
    (rs : r≤2*s) (sr : s≤2*r) (order : U*r≤V*s) (close : 8*(V*s)≤9*(U*r)) :
    4*U≤9*V ∧ 4*V≤9*U := by
  have a : U*r≤(2*V)*r := order.trans ((Nat.mul_le_mul_left V sr).trans_eq (by ring))
  have b : (4*V)*(2*s)≤(9*U)*(2*s) := calc
    _ = 8*(V*s) := by ring
    _ ≤ 9*(U*r) := close
    _ ≤ 9*(U*(2*s)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ rs)
    _ = _ := by ring
  have left := Nat.le_of_mul_le_mul_right a rp
  exact ⟨by omega,Nat.le_of_mul_le_mul_right b (by positivity)⟩

theorem primitive_split {p q a b d : ℕ} (pp : p.Prime) (qp : q.Prime)
    (po : Odd p) (qo : Odd q) (ordered : p≤q) (balanced : q≤2*p)
    (large : 2^2047≤p*q) (small : p*q<2^2048) (dp : 0<d) (fit : d≤2048)
    (bp : 0<b) (prim : a.Coprime b) (point : d^4*(p*q)=a^4+4*b^4)
    (gap : d^4*(p*q)<(a+1)^4 ∨ d^4*(p*q)<4*(b+1)^4) :
    ∃ u v : ℕ, d=u*v ∧ u.Coprime v ∧ 4*u^4≤9*v^4 ∧ 4*v^4≤9*u^4 := by
  have bound := Nat.pow_le_pow_left fit 4
  have size : 6*d^4≤p*q := by omega
  obtain ⟨u,v,split,cop,orient,_⟩ := QuarticDenominatorSplit.partition pp qp po qo ordered balanced
    bp prim point size
  have close := close_factors large small dp fit point gap
  have order : (factors a b).1≤(factors a b).2 := by dsimp [factors]; omega
  refine ⟨u,v,split,cop,?_⟩
  rcases orient with ⟨left,right⟩|⟨left,right⟩ <;> rw [left,right] at close order
  · exact ratio_parts pp.pos qp.pos (by omega) balanced order close
  · exact ratio_parts qp.pos pp.pos balanced (by omega) order close

private def axes : List ℕ := [1,5,13,17,25,29,37,41]

set_option synthInstance.maxSize 1000 in
private theorem small_axis : ∀ x : Fin 51, 0<x.val →
    (∀ p : Fin 51, p.val.Prime → p.val∣x.val → p.val%4=1) → x.val∈axes := by decide +kernel

set_option synthInstance.maxSize 1000 in
private theorem table : ∀ u ∈ axes, ∀ v ∈ axes, u*v≤2048 → u.Coprime v →
    4*u^4≤9*v^4 → 4*v^4≤9*u^4 → u*v=1 ∨ u*v=725 ∨ u*v=1517 := by decide +kernel

private theorem small_coordinate {u v : ℕ} (size : u*v≤2048) (ratio : 4*u^4≤9*v^4) : u<51 := by
  by_contra! big
  have other : v≤40 := by
    by_contra! large
    have := Nat.mul_le_mul big (show 41≤v by omega)
    omega
  have := Nat.pow_le_pow_left big 4
  have := Nat.pow_le_pow_left other 4
  omega

/-- The coprime, prime-support, ratio and size conditions permit exactly three
denominator values. A realizable semiprime is a separate requirement. -/
theorem menu {d u v : ℕ} (dp : 0<d) (fit : d≤2048) (split : d=u*v) (cop : u.Coprime v)
    (support : ∀ p, p.Prime → p∣d → p%4=1)
    (uv : 4*u^4≤9*v^4) (vu : 4*v^4≤9*u^4) : d=1 ∨ d=725 ∨ d=1517 := by
  subst d
  have upos := Nat.pos_of_mul_pos_right dp
  have vpos := Nat.pos_of_mul_pos_left dp
  have allowed {x : ℕ} (small : x<51) (pos : 0<x) (dv : x∣u*v) : x∈axes := by
    apply small_axis ⟨x,small⟩ pos
    intro p prime div
    exact support p.val prime (div.trans dv)
  have au := allowed (small_coordinate fit uv) upos (dvd_mul_right u v)
  have av := allowed (small_coordinate (by simpa only [Nat.mul_comm v u] using fit) vu) vpos (dvd_mul_left v u)
  exact table u au v av fit cop uv vu

/-- Each remaining denominator meets the arithmetic conditions on the
two parts. This does not assert the existence of a full-width quartic point. -/
theorem menu_iff {d : ℕ} :
    (∃ u v : ℕ, 0<d ∧ d≤2048 ∧ d=u*v ∧ u.Coprime v ∧
      (∀ p, p.Prime → p∣d → p%4=1) ∧ 4*u^4≤9*v^4 ∧ 4*v^4≤9*u^4) ↔
    d=1 ∨ d=725 ∨ d=1517 := by
  constructor
  · rintro ⟨u,v,dp,fit,split,cop,sup,l,r⟩
    exact menu dp fit split cop sup l r
  · have single {p k : ℕ} (pp : p.Prime) (kp : k.Prime) (pass : k%4=1) (dvd : p∣k) : p%4=1 :=
      ((Nat.prime_dvd_prime_iff_eq pp kp).mp dvd) ▸ pass
    rintro (rfl|rfl|rfl)
    · refine ⟨1,1,by decide,by decide,rfl,by decide,?_,by decide,by decide⟩
      exact fun _ pp dvd => False.elim (pp.not_dvd_one dvd)
    · refine ⟨25,29,by decide,by decide,rfl,by decide,?_,by decide,by decide⟩
      intro p pp dvd
      change p∣5^2*29 at dvd
      rcases pp.dvd_mul.mp dvd with five|other
      · exact single pp (by decide : Nat.Prime 5) (by decide) (pp.dvd_of_dvd_pow five)
      · exact single pp (by decide : Nat.Prime 29) (by decide) other
    · refine ⟨37,41,by decide,by decide,rfl,by decide,?_,by decide,by decide⟩
      intro p pp dvd
      change p∣37*41 at dvd
      rcases pp.dvd_mul.mp dvd with first|other
      · exact single pp (by decide : Nat.Prime 37) (by decide) first
      · exact single pp (by decide : Nat.Prime 41) (by decide) other

theorem primitive_menu {p q a b d : ℕ} (pp : p.Prime) (qp : q.Prime)
    (po : Odd p) (qo : Odd q) (ordered : p≤q) (balanced : q≤2*p)
    (large : 2^2047≤p*q) (small : p*q<2^2048) (dp : 0<d) (fit : d≤2048)
    (bp : 0<b) (prim : a.Coprime b) (point : d^4*(p*q)=a^4+4*b^4)
    (gap : d^4*(p*q)<(a+1)^4 ∨ d^4*(p*q)<4*(b+1)^4) :
    d=1 ∨ d=725 ∨ d=1517 := by
  obtain ⟨u,v,split,cop,uv,vu⟩ := primitive_split pp qp po qo ordered balanced large small dp fit
    bp prim point gap
  exact menu dp fit split cop (fun _ prime dvd => LeastPrimitiveQuarticDenominator.prime_support
    prim point prime dvd) uv vu

end PrimeFactors.QuarticStripDenominators
