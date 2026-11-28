import PrimeFactors.CircleBranchCount

/-! Translated overlaps of the two root classes marked by a negative-Jacobi circle target. -/
namespace PrimeFactors.CircleMarkAutocorrelation

open Finset CircleBranchCount
open scoped Classical

/-- Ordered marked pairs at lag `h`, counting each possible starting coordinate once. -/
noncomputable def overlap (n : ℕ) [NeZero n] (a h : ℤ) : ℕ :=
  ((marked n a).filter fun x => x + (h : ZMod n) ∈ marked n a).card

/-- The nonsquare coordinate cannot contribute a mark. -/
theorem mark_left {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    {a : ℤ} (nq : legendreSym q a = -1) (x : ZMod (p*q)) :
    x ∈ marked (p*q) a ↔ (ZMod.chineseRemainder cop x).1 ^ 2 = (a : ZMod p) := by
  let e := ZMod.chineseRemainder cop
  have nq' : (e x).2 ^ 2 ≠ (a : ZMod q) := fun eq =>
    (legendreSym.eq_neg_one_iff q).mp nq ((isSquare_iff_exists_sq _).mpr ⟨_,eq.symm⟩)
  simp only [marked, mem_filter, mem_univ, true_and]
  rw [← isUnit_map_iff e, map_sub, map_intCast, map_pow, Prod.isUnit_iff]
  change ¬(IsUnit ((a : ZMod p) - (e x).1 ^ 2) ∧ IsUnit ((a : ZMod q) - (e x).2 ^ 2)) ↔ (e x).1^2= (a:ZMod p)
  simp only [isUnit_iff_ne_zero, ne_eq, sub_eq_zero, Ne.symm nq', not_false_eq_true, and_true, not_not]
  exact eq_comm

private theorem field_shift {F : Type*} [Field F] {a h x : F} (two : (2:F)≠0)
    (moving : h≠0) :
    x^2=a ∧ (x+h)^2=a ↔ x= -h/2 ∧ h^2=4*a := by
  constructor
  · rintro ⟨left,right⟩
    have hz : h*(2*x+h)=0 := by linear_combination right-left
    have middle := (mul_eq_zero.mp hz).resolve_left moving
    constructor
    · apply (eq_div_iff two).mpr
      linear_combination middle
    · linear_combination 4*left+(h-2*x)*middle
  · rintro ⟨rfl,square⟩
    constructor <;> field_simp <;> linear_combination square

/-- At every lag the overlap has one of three sizes. Here the target is a square
at p and a nonsquare at q. A full p-period shift keeps both root classes. -/
theorem oriented {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (odd : p≠2) {a : ℤ} (sp : legendreSym p a=1)
    (nq : legendreSym q a= -1) (h : ℤ) :
    overlap (p*q) a h = if (h:ZMod p)=0 then 2*q else
      if (h:ZMod p)^2=4*(a:ZMod p) then q else 0 := by
  let cop := (Nat.coprime_primes hp.out hq.out).mpr diff
  let e := ZMod.chineseRemainder cop
  let A := (roots p a).filter fun x => (x+(h:ZMod p))^2=(a:ZMod p)
  have image : ((marked (p*q) a).filter fun x => x+(h:ZMod (p*q))∈marked (p*q) a).map
      e.toEquiv.toEmbedding = A ×ˢ (univ : Finset (ZMod q)) := by
    ext v
    obtain ⟨x,rfl⟩ := e.toEquiv.surjective v
    simp only [mem_map_equiv, Equiv.symm_apply_apply, mem_filter, mark_left cop nq,
      A, roots, mem_product, mem_univ, true_and, and_true, map_add, map_intCast,
      RingEquiv.symm_apply_apply]
    rfl
  have card : overlap (p*q) a h=A.card*q := by
    simpa only [overlap, card_map, card_product, card_univ, ZMod.card] using congrArg Finset.card image
  rw [card]
  split_ifs with zero square
  · have same : A=roots p a := by ext x; simp [A, roots, zero]
    have count := roots_count odd a
    rw [sp] at count
    rw [same, show (roots p a).card=2 by omega]
  · have two : (2:ZMod p)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    have eq : A={-(h:ZMod p)/2} := by
      ext x
      simp only [A, roots, mem_filter, mem_univ, true_and, mem_singleton]
      simp [field_shift two zero, square]
    simp [eq]
  · have two : (2:ZMod p)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    have eq : A=∅ := by
      ext x
      simp only [A, roots, mem_filter, mem_univ, true_and, not_mem_empty, iff_false]
      simp [field_shift two zero, square]
    simp [eq]

/-- The gcd can be evaluated on signed integer representatives of the target and lag. -/
def lagGcd (n : ℕ) (a h : ℤ) : ℕ := n.gcd (h^2-4*a).natAbs

private theorem cast_zero {r : ℕ} (u : ℤ) :
    (u:ZMod r)=0 ↔ r∣u.natAbs := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← Int.natAbs_dvd_natAbs]
  rfl

private theorem lag_dvd {r : ℕ} (a h : ℤ) :
    r∣(h^2-4*a).natAbs ↔ (h:ZMod r)^2=4*(a:ZMod r) := by
  rw [←cast_zero,Int.cast_sub,Int.cast_pow,Int.cast_mul,Int.cast_ofNat,sub_eq_zero]

private theorem oriented_gcd {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a h : ℤ} (sp : legendreSym p a=1)
    (nq : legendreSym q a= -1) (unit : h.natAbs.Coprime (p*q)) :
    overlap (p*q) a h = if lagGcd (p*q) a h=1 then 0 else (p*q)/lagGcd (p*q) a h := by
  have nz : (h:ZMod p)≠0 := fun z => hp.out.coprime_iff_not_dvd.mp
    (unit.of_dvd_right (dvd_mul_right p q)).symm ((cast_zero h).mp z)
  have two : (2:ZMod q)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have no : ¬q∣(h^2-4*a).natAbs := by
    intro dv
    have sq := (lag_dvd a h).mp dv
    apply (legendreSym.eq_neg_one_iff q).mp nq
    refine (isSquare_iff_exists_sq _).mpr ⟨(h:ZMod q)/2,?_⟩
    symm
    field_simp
    linear_combination sq
  have cq := hq.out.coprime_iff_not_dvd.mpr no
  rw [oriented diff op sp nq,if_neg nz]
  split_ifs with square one one
  · have g : lagGcd (p*q) a h=p := by
      rw [lagGcd,Nat.mul_comm]
      exact Nat.gcd_mul_of_coprime_of_dvd cq ((lag_dvd a h).mpr square)
    exact (hp.out.ne_one (g.symm.trans one)).elim
  · have g : lagGcd (p*q) a h=p := by
      rw [lagGcd,Nat.mul_comm]
      exact Nat.gcd_mul_of_coprime_of_dvd cq ((lag_dvd a h).mpr square)
    simp [g,hp.out.pos]
  · rfl
  · exact (one (Nat.coprime_mul_iff_left.mpr ⟨hp.out.coprime_iff_not_dvd.mpr (mt (lag_dvd a h).mp square),cq⟩).gcd_eq_one).elim

/-- A nonzero overlap at a unit lag can be evaluated by one gcd and an exact division. -/
theorem unit_gcd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q)
    (op : p≠2) (oq : q≠2) {a h : ℤ} (neg : jacobiSym a (p*q)= -1)
    (unit : h.natAbs.Coprime (p*q)) :
    overlap (p*q) a h = if lagGcd (p*q) a h=1 then 0 else (p*q)/lagGcd (p*q) a h := by
  rcases opposite neg with signs|signs
  · exact oriented_gcd diff op oq signs.1 signs.2 unit
  · let P (n : ℕ) : Prop := ∀ nz : NeZero n,
        @overlap n nz a h = if lagGcd n a h=1 then 0 else n/lagGcd n a h
    have rev : P (q*p) := fun _ =>
      oriented_gcd diff.symm oq op signs.2 signs.1 (by simpa only [Nat.mul_comm q p] using unit)
    exact (Nat.mul_comm q p ▸ rev : P (p*q)) inferInstance

private theorem abs_coprime (n : ℕ) (u : ℤ) :
    IsUnit (u : ZMod n) ↔ n.Coprime u.natAbs := by
  have abs : IsUnit (u : ZMod n) ↔ IsUnit (u.natAbs : ZMod n) := by
    obtain e|e := Int.natAbs_eq u
    · conv_lhs => rw [e,Int.cast_natCast]
    · conv_lhs => rw [e,Int.cast_neg,Int.cast_natCast]
      simp
  exact abs.trans ((ZMod.isUnit_iff_coprime _ _).trans Nat.coprime_comm)

/-- Doubling is a bijection at an odd modulus. The mark at the half-lag
detects exactly when the lag discriminant has a nontrivial gcd. -/
theorem half_mark {n : ℕ} [NeZero n] (odd : Odd n) {a h : ℤ} {x : ZMod n}
    (half : 2*x=(h:ZMod n)) :
    x∈marked n a ↔ lagGcd n a h≠1 := by
  have two : IsUnit (2:ZMod n) := (ZMod.isUnit_iff_coprime 2 n).mpr odd.coprime_two_left
  have unit : IsUnit (-((2:ZMod n)^2)) := (two.pow 2).neg
  have eq : ((h^2-4*a : ℤ):ZMod n) = -((2:ZMod n)^2)*((a:ZMod n)-x^2) := by
    push_cast
    rw [←half]
    ring
  have gcd := abs_coprime n (h^2-4*a)
  rw [eq,IsUnit.mul_iff, and_iff_right unit] at gcd
  simpa only [marked,mem_filter,mem_univ,true_and,lagGcd,Nat.Coprime] using gcd.not

/-- An explicit half-lag using only the odd modulus and the integer shift. -/
theorem half_coordinate {n : ℕ} (odd : Odd n) (h : ℤ) :
    2*((((n+1)/2 : ℕ) : ZMod n)*(h:ZMod n))=(h:ZMod n) := by
  obtain ⟨k,hk⟩ := odd
  have eq : 2*((n+1)/2)=n+1 := by omega
  have cast := congrArg (fun u:ℕ => (u:ZMod n)) eq
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,ZMod.natCast_self,zero_add] at cast
  rw [←mul_assoc,cast,one_mul]

/-- A unit-lag correlation is positive precisely when an ordinary mark occurs at h/2. -/
theorem unit_half {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (diff : p≠q)
    (op : p≠2) (oq : q≠2) {a h : ℤ} (neg : jacobiSym a (p*q)= -1)
    (unit : h.natAbs.Coprime (p*q)) {x : ZMod (p*q)} (half : 2*x=(h:ZMod (p*q))) :
    0<overlap (p*q) a h ↔ x∈marked (p*q) a := by
  have odd := (hp.out.odd_of_ne_two op).mul (hq.out.odd_of_ne_two oq)
  rw [half_mark odd half,unit_gcd diff op oq neg unit]
  split_ifs with one
  · simp [one]
  · have pos := Nat.mul_pos hp.out.pos hq.out.pos
    exact iff_of_true (Nat.div_pos (Nat.le_of_dvd pos (Nat.gcd_dvd_left _ _))
      (Nat.gcd_pos_of_pos_left _ pos)) one

/-- The zero lag and a complete local period keep all 22 marks. The two
unit lags distinguish an overlap of eleven from a disjoint translate. -/
theorem seventy_seven : overlap 77 2 0=22 ∧ overlap 77 2 1=11 ∧
    overlap 77 2 2=0 ∧ overlap 77 2 7=22 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have formula := oriented (p:=7) (q:=11) (a:=2) (by decide) (by decide)
    (by norm_num) (by norm_num)
  change overlap (7*11) 2 0=_ ∧ overlap (7*11) 2 1=_ ∧ overlap (7*11) 2 2=_ ∧
    overlap (7*11) 2 7=_
  rw [formula,formula,formula,formula]
  decide

end PrimeFactors.CircleMarkAutocorrelation
