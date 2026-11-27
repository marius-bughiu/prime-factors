import PrimeFactors.TwelveImageSize
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! A second collision comparison costs one multiplication of an existing
key. Its extra matches occur precisely at primes where three is a square. -/
namespace PrimeFactors.ComplementaryKeys
open Finset TwelveResidueCollision TwelveImageSize

def fold {R : Type*} [CommRing R] (z : R) := z*(1-z)

theorem fold_eq {K : Type*} [Field K] (u v : K) :
    fold u=fold v ↔ u=v ∨ v=1-u := by
  have h : fold u-fold v=(u-v)*(1-u-v) := by unfold fold; ring
  rw [←sub_eq_zero,h,mul_eq_zero,sub_eq_zero,sub_eq_zero,eq_comm (a:=1-u)]

private def sinNum {K : Type*} [Field K] (x : K) := 6*x*(x^2-1)*(x^2-9)
private def cosPart {K : Type*} [Field K] (x : K) := sextic x/(x^2+3)^3
private def sinPart {K : Type*} [Field K] (x : K) := sinNum x/(x^2+3)^3

private theorem cos_sq {K : Type*} [Field K] (x : K) : (cosPart x)^2=value x := by
  simp [cosPart,value,den,num,div_pow,←pow_mul]

private theorem complementary {K : Type*} [Field K] {x : K} (dx : den x≠0) :
    1-value x=3*(sinPart x)^2 := by
  have nz : x^2+3≠0 := by simpa [den] using dx
  unfold sinPart sinNum value num sextic den
  field_simp [nz]
  ring

/-- A complement match gives an actual square root of three in the field. -/
theorem complement_implies_square {K : Type*} [Field K] (char : (108:K)≠0) {x y : K}
    (reg : mask x≠0) (hit : value y=1-value x) : IsSquare (3:K) := by
  obtain ⟨dx,_,diff⟩ := (regular_iff char x).mp reg
  have one : value x≠1 := by simpa [value,div_eq_one_iff_eq dx] using Ne.symm diff
  have si : sinPart x≠0 := by
    intro z
    have h := complementary dx
    rw [z] at h
    apply one
    linear_combination -h
  have eq : (cosPart y)^2=3*(sinPart x)^2 := by rw [cos_sq,hit,complementary dx]
  refine ⟨cosPart y/sinPart x, ?_⟩
  field_simp [si]
  linear_combination -eq

private def homCos {K : Type*} [Field K] (a b : K) :=
  a^6-45*a^4*b^2+135*a^2*b^4-27*b^6

private theorem rotate_forms {K : Type*} [Field K] {s : K} (ss : s^2=3) (x : K) :
    (s*x-3)^2+3*(x+s)^2=6*(x^2+3) ∧
    homCos (s*x-3) (x+s)=216*s*sinNum x := by
  have h3 : s^3=3*s := by rw [pow_succ,ss]
  have h4 : s^4=9 := by rw [show (4:ℕ)=2*2 by decide,pow_mul,ss]; norm_num
  have h5 : s^5=9*s := by rw [pow_succ,h4]
  have h6 : s^6=27 := by rw [show (6:ℕ)=2*3 by decide,pow_mul,ss]; norm_num
  constructor
  · linear_combination (x^2+3)*ss
  · unfold homCos sinNum
    ring_nf
    simp only [ss,h3,h4,h5,h6]
    ring

private theorem rotate {K : Type*} [Field K] (char : (108:K)≠0) {s x : K} (ss : s^2=3)
    (reg : mask x≠0) : ∃ y, mask y≠0 ∧ value y=1-value x := by
  obtain ⟨dx,nx,neq⟩ := (regular_iff char x).mp reg
  have nz : x^2+3≠0 := by simpa [den] using dx
  have nz6 : (6:K)≠0 := fun z => char (by linear_combination 18*z)
  have v : x+s≠0 := by
    intro z
    have bad : x^2-3=0 := by linear_combination (x-s)*z+ss
    exact reg (by simp [mask,bad])
  let y := (s*x-3)/(x+s)
  obtain ⟨f,g⟩ := rotate_forms ss x
  have yy : y^2+3=6*(x^2+3)/(x+s)^2 := by
    dsimp [y]
    field_simp [v]
    linear_combination f
  have dy : den y≠0 := by simpa [den,yy] using
    (div_ne_zero (mul_ne_zero nz6 nz) (pow_ne_zero 2 v))
  have sy : sextic y=homCos (s*x-3) (x+s)/(x+s)^6 := by
    unfold sextic homCos y
    field_simp [v]
    ring
  have cs : cosPart y=s*sinPart x := by
    rw [cosPart,yy,sy,g,sinPart]
    field_simp [v,nz6,nz]
    ring
  have hit : value y=1-value x := by rw [←cos_sq,cs,mul_pow,ss,complementary dx]
  have vx : value x≠0 := div_ne_zero nx dx
  have vx1 : value x≠1 := by simpa [value,div_eq_one_iff_eq dx] using Ne.symm neq
  refine ⟨y,(regular_iff char y).mpr ⟨dy,?_,?_⟩,hit⟩
  · intro zero
    have h : value y=0 := by simp [value,zero]
    exact vx1 (by linear_combination hit-h)
  · intro same
    have h : value y=1 := (div_eq_one_iff_eq dy).mpr same.symm
    exact vx (by linear_combination hit-h)

/-- The second admissible value occurs for every regular seed at a
square-three prime and for no regular seed at a nonsquare-three prime. -/
theorem complement_iff {K : Type*} [Field K] (char : (108:K)≠0) {x : K}
    (reg : mask x≠0) : (∃ y, mask y≠0 ∧ value y=1-value x) ↔ IsSquare (3:K) := by
  constructor
  · rintro ⟨y,_,hit⟩
    exact complement_implies_square char reg hit
  · rintro ⟨s,ss⟩
    exact rotate char (by rw [sq,←ss]) reg

private theorem nonzero108 {p : ℕ} [Fact p.Prime] (big : 864<p) : (108:ZMod p)≠0 := by
  exact_mod_cast (show ((108:ℕ):ZMod p)≠0 by
    rw [Ne,ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega))

private theorem old_fiber {p : ℕ} [Fact p.Prime] (big : 864<p)
    {x : ZMod p} (rx : x∈regulars p) :
    ((regulars p).filter (fun y => value y=value x)).card=12 := by
  rw [←regular_fiber big rx]
  congr 1
  ext y
  simp only [mem_filter,and_congr_right_iff]
  intro hy
  have dx := ((regular_iff (nonzero108 big) x).mp (mem_filter.mp rx).2).1
  have dy := ((regular_iff (nonzero108 big) y).mp (mem_filter.mp hy).2).1
  exact (div_eq_div_iff dy dx).trans eq_comm

/-- Number of additional local partners before merging the shared middle value. -/
theorem complement_count {p : ℕ} [Fact p.Prime] (big : 864<p)
    {x : ZMod p} (rx : x∈regulars p) :
    ((regulars p).filter (fun y => value y=1-value x)).card=
      if IsSquare (3:ZMod p) then 12 else 0 := by
  classical
  have chars := complement_iff (nonzero108 big) (mem_filter.mp rx).2
  split_ifs with is
  · obtain ⟨y,ry,hy⟩ := chars.mpr is
    rw [←hy]
    exact old_fiber big (mem_filter.mpr ⟨mem_univ _,ry⟩)
  · apply card_eq_zero.mpr
    apply eq_empty_iff_forall_not_mem.mpr
    intro z inc
    obtain ⟨r,h⟩ := mem_filter.mp inc
    exact is (chars.mp ⟨z,(mem_filter.mp r).2,h⟩)

/-- The only possible overlap of the old and new comparisons is a label
equal to its complement. It can be detected on the public product. -/
theorem fold_count {p : ℕ} [Fact p.Prime] (big : 864<p) {x : ZMod p}
    (rx : x∈regulars p) (apart : value x≠1-value x) :
    ((regulars p).filter (fun y => fold (value x)=fold (value y))).card =
      12 + (if IsSquare (3:ZMod p) then 12 else 0) := by
  classical
  let a := (regulars p).filter (fun y => value y=value x)
  let b := (regulars p).filter (fun y => value y=1-value x)
  have union : (regulars p).filter (fun y => fold (value x)=fold (value y))=a∪b := by
    ext y
    simp [a,b,fold_eq,eq_comm (a:=value x) (b:=value y),and_or_left]
  have dis : Disjoint a b := by
    apply disjoint_left.mpr
    intro y ha hb
    exact apart ((mem_filter.mp ha).2.symm.trans (mem_filter.mp hb).2)
  rw [union,card_union_of_disjoint dis,old_fiber big rx,complement_count big rx]

/-- The fixed label accounts for at most twelve possible seeds at any prime. -/
theorem middle_bound {p : ℕ} [Fact p.Prime] (big : 864<p) :
    ((regulars p).filter (fun x => value x=1-value x)).card≤12 := by
  classical
  let s := (regulars p).filter (fun x => value x=1-value x)
  by_cases h : s.Nonempty
  · obtain ⟨x,hx⟩ := h
    obtain ⟨rx,middle⟩ := mem_filter.mp hx
    have two : (2:ZMod p)≠0 := fun z => nonzero108 big (by linear_combination 54*z)
    have sub : s⊆(regulars p).filter (fun y => value y=value x) := by
      intro y hy
      obtain ⟨ry,n⟩ := mem_filter.mp hy
      refine mem_filter.mpr ⟨ry,(mul_left_cancel₀ two ?_)⟩
      linear_combination n-middle
    exact (card_le_card sub).trans (old_fiber big rx).le
  · change s.card ≤ 12
    simp [not_nonempty_iff_eq_empty.mp h]

/-- Reading the public product modulo twelve identifies inputs with
exactly one prime supporting extra matches. -/
theorem mixed {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (bp : 864<p) (bq : 864<q)
    (res : (p*q)%12=5 ∨ (p*q)%12=7) :
    (IsSquare (3:ZMod p) ∧ ¬IsSquare (3:ZMod q)) ∨
      (IsSquare (3:ZMod q) ∧ ¬IsSquare (3:ZMod p)) := by
  have odd := (hp.out.odd_of_ne_two (by omega)).mul (hq.out.odd_of_ne_two (by omega))
  have public : jacobiSym 3 (p*q) = -1 := by
    rw [jacobiSym.mod_right 3 odd]
    change jacobiSym 3 ((p*q)%12) = -1
    rcases res with h|h <;> rw [h] <;> norm_num
  rw [jacobiSym.mul_right,←jacobiSym.legendreSym.to_jacobiSym,←jacobiSym.legendreSym.to_jacobiSym] at public
  have nz {r : ℕ} (hr : 864<r) : (3:ZMod r)≠0 := by
    exact_mod_cast (show ((3:ℕ):ZMod r)≠0 by
      rw [Ne,ZMod.natCast_zmod_eq_zero_iff_dvd]
      exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have ep := legendreSym.eq_one_iff (a:=(3:ℤ)) p (by simpa using nz bp)
  have eq := legendreSym.eq_one_iff (a:=(3:ℤ)) q (by simpa using nz bq)
  have np := legendreSym.eq_neg_one_iff (a:=(3:ℤ)) p
  have nq := legendreSym.eq_neg_one_iff (a:=(3:ℤ)) q
  push_cast at ep eq np nq
  rcases legendreSym.eq_one_or_neg_one p (by simpa using nz bp : ((3:ℤ):ZMod p)≠0) with a|a
  · rw [a,one_mul] at public
    exact .inl ⟨ep.mp a,nq.mp public⟩
  · rw [a,neg_one_mul] at public
    exact .inr ⟨eq.mp (by omega),np.mp a⟩

end PrimeFactors.ComplementaryKeys
