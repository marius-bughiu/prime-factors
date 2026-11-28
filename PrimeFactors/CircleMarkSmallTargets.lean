import PrimeFactors.CircleMarkResultant
import Mathlib.Data.Rat.Lemmas

/-! A signed nonzero remainder smaller than both prime factors is a unit.
This gives an initial interval with no marks, and a size obstruction for
lag windows using a target and its square multiple. -/
namespace PrimeFactors.CircleMarkSmallTargets

open Finset CircleBranchCount CircleMarkCrossTargets CircleMarkResultant
open private PrimeFactors.CircleMarkAutocorrelation.abs_coprime from PrimeFactors.CircleMarkAutocorrelation

/-- A Jacobi-negative integer is not even a rational square. In particular
clearing a nonzero denominator cannot turn the target into a square. -/
theorem nonzero_component {n : ℕ} {a h s : ℤ} (neg : jacobiSym a n= -1)
    (active : h≠0 ∨ s≠0) : h^2-a*s^2≠0 := by
  intro zero
  by_cases sn : s=0
  · have h0 : h≠0 := active.resolve_right (by simpa using sn)
    simp [sn,h0] at zero
  · have snQ : (s:ℚ)≠0 := by exact_mod_cast sn
    have eqQ : (h:ℚ)^2=(a:ℚ)*(s:ℚ)^2 := by exact_mod_cast sub_eq_zero.mp zero
    have square : IsSquare (a:ℚ) := (isSquare_iff_exists_sq _).mpr
      ⟨(h:ℚ)/s,by rw [div_pow,eqQ,mul_div_cancel_right₀ _ (pow_ne_zero 2 snQ)]⟩
    obtain ⟨z,hz⟩ := Rat.isSquare_intCast_iff.mp square
    rw [hz,jacobiSym.mul_left] at neg
    nlinarith [sq_nonneg (jacobiSym z n)]

private theorem small_coprime {p q P u : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (pl : P≤p) (ql : P≤q) (pos : 0<u) (small : u<P) : (p*q).Coprime u := by
  apply Nat.coprime_mul_iff_left.mpr
  exact ⟨hp.out.coprime_iff_not_dvd.mpr (fun dv => not_lt_of_ge (Nat.le_of_dvd pos dv) (small.trans_le pl)),
    hq.out.coprime_iff_not_dvd.mpr (fun dv => not_lt_of_ge (Nat.le_of_dvd pos dv) (small.trans_le ql))⟩

private theorem abs_sub_bound {u v : ℤ} {P : ℕ} (u0 : 0≤u) (v0 : 0≤v)
    (ul : u<(P:ℤ)) (vl : v<(P:ℤ)) : (u-v).natAbs<P := by
  rw [←Nat.cast_lt (α:=ℤ),Int.natCast_natAbs,abs_lt]
  omega

/-- Exact sufficient condition on an integer coordinate, including a negative
representative of the same cyclic ring. -/
theorem raw {p q P : ℕ} [Fact p.Prime] [Fact q.Prime] {a x : ℤ}
    (neg : jacobiSym a (p*q)= -1) (pl : P≤p) (ql : P≤q)
    (size : (x^2-a).natAbs<P) : (x:ZMod (p*q))∉marked (p*q) a := by
  have nz : x^2-a≠0 := by
    simpa using nonzero_component (s:=1) (h:=x) neg (Or.inr one_ne_zero)
  have cop := small_coprime pl ql (Int.natAbs_pos.mpr nz) size
  have unit := (PrimeFactors.CircleMarkAutocorrelation.abs_coprime (p*q) (x^2-a)).mpr cop
  simp only [marked,mem_filter,mem_univ,true_and,not_not]
  convert unit.neg using 1
  push_cast
  ring

/-- For a nonnegative target smaller than the factor floor, all coordinates
from zero through the specified inclusive square root can be skipped. -/
theorem initial {p q P a x : ℕ} [Fact p.Prime] [Fact q.Prime]
    (neg : jacobiSym a (p*q)= -1) (pl : P≤p) (ql : P≤q) (small : a<P)
    (inside : x≤(a+P-1).sqrt) : (x:ZMod (p*q))∉marked (p*q) a := by
  have square := Nat.le_sqrt'.mp inside
  have top : x^2<a+P := by omega
  have broad : (((x:ℤ)^2)-a).natAbs<P := by
    rw [←Nat.cast_lt (α:=ℤ),Int.natCast_natAbs,abs_lt]
    have lt : (x:ℤ)^2<(a:ℤ)+P := by exact_mod_cast top
    have bot : (a:ℤ)<P := by exact_mod_cast small
    constructor <;> linarith [sq_nonneg (x:ℤ)]
  simpa only [Int.cast_natCast] using raw neg pl ql broad

/-- Both factors strictly below U guarantee a factor floor computable from
the public product and U. -/
theorem public_floor {p q U : ℕ} (pp : 0<p) (qp : 0<q) (pu : p<U) (qu : q<U) :
    p*q/U+1≤p ∧ p*q/U+1≤q := by
  have up : 0<U := pp.trans pu
  constructor
  · exact (Nat.div_lt_iff_lt_mul up).mpr (Nat.mul_lt_mul_of_pos_left qu pp)
  · exact (Nat.div_lt_iff_lt_mul up).mpr (by rw [Nat.mul_comm q U]; exact Nat.mul_lt_mul_of_pos_right pu qp)

/-- The integer factors of the resultant may be tested separately. Their
product can exceed both primes. Only the multiplier and lag need be units. -/
theorem packed {p q P : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q)
    (op : p≠2) (oq : q≠2) {a d h : ℤ} (neg : jacobiSym a (p*q)= -1)
    (pl : P≤p) (ql : P≤q) (hu : h.natAbs.Coprime (p*q)) (du : d.natAbs.Coprime (p*q))
    (nonzero : h≠0) (left : (h^2-a*(d-1)^2).natAbs<P) (right : (h^2-a*(d+1)^2).natAbs<P) :
    commonGcd (p*q) a (a*d^2) h=1 ∧ cross (p*q) a (a*d^2) h=0 := by
  have side (s : ℤ) (bound : (h^2-a*s^2).natAbs<P) : (p*q).Coprime (h^2-a*s^2).natAbs :=
    small_coprime pl ql (Int.natAbs_pos.mpr (nonzero_component neg (Or.inl nonzero))) bound
  have cop := (side (d-1) left).mul_right (side (d+1) right)
  have g := cop.gcd_eq_one
  rw [←Int.natAbs_mul] at g
  exact ⟨by simpa only [commonGcd,scaled_resultant] using g,
    by simpa only [g,if_true] using scaled diff op oq neg du hu⟩

set_option exponentiation.threshold 2048 in
/-- With a supplied Jacobi-negative target at most 2,015,165, a 1,024-bit
factor floor rules out this entire initial coordinate interval. This theorem
has no hypothesis about how the target was obtained. -/
theorem full_raw {p q a : ℕ} [Fact p.Prime] [Fact q.Prime]
    (pl : 2^1023≤p) (ql : 2^1023≤q) (neg : jacobiSym a (p*q)= -1)
    (cap : a≤2015165) {x : ℕ} (inside : x≤2^511) :
    (x:ZMod (p*q))∉marked (p*q) a := by
  apply initial neg pl ql (cap.trans_lt (by decide))
  apply Nat.le_sqrt'.mpr
  have pow := Nat.pow_le_pow_left inside 2
  have room : ((2:ℕ)^511)^2<2^1023 := by decide
  omega

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 2048 in
/-- At every positive lag through L, with the square multiplier (2L)²,
both discriminant components are too small for any mark intersection.
The given target bound is just a finite numerical hypothesis. -/
theorem full_packed {p q a L h : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (neg : jacobiSym a (p*q)= -1)
    (cap : a≤2015165) (length : L≤2^500) (positive : 0<h) (inside : h≤L) :
    let d : ℤ := 2*(L:ℤ)
    commonGcd (p*q) a (a*d^2) h=1 ∧ cross (p*q) a (a*d^2) h=0 := by
  dsimp only
  have up : (2:ℕ)^501<2^1023 := by decide
  have dmax : 2*L≤2^501 := by
    calc 2*L≤2*2^500 := Nat.mul_le_mul_left 2 length
         _ = _ := by decide
  have hsmall : h<2^1023 := by omega
  have dsmall : 2*L<2^1023 := dmax.trans_lt up
  have hu : (h:ℤ).natAbs.Coprime (p*q) := (small_coprime pl ql positive hsmall).symm
  have du : (2*(L:ℤ)).natAbs.Coprime (p*q) := by
    change (2*L).Coprime (p*q)
    exact
      (small_coprime pl ql (by omega : 0<2*L) dsmall).symm
  have hs : (h:ℤ)^2<((2^1023:ℕ):ℤ) := by
    have bound := Nat.pow_le_pow_left (inside.trans length) 2
    exact_mod_cast bound.trans_lt (by decide : ((2:ℕ)^500)^2<2^1023)
  have upper : 2*(L:ℤ)≤(2:ℤ)^501 := by exact_mod_cast dmax
  have bound (s : ℤ) (lo : 0≤s) (big : s≤(2:ℤ)^501+1) :
      ((h:ℤ)^2-(a:ℤ)*s^2).natAbs<2^1023 := by
    apply abs_sub_bound (sq_nonneg _) (by positivity) hs
    have c : (a:ℤ)≤2015165 := by exact_mod_cast cap
    calc (a:ℤ)*s^2≤2015165*((2:ℤ)^501+1)^2 :=
           mul_le_mul c (pow_le_pow_left₀ lo big 2) (sq_nonneg _) (by decide)
         _ < _ := by decide
  have op : p≠2 := by omega
  have oq : q≠2 := by omega
  have ll : 0<(L:ℤ) := by exact_mod_cast positive.trans_le inside
  exact packed diff op oq neg pl ql hu du (by exact_mod_cast positive.ne')
    (bound _ (by linarith) (by linarith)) (bound _ (by linarith) (by linarith))

/-- The strict bound is attained at the first coordinate beyond the skip:
3²−2=7. At the same lag, scaling the target by four gives resultant gcd 7. -/
theorem seventy_seven_boundary :
    (∀ x : ℕ, x≤2 → (x:ZMod 77)∉marked 77 2) ∧
    (3:ZMod 77)∈marked 77 2 ∧ (3:ℤ)^2-2=7 ∧ commonGcd 77 2 8 3=7 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have neg : jacobiSym (2:ℤ) (7*11)= -1 := by norm_num
  refine ⟨fun x inside => initial (a:=2) neg (le_refl 7) (by decide) (by decide)
    (inside.trans (by decide)),?_,by decide,CircleMarkResultant.seventy_seven.2.2.1⟩
  exact (proper_gcd (by decide : (7:ℕ)≠11) neg (3:ZMod (7*11))).mpr (by decide)

end PrimeFactors.CircleMarkSmallTargets
