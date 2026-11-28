import PrimeFactors.CircleMarkRationalCover
import Mathlib.FieldTheory.Finite.Basic

/-! At the last rectangle before universal coverage, exactly one nonzero
square value is missed. The first two power sums identify that value. -/
namespace PrimeFactors.CircleMarkRationalOneHole

open Finset CircleMarkRationalCover

private def center {R : Type*} [CommRing R] (B x : ℕ) : R := 2*x-B

private theorem powers (R : Type*) [CommRing R] (B : ℕ) :
    2*(∑ x ∈ range (B+1), (x:R)) = (B:R)*(B+1) ∧
    6*(∑ x ∈ range (B+1), (x:R)^2) = (B:R)*(B+1)*(2*B+1) := by
  induction B with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ (fun x : ℕ => (x:R)) (n+1),sum_range_succ (fun x : ℕ => (x:R)^2) (n+1)]
    push_cast
    constructor
    · linear_combination ih.1
    · linear_combination ih.2

private theorem centered (R : Type*) [CommRing R] (B : ℕ) :
    (∑ x ∈ range (B+1), center B x : R) = 0 ∧
    3*(∑ x ∈ range (B+1), (center B x:R)^2) = (B:R)*(B+1)*(B+2) := by
  have ⟨one,two⟩ := powers R B
  constructor
  · simp only [center,sum_sub_distrib,←mul_sum,sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    linear_combination one
  · have expand (x : ℕ) : (center B x:R)^2=4*(x:R)^2-(4*B:R)*x+(B:R)^2 := by unfold center; ring
    simp only [expand,sum_add_distrib,sum_sub_distrib,←mul_sum,sum_const,card_range,nsmul_eq_mul,
      Nat.cast_add,Nat.cast_one]
    linear_combination 2*two-6*(B:R)*one

private abbrev box (H D : ℕ) := range (H+1) ×ˢ range (D+1)

private def point {p : ℕ} (r : ZMod p) (H D : ℕ) (v : ℕ×ℕ) : ZMod p :=
  center H v.1 + r*center D v.2

private theorem moments {p : ℕ} (r : ZMod p) (H D : ℕ) :
    (∑ v∈box H D,point r H D v)=0 ∧
    3*(∑ v∈box H D,(point r H D v)^2)=
      ((H:ZMod p)+1)*(D+1)*(H*(H+2)+r^2*D*(D+2)) := by
  have h := centered (ZMod p) H
  have d := centered (ZMod p) D
  have first (u : ZMod p) :
      (∑ j∈range (D+1),(u+r*center D j)) = ((D:ZMod p)+1)*u := by
    simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,←mul_sum,d.1,
      Nat.cast_add,Nat.cast_one,mul_zero,add_zero]
  have second (u : ZMod p) :
      (∑ j∈range (D+1),(u+r*center D j)^2) =
        ((D:ZMod p)+1)*u^2 + r^2*(∑ j∈range (D+1),(center D j:ZMod p)^2) := by
    have expand (j : ℕ) : (u+r*center D j)^2 = u^2+(2*u*r)*center D j+r^2*(center D j)^2 := by ring
    simp only [expand,sum_add_distrib,sum_const,card_range,nsmul_eq_mul,←mul_sum,d.1,
      Nat.cast_add,Nat.cast_one,mul_zero,add_zero]
  constructor
  · simp only [box,sum_product,point,first,←mul_sum,h.1,mul_zero]
  · simp only [box,sum_product,point,second,sum_add_distrib,←mul_sum,sum_const,card_range,
      nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    linear_combination ((D:ZMod p)+1)*h.2 + ((H:ZMod p)+1)*r^2*d.2

private theorem delta {p B x y : ℕ} (xb : x≤B) (yb : y≤B) (ne : x≠y) :
    ∃ k∈Icc 1 B, (k:ZMod p)=x-y ∨ (k:ZMod p)= -(x-y) := by
  rcases lt_or_gt_of_ne ne with lt|gt
  · exact ⟨y-x,mem_Icc.mpr ⟨by omega,by omega⟩,Or.inr (by rw [Nat.cast_sub lt.le]; ring)⟩
  · exact ⟨x-y,mem_Icc.mpr ⟨by omega,by omega⟩,Or.inl (Nat.cast_sub gt.le)⟩

private theorem injective {p H D : ℕ} [Fact p.Prime] (large : 3<p) (hs : H<p) (ds : D<p)
    {r : ZMod p} (nz : r≠0) (miss : ¬Represents r H D) : Set.InjOn (point r H D) (box H D) := by
  rintro ⟨i,j⟩ v ⟨k,l⟩ w eqn
  obtain ⟨hi,hj⟩ := mem_product.mp v
  obtain ⟨hk,hl⟩ := mem_product.mp w
  simp only [mem_range] at hi hj hk hl
  have two : (2:ZMod p)≠0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
  have relation : (i:ZMod p)-k = r*((l:ZMod p)-j) := by
    apply mul_left_cancel₀ two
    unfold point center at eqn
    linear_combination eqn
  have same {x y : ℕ} (xp : x<p) (yp : y<p) (h : (x:ZMod p)=(y:ZMod p)) : x=y := by
    have h' := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt xp,ZMod.val_natCast_of_lt yp] using h'
  by_cases js : j=l
  · rw [js,sub_self,mul_zero] at relation
    exact Prod.ext (same (by omega) (by omega) (sub_eq_zero.mp relation)) js
  have is : i≠k := by
    intro eq
    rw [eq,sub_self,eq_comm,mul_eq_zero] at relation
    exact js (same (by omega) (by omega) (sub_eq_zero.mp (relation.resolve_left nz)).symm)
  obtain ⟨x,hx,xx⟩ := delta (p:=p) (show i≤H by omega) (show k≤H by omega) is
  obtain ⟨y,hy,yy⟩ := delta (p:=p) (show l≤D by omega) (show j≤D by omega) (Ne.symm js)
  apply False.elim (miss ⟨x,hx,y,hy,?_⟩)
  rcases xx with xx|xx <;> rcases yy with yy|yy <;> rw [xx,yy,relation] <;> ring_nf <;> simp

private theorem square_moment {p H D : ℕ} [Fact p.Prime] (large : 3<p) (hs : H<p) (ds : D<p)
    (size : (H+1)*(D+1)+1=p) {r : ZMod p} (nz : r≠0) (miss : ¬Represents r H D) :
    H*(H+2)+r^2*D*(D+2)=0 := by
  let S := (box H D).image (point r H D)
  have inj := injective large hs ds nz miss
  have card : S.card=(H+1)*(D+1) := by simp only [S,card_image_of_injOn inj,box,card_product,card_range]
  have cc : Sᶜ.card=1 := by rw [card_compl,ZMod.card,card]; omega
  obtain ⟨m,hm⟩ := card_eq_one.mp cc
  have eqSum (f : ZMod p→ZMod p) : (∑ x∈box H D,f (point r H D x))+f m=∑ z : ZMod p,f z := by
    have h := sum_add_sum_compl S f
    rw [hm,sum_singleton] at h
    simp only [S,sum_image inj] at h
    exact h
  have all1 : (∑ z : ZMod p,z)=0 := by
    simpa only [pow_one] using FiniteField.sum_pow_lt_card_sub_one (ZMod p) 1 (by rw [ZMod.card]; omega)
  have all2 := FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 (by rw [ZMod.card]; omega)
  have mom := moments r H D
  have m0 : m=0 := by simpa only [id_eq,mom.1,zero_add,all1] using eqSum id
  have sum0 : (∑ x∈box H D,(point r H D x)^2)=0 := by
    have e := eqSum (fun z => z^2)
    rw [m0,zero_pow (by decide : 2≠0),add_zero,all2] at e
    exact e
  have prod := congrArg (fun z : ℕ => (z:ZMod p)) size
  push_cast at prod
  rw [ZMod.natCast_self] at prod
  rw [sum0,mul_zero] at mom
  have minus : ((H:ZMod p)+1)*(D+1)= -1 := by linear_combination prod
  have last := mom.2
  rw [minus,neg_one_mul] at last
  exact neg_eq_zero.mp last.symm

/-- When the rectangular grid has p−1 endpoint pairs, its only missed nonzero
roots are H+1 and its negative. -/
theorem miss_iff {p H D : ℕ} [Fact p.Prime] (large : 3<p) (hp : 0<H) (dp : 0<D)
    (size : (H+1)*(D+1)+1=p) {r : ZMod p} (nz : r≠0) :
    ¬Represents r H D ↔ r=(H+1:ℕ) ∨ r= -((H+1:ℕ):ZMod p) := by
  have hs : H+2<p := by nlinarith only [size,Nat.le_mul_of_pos_right (H+1) dp]
  have ds : D<p := by nlinarith only [size,Nat.zero_le (H*D)]
  constructor
  · intro miss
    have eq := square_moment large (by omega) ds size nz miss
    have prod := congrArg (fun z : ℕ => (z:ZMod p)) size
    push_cast at prod
    rw [ZMod.natCast_self] at prod
    have rel : ((H:ZMod p)+1)*(D+1)= -1 := by linear_combination prod
    have m2 := congrArg (·^2) rel
    have nonzero {k : ℕ} (kp : 0<k) (ks : k<p) : (k:ZMod p)≠0 := fun h =>
      Nat.not_dvd_of_pos_of_lt kp ks ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h)
    have h2 : (H:ZMod p)+2≠0 := by exact_mod_cast nonzero (k:=H+2) (by omega) hs
    have zero : (H:ZMod p)*(H+2)*(((H:ZMod p)+1)^2-r^2)=0 := by
      linear_combination ((H:ZMod p)+1)^2*eq-r^2*m2
    have sol := sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left (mul_ne_zero (nonzero hp (by omega)) h2))
    simpa only [Nat.cast_add,Nat.cast_one] using sq_eq_sq_iff_eq_or_eq_neg.mp sol.symm
  · have base := (missed (p:=p) dp (by omega : (H+1)*(D+1)≤p)).2
    rintro (rfl|rfl)
    · exact base
    · simpa only [Represents,mul_neg,neg_neg,or_comm] using base

/-- Among the nonzero square targets at p, the only missed residue is
the square of H+1. -/
theorem square_miss_iff {p H D : ℕ} [Fact p.Prime] (large : 3<p) (hp : 0<H) (dp : 0<D)
    (size : (H+1)*(D+1)+1=p) {a : ℤ} (square : legendreSym p a=1) :
    ¬SquareHit p a H D ↔ (a:ZMod p)=((H+1:ℕ):ZMod p)^2 := by
  have nz : (a:ZMod p)≠0 := by
    intro h
    rw [legendreSym,h,quadraticChar_zero] at square
    contradiction
  obtain ⟨r,eq⟩ := (isSquare_iff_exists_sq _).mp ((legendreSym.eq_one_iff p nz).mp square)
  have rn : r≠0 := fun z => nz (by simp [eq,z])
  rw [square_iff eq.symm H D,miss_iff large hp dp size rn,eq,sq_eq_sq_iff_eq_or_eq_neg]

/-- The 3-by-2 rectangle at 13 misses the negative-Jacobi target 3 at 65.
The target 12 has the same two character signs and is covered. -/
theorem sixty_five :
    jacobiSym 3 65= -1 ∧ jacobiSym 12 65= -1 ∧
    ¬SquareHit 13 3 3 2 ∧ SquareHit 13 12 3 2 := by
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · apply (square_miss_iff (p:=13) (H:=3) (D:=2) (by decide) (by decide) (by decide)
      (by decide) (by norm_num : legendreSym 13 3=1)).mpr
    decide
  · exact ⟨3,by decide,2,by decide,by decide⟩

end PrimeFactors.CircleMarkRationalOneHole
