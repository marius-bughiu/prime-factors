import PrimeFactors.CircleMarkTargetFrequency
import PrimeFactors.CircleMarkResultant

/-! Two coordinates per lag for a square-related pair of targets. All rate
statements use the uniform distribution on Jacobi-negative target residues. -/

namespace PrimeFactors.CircleMarkPackedMenu

open Finset CircleMarkTargetFrequency
open private PrimeFactors.SumGuessIncidence.half_inj from PrimeFactors.SumGuessIncidence
open private PrimeFactors.CircleMarkAutocorrelation.abs_coprime from PrimeFactors.CircleMarkAutocorrelation
open scoped Classical

private def arm (L k : ℕ) : Finset ℕ := (Icc 1 L).image (fun h => k*h)

/-- Numerators of h/(2L+1) and h/(2L−1) over the common denominator
(2L−1)(2L+1), for h ranging from one through J. -/
noncomputable def numerators (L J : ℕ) : Finset ℕ := arm J (2*L-1) ∪ arm J (2*L+1)

private theorem coprime_arms {L : ℕ} (pos : 0<L) : (2*L-1).Coprime (2*L+1) := by
  have odd : Odd (2*L-1) := ⟨L-1,by omega⟩
  rw [show 2*L+1=(2*L-1)+2 by omega,Nat.coprime_self_add_right]
  exact Nat.coprime_two_right.mpr odd

theorem numerator_count {L J : ℕ} (pos : 0<L) (limit : J≤L) : (numerators L J).card=2*J := by
  have sep : Disjoint (arm J (2*L-1)) (arm J (2*L+1)) := by
    apply disjoint_left.mpr
    intro z hl hr
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hl
    obtain ⟨b,_,eq⟩ := mem_image.mp hr
    have dvd := (coprime_arms pos).symm.dvd_of_dvd_mul_left ⟨b,eq.symm⟩
    have size := Nat.le_of_dvd (mem_Icc.mp ha).1 dvd
    have := (mem_Icc.mp ha).2
    omega
  have card {k : ℕ} (p : 0<k) : (arm J k).card=J := by
    rw [arm,card_image_of_injective _ (fun _ _ eq => Nat.mul_left_cancel p eq),Nat.card_Icc]
    omega
  rw [numerators,card_union_of_disjoint sep,card (by omega),card (by omega)]
  omega

private theorem numerator_range {L J a : ℕ} (pos : 0<L) (limit : J≤L) (h : a∈numerators L J) :
    0<a ∧ a≤(2*L+1)*L := by
  have arm_bound {k : ℕ} (lo : 0<k) (hi : k≤2*L+1) (mem : a∈arm J k) :
      0<a ∧ a≤(2*L+1)*L := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp mem
    exact ⟨Nat.mul_pos lo (mem_Icc.mp hx).1,Nat.mul_le_mul hi ((mem_Icc.mp hx).2.trans limit)⟩
  rcases mem_union.mp h with left|right
  · exact arm_bound (by omega) (by omega) left
  · exact arm_bound (by omega) le_rfl right

/-- All 2J integer numerators have distinct nonzero squares at a prime
larger than twice the largest numerator. -/
theorem numerator_cover {p L J : ℕ} [Fact p.Prime] (pos : 0<L) (limit : J≤L) (large : 2*(2*L+1)*L<p) :
    (covered p (numerators L J)).card=2*J := by
  let f (x : ℕ) := (x:ZMod p)^2
  have val {x : ℕ} (h : x∈numerators L J) : (x:ZMod p).val=x :=
    ZMod.val_natCast_of_lt (by have := (numerator_range pos limit h).2; rw [mul_assoc] at large; omega)
  have half {x : ℕ} (h : x∈numerators L J) : (x:ZMod p)∈SumGuessIncidence.halfPeriod p := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rw [val h]
    have := (numerator_range pos limit h).2
    rw [mul_assoc] at large
    omega
  have inj : Set.InjOn f (numerators L J) := by
    intro a ha b hb eq
    have same := PrimeFactors.SumGuessIncidence.half_inj (half ha) (half hb) eq
    simpa only [val ha,val hb] using congrArg ZMod.val same
  have nz : (0:ZMod p)∉(numerators L J).image f := by
    intro h
    obtain ⟨x,hx,z⟩ := mem_image.mp h
    have zero := congrArg ZMod.val (sq_eq_zero_iff.mp z : (x:ZMod p)=0)
    rw [val hx,ZMod.val_zero] at zero
    exact (numerator_range pos limit hx).1.ne' zero
  rw [covered,erase_eq_of_not_mem nz,card_image_of_injOn inj,numerator_count pos limit]

/-- Reduce the coordinates after multiplying each by the specified public unit. -/
noncomputable def scale (n : ℕ) (u : (ZMod n)ˣ) (C : Finset ℕ) : Finset ℕ :=
  C.image fun x : ℕ => ((u : ZMod n)*(x:ZMod n)).val

private theorem scaled_cover {n p : ℕ} [NeZero n] [Fact p.Prime] (dvd : p∣n) (u : (ZMod n)ˣ) (C : Finset ℕ) :
    (covered p (scale n u C)).card=(covered p C).card := by
  let f := ZMod.castHom dvd (ZMod p)
  let k := (f (u:ZMod n))^2
  have nz : k≠0 := pow_ne_zero _ (isUnit_iff_ne_zero.mp (u.isUnit.map f))
  have inj : Function.Injective (fun x : ZMod p => k*x) := mul_right_injective₀ nz
  have coord (x : ℕ) : ((((u:ZMod n)*(x:ZMod n)).val : ℕ) : ZMod p)^2=k*(x:ZMod p)^2 := by
    have id := congrArg f (ZMod.natCast_zmod_val ((u:ZMod n)*(x:ZMod n)))
    simp only [map_natCast,map_mul] at id
    rw [id,mul_pow]
  have eq : covered p (scale n u C)=(covered p C).image (fun x => k*x) := by
    rw [covered,covered,scale,image_erase inj]
    simp only [image_image,Function.comp_def,mul_zero,coord]
  rw [eq,card_image_of_injective _ inj]

/-- The common denominator is publicly invertible under the same size condition. -/
theorem denominator_coprime {p q L : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (pos : 0<L) (pl : 2*(2*L+1)*L<p) (ql : 2*(2*L+1)*L<q) :
    ((2*L-1)*(2*L+1)).Coprime (p*q) := by
  have good {r : ℕ} (rp : r.Prime) (size : 2*(2*L+1)*L<r) :
      ((2*L-1)*(2*L+1)).Coprime r := by
    have big : 2*L+1<r := by
      have le := Nat.le_mul_of_pos_right (2*(2*L+1)) pos
      omega
    apply Nat.Coprime.symm
    apply rp.coprime_iff_not_dvd.mpr
    intro dv
    rcases rp.dvd_mul.mp dv with u|v
    · have := Nat.le_of_dvd (by omega : 0<2*L-1) u
      omega
    · have := Nat.le_of_dvd (by omega : 0<2*L+1) v
      omega
  exact (good hp.out pl).mul_right (good hq.out ql)

/-- The actual modular quotient coordinates, represented by natural numbers
below the product. The supplied proof of coprimality can be checked by gcd. -/
noncomputable def menu (n L J : ℕ) (unit : ((2*L-1)*(2*L+1)).Coprime n) : Finset ℕ :=
  scale n (ZMod.unitOfCoprime _ unit)⁻¹ (numerators L J)

theorem menu_cover {n p L J : ℕ} [NeZero n] [Fact p.Prime] (dvd : p∣n) (pos : 0<L) (limit : J≤L)
    (large : 2*(2*L+1)*L<p) (unit : ((2*L-1)*(2*L+1)).Coprime n) :
    (covered p (menu n L J unit)).card=2*J := by
  rw [menu,scaled_cover dvd,numerator_cover pos limit large]

/-- Each lag supplies two tests. Their success probability equals that of
the optimal ordinary menu of 2J coordinates and twice that of J coordinates,
for every prefix J≤L with the multiplier 2L held fixed. -/
theorem coverage {p q L J : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (pos : 0<L) (limit : J≤L)
    (pl : 2*(2*L+1)*L<p) (ql : 2*(2*L+1)*L<q) :
    let C := menu (p*q) L J (denominator_coprime pos pl ql)
    rate (p*q) C=rate (p*q) (Icc 1 (2*J)) ∧
    rate (p*q) C=2*rate (p*q) (Icc 1 J) := by
  have enough {r : ℕ} (h : 2*(2*L+1)*L<r) : r≠2 ∧ 2*J≤(r-1)/2 := by
    have base := Nat.le_mul_of_pos_right (2*(2*L+1)) pos
    omega
  obtain ⟨op,hp⟩ := enough pl
  obtain ⟨oq,hq⟩ := enough ql
  let C := menu (p*q) L J (denominator_coprime pos pl ql)
  have direct := rate_eq diff op oq C
  rw [menu_cover (dvd_mul_right p q) pos limit pl,menu_cover (dvd_mul_left q p) pos limit ql] at direct
  change rate (p*q) C=_ ∧ rate (p*q) C=_
  rw [direct,first_hit diff op oq,first_hit diff op oq,min_eq_left hp,min_eq_left hq,
    min_eq_left (by omega : J≤(p-1)/2),min_eq_left (by omega : J≤(q-1)/2)]
  push_cast
  constructor <;> ring

private theorem clear_test {n : ℕ} [NeZero n] (a : ℤ) {x k h : ZMod n}
    (unit : IsUnit k) (den : k*x=h) :
    x∈CircleBranchCount.marked n a ↔ ¬IsUnit (h^2-(a:ZMod n)*k^2) := by
  have eq : h^2-(a:ZMod n)*k^2 = -((a:ZMod n)-x^2)*k^2 := by rw [←den]; ring
  simp only [CircleBranchCount.marked,mem_filter,mem_univ,true_and,eq,IsUnit.mul_iff,
    IsUnit.neg_iff,unit.pow,and_true]

/-- Over the actual, unscaled target, each lag's single resultant gcd detects
exactly the union of its two coordinate tests. -/
theorem gcd_hit {n L J : ℕ} [NeZero n] (pos : 0<L) (unit : ((2*L-1)*(2*L+1)).Coprime n)
    (t : ZMod n) :
    t∈hits n (menu n L J unit) ↔ t∈targets n ∧ ∃ h∈Icc 1 J,
      CircleMarkResultant.commonGcd n t.val (t.val*(2*(L:ℤ))^2) h ≠ 1 := by
  let m := 2*L-1
  let s := 2*L+1
  let u := ZMod.unitOfCoprime (m*s) unit
  let v : ZMod n := ↑u⁻¹
  let point (k h : ℕ) : ZMod n := v*(k*h : ℕ)
  have inv : (m:ZMod n)*s*v=1 := by
    rw [←Nat.cast_mul]
    change (↑(m*s) : ZMod n)*(↑u⁻¹ : ZMod n)=1
    rw [show (↑(m*s) : ZMod n)=(u:ZMod n) from (ZMod.coe_unitOfCoprime (m*s) unit).symm]
    exact Units.mul_inv u
  have ku : IsUnit (m:ZMod n) ∧ IsUnit (s:ZMod n) := by
    apply IsUnit.mul_iff.mp
    rw [←Nat.cast_mul]
    exact (ZMod.isUnit_iff_coprime _ _).mpr unit
  have left (h : ℕ) : (m:ZMod n)*point s h=h := by
    calc _ = ((m:ZMod n)*s*v)*h := by simp only [point,Nat.cast_mul]; ring
         _ = _ := by rw [inv,one_mul]
  have right (h : ℕ) : (s:ZMod n)*point m h=h := by
    calc _ = ((m:ZMod n)*s*v)*h := by simp only [point,Nat.cast_mul]; ring
         _ = _ := by rw [inv,one_mul]
  have one (h : ℕ) : CircleMarkResultant.commonGcd n t.val (t.val*(2*(L:ℤ))^2) h ≠ 1 ↔
      point s h∈CircleBranchCount.marked n t.val ∨ point m h∈CircleBranchCount.marked n t.val := by
    rw [clear_test _ ku.1 (left h),clear_test _ ku.2 (right h),CircleMarkResultant.commonGcd,
      CircleMarkResultant.scaled_resultant]
    change ¬n.Coprime _ ↔ _
    rw [←PrimeFactors.CircleMarkAutocorrelation.abs_coprime]
    simp only [Int.cast_mul,Int.cast_sub,Int.cast_add,Int.cast_pow,Int.cast_one,Int.cast_ofNat,
      Int.cast_natCast,IsUnit.mul_iff]
    have l : (m:ZMod n) = 2*(L:ZMod n)-1 := by
      dsimp [m]
      rw [Nat.cast_sub (by omega : 1≤2*L)]
      push_cast
      rfl
    have r : (s:ZMod n) = 2*(L:ZMod n)+1 := by simp [s]
    rw [l,r]
    tauto
  have mem (z : ℕ) : z∈menu n L J unit ↔
      (∃ h∈Icc 1 J, (point m h).val=z) ∨ (∃ h∈Icc 1 J, (point s h).val=z) := by
    simp only [menu,scale,numerators,arm,image_union,image_image,mem_union,mem_image,
      Function.comp_apply,point,v,u,m,s]
  rw [hits,mem_filter]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨z,hz,hit⟩
    rcases (mem z).mp hz with ⟨h,hh,rfl⟩|⟨h,hh,rfl⟩
    · exact ⟨h,hh,(one h).mpr (Or.inr (by simpa only [ZMod.natCast_zmod_val] using hit))⟩
    · exact ⟨h,hh,(one h).mpr (Or.inl (by simpa only [ZMod.natCast_zmod_val] using hit))⟩
  · rintro ⟨h,hh,hit⟩
    rcases (one h).mp hit with l|r
    · exact ⟨_,(mem _).mpr (Or.inr ⟨h,hh,rfl⟩),by simpa only [ZMod.natCast_zmod_val] using l⟩
    · exact ⟨_,(mem _).mpr (Or.inl ⟨h,hh,rfl⟩),by simpa only [ZMod.natCast_zmod_val] using r⟩

/-- Exhaustive target counts on 23 times 29: 2 lags cover 100 of the 308
negative-Jacobi targets, exactly matching the four consecutive coordinate tests. -/
theorem controls :
    let C := menu 667 2 2 (by decide)
    (targets 667).card=308 ∧ (hits 667 C).card=100 ∧
    rate 667 C=25/77 ∧ rate 667 (Icc 1 4)=25/77 ∧ rate 667 (Icc 1 2)=25/154 := by
  letI : Fact (Nat.Prime 23) := ⟨by decide⟩
  letI : Fact (Nat.Prime 29) := ⟨by decide⟩
  let C := menu (23*29) 2 2 (by decide)
  have ⟨t,h⟩ := counts (p:=23) (q:=29) (by decide) (by decide) (by decide) C
  rw [menu_cover (p:=23) (dvd_mul_right 23 29) (by decide) (by decide) (by decide),
    menu_cover (p:=29) (dvd_mul_left 29 23) (by decide) (by decide) (by decide)] at h
  have cmp := coverage (p:=23) (q:=29) (L:=2) (J:=2) (by decide) (by decide) (by decide) (by decide) (by decide)
  change rate (23*29) C=_ ∧ rate (23*29) C=_ at cmp
  have frac : rate (23*29) C=25/77 := by rw [rate,t,h]; norm_num
  exact ⟨t,h,frac,cmp.1.symm.trans frac,by linarith only [cmp.2,frac]⟩

/-- At 7 times 11 the same two-lag menu has repeated local squares. It hits
only 24 of the 30 targets, whereas four consecutive coordinates hit 27. -/
theorem small_control :
    let C := menu 77 2 2 (by decide)
    (targets 77).card=30 ∧ (hits 77 C).card=24 ∧ (hits 77 (Icc 1 4)).card=27 ∧
    rate 77 C=4/5 ∧ rate 77 (Icc 1 4)=9/10 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  let C := menu (7*11) 2 2 (by decide)
  have local_size {p : ℕ} [Fact p.Prime] (dvd : p∣7*11) :
      (covered p C).card=(covered p (numerators 2 2)).card :=
    scaled_cover dvd _ _
  have ⟨t,h⟩ := counts (p:=7) (q:=11) (by decide) (by decide) (by decide) C
  rw [local_size (dvd_mul_right 7 11),local_size (dvd_mul_left 11 7)] at h
  rw [show (covered 7 (numerators 2 2)).card=3 by decide,
    show (covered 11 (numerators 2 2)).card=3 by decide] at h
  have raw := (counts (p:=7) (q:=11) (by decide) (by decide) (by decide) (Icc 1 4)).2
  rw [prefix_cover (p:=7) (by decide),prefix_cover (p:=11) (by decide)] at raw
  refine ⟨t,h,raw,?_,?_⟩
  · change rate (7*11) C=4/5
    rw [rate,t,h]; norm_num
  · change rate (7*11) (Icc 1 4)=9/10
    rw [rate,t,raw]; norm_num

end PrimeFactors.CircleMarkPackedMenu
