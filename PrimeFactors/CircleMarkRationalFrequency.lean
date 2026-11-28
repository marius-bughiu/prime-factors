import PrimeFactors.CircleMarkPackedMenu

/-! Coverage of squared rational coordinates among uniformly chosen negative-Jacobi
targets at one fixed semiprime. In a sufficiently small rectangle, all collisions
of squared slopes come from ordinary equality of positive reduced fractions. -/
namespace PrimeFactors.CircleMarkRationalFrequency

open Finset CircleMarkTargetFrequency
open private PrimeFactors.SumGuessIncidence.half_inj from PrimeFactors.SumGuessIncidence
open private PrimeFactors.CircleMarkPackedMenu.clear_test from PrimeFactors.CircleMarkPackedMenu
open private PrimeFactors.CircleMarkAutocorrelation.abs_coprime from PrimeFactors.CircleMarkAutocorrelation

noncomputable def rectangle (H D : ℕ) : Finset (ℕ × ℕ) := Icc 1 H ×ˢ Icc 1 D

/-- One integer pair for each distinct positive rational number in the rectangle. -/
noncomputable def primitive (H D : ℕ) : Finset (ℕ × ℕ) :=
  (rectangle H D).filter fun z => z.1.Coprime z.2

private theorem in_rect {H D : ℕ} {z : ℕ × ℕ} : z∈rectangle H D ↔
    (0<z.1 ∧ z.1≤H) ∧ (0<z.2 ∧ z.2≤D) := by simp only [rectangle,mem_product,mem_Icc]; rfl

private noncomputable def point (n : ℕ) (z : ℕ × ℕ) : ZMod n :=
  (z.1 : ZMod n) * (z.2 : ZMod n)⁻¹

/-- Evaluate each public quotient modulo the product and keep its standard representative. -/
noncomputable def menu (n H D : ℕ) : Finset ℕ :=
  (rectangle H D).image fun z => (point n z).val

private theorem denom {p H D : ℕ} [hp : Fact p.Prime] {z : ℕ × ℕ} (mem : z∈rectangle H D)
    (large : 2*(H*D)<p) : z.2.Coprime p := by
  obtain ⟨⟨nl,nh⟩,⟨dl,dh⟩⟩ := in_rect.mp mem
  have cap := Nat.le_mul_of_pos_left D (nl.trans_le nh)
  exact (hp.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt dl (by omega))).symm

private theorem clear_point {n : ℕ} (z : ℕ×ℕ) (cop : z.2.Coprime n) :
    point n z * (z.2 : ZMod n) = z.1 := by
  rw [point,mul_assoc,ZMod.inv_mul_of_unit _ ((ZMod.isUnit_iff_coprime ..).mpr cop),mul_one]

private theorem local_point {n p : ℕ} [NeZero n] [Fact p.Prime] (dv : p∣n)
    (z : ℕ×ℕ) (cop : z.2.Coprime n) :
    ((point n z).val : ZMod p)=point p z := by
  let f := ZMod.castHom dv (ZMod p)
  have eqn := congrArg f (clear_point z cop)
  have val := congrArg f (ZMod.natCast_zmod_val (point n z))
  simp only [map_natCast,map_mul] at eqn val
  have unit := (ZMod.isUnit_iff_coprime z.2 p).mpr (cop.of_dvd_right dv)
  exact mul_right_cancel₀ (isUnit_iff_ne_zero.mp unit)
    (by rw [val,eqn,clear_point z (cop.of_dvd_right dv)])

private theorem fraction_eq {p : ℕ} [Fact p.Prime] {z w : ℕ×ℕ}
    (zc : z.2.Coprime p) (wc : w.2.Coprime p) (same : z.1*w.2=w.1*z.2) :
    point p z=point p w := by
  apply mul_right_cancel₀ (b:=((z.2:ZMod p)*w.2))
    (mul_ne_zero (isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime ..).mpr zc))
      (isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime ..).mpr wc)))
  calc
    point p z * _ = (z.1:ZMod p)*w.2 := by rw [←mul_assoc,clear_point z zc]
    _ = (w.1:ZMod p)*z.2 := by exact_mod_cast congrArg (fun k : ℕ => (k:ZMod p)) same
    _ = point p w * _ := by rw [mul_comm (z.2:ZMod p),←mul_assoc,clear_point w wc]

private theorem normalize {H D : ℕ} {z : ℕ×ℕ} (mem : z∈rectangle H D) :
    ∃ w∈primitive H D, z.1*w.2=w.1*z.2 := by
  obtain ⟨⟨np,nh⟩,⟨dp,dh⟩⟩ := in_rect.mp mem
  let g := z.1.gcd z.2
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ np
  have dn : g∣z.1 := Nat.gcd_dvd_left ..
  have dd : g∣z.2 := Nat.gcd_dvd_right ..
  have nrep := Nat.div_mul_cancel dn
  have drep := Nat.div_mul_cancel dd
  refine ⟨(z.1/g,z.2/g),mem_filter.mpr ⟨in_rect.mpr
    ⟨⟨Nat.div_pos (Nat.le_of_dvd np dn) gp,(Nat.div_le_self ..).trans nh⟩,
     ⟨Nat.div_pos (Nat.le_of_dvd dp dd) gp,(Nat.div_le_self ..).trans dh⟩⟩,
    Nat.coprime_div_gcd_div_gcd gp⟩,?_⟩
  change z.1*(z.2/g)=(z.1/g)*z.2
  calc z.1*(z.2/g) = (z.1/g*g)*(z.2/g) := by rw [nrep]
       _ = (z.1/g)*(z.2/g*g) := by ring
       _ = _ := by rw [drep]

private theorem reduced_unique {z w : ℕ×ℕ} (zc : z.1.Coprime z.2) (wc : w.1.Coprime w.2)
    (pos : 0<z.1) (eqn : z.1*w.2=w.1*z.2) : z=w := by
  have left := zc.dvd_of_dvd_mul_right (eqn ▸ dvd_mul_right z.1 w.2)
  have right := wc.dvd_of_dvd_mul_right (eqn.symm ▸ dvd_mul_right w.1 z.2)
  have same := Nat.dvd_antisymm left right
  exact Prod.ext same (Nat.mul_left_cancel pos (by rw [←same] at eqn; exact eqn.symm))

private theorem half_cross {p H D : ℕ} [Fact p.Prime] (large : 2*(H*D)<p) {a b : ℕ}
    (ah : a≤H) (bh : b≤D) :
    ((a*b : ℕ) : ZMod p) ∈ SumGuessIncidence.halfPeriod p := by
  have limit := Nat.mul_le_mul ah bh
  apply mem_filter.mpr
  exact ⟨mem_univ _,by rw [ZMod.val_natCast_of_lt (by omega : a*b<p)]; omega⟩

private theorem square_injective {p H D : ℕ} [Fact p.Prime] (large : 2*(H*D)<p) :
    Set.InjOn (fun z => (point p z)^2) (primitive H D) := by
  intro z hz w hw eqn
  obtain ⟨zm,zc⟩ := mem_filter.mp hz
  obtain ⟨wm,wc⟩ := mem_filter.mp hw
  have zd := denom zm large
  have wd := denom wm large
  have halfZ := half_cross large (in_rect.mp zm).1.2 (in_rect.mp wm).2.2
  have halfW := half_cross large (in_rect.mp wm).1.2 (in_rect.mp zm).2.2
  have cross : ((z.1*w.2 : ℕ):ZMod p)^2=((w.1*z.2 : ℕ):ZMod p)^2 := by
    rw [Nat.cast_mul,Nat.cast_mul,←clear_point z zd,←clear_point w wd]
    simp only [mul_pow]
    linear_combination (z.2:ZMod p)^2*(w.2:ZMod p)^2*eqn
  have ordinary := congrArg ZMod.val (PrimeFactors.SumGuessIncidence.half_inj halfZ halfW cross)
  have capZ := Nat.mul_le_mul (in_rect.mp zm).1.2 (in_rect.mp wm).2.2
  have capW := Nat.mul_le_mul (in_rect.mp wm).1.2 (in_rect.mp zm).2.2
  rw [ZMod.val_natCast_of_lt (by omega : z.1*w.2<p),ZMod.val_natCast_of_lt (by omega : w.1*z.2<p)] at ordinary
  exact reduced_unique zc wc (in_rect.mp zm).1.1 ordinary

/-- Squaring the tested modular fractions identifies exactly the common multiples
of primitive numerator/denominator pairs once twice the area is below the prime. -/
theorem cover_count {n p H D : ℕ} [NeZero n] [Fact p.Prime] (dv : p∣n)
    (large : 2*(H*D)<p) (units : ∀ z∈rectangle H D, z.2.Coprime n) :
    (covered p (menu n H D)).card=(primitive H D).card := by
  let f := fun z => (point p z)^2
  have image : ((menu n H D).image fun x : ℕ => (x:ZMod p)^2)=(primitive H D).image f := by
    rw [menu,image_image]
    ext x
    constructor
    · intro mem
      obtain ⟨z,zm,eq⟩ := mem_image.mp mem
      obtain ⟨w,wm,same⟩ := normalize zm
      refine mem_image.mpr ⟨w,wm,?_⟩
      change (((point n z).val:ZMod p)^2)=x at eq
      rw [local_point dv z (units z zm),fraction_eq (denom zm large) (denom (mem_filter.mp wm).1 large) same] at eq
      exact eq
    · intro mem
      obtain ⟨z,zm,rfl⟩ := mem_image.mp mem
      refine mem_image.mpr ⟨z,(mem_filter.mp zm).1,?_⟩
      change (((point n z).val:ZMod p)^2)=(point p z)^2
      rw [local_point dv z (units z (mem_filter.mp zm).1)]
  have nz : (0:ZMod p)∉(primitive H D).image f := by
    intro h
    obtain ⟨z,zm,zero⟩ := mem_image.mp h
    have m := (mem_filter.mp zm).1
    have eqn : (point p z)=0 := sq_eq_zero_iff.mp zero
    have bad := clear_point z (denom m large)
    rw [eqn,zero_mul] at bad
    have ⟨⟨nl,nh⟩,⟨dl,dh⟩⟩ := in_rect.mp m
    have high := Nat.le_mul_of_pos_right H (dl.trans_le dh)
    have val := congrArg ZMod.val bad
    rw [ZMod.val_zero,ZMod.val_natCast_of_lt (by omega : z.1<p)] at val
    omega
  rw [covered,image,erase_eq_of_not_mem nz,card_image_of_injOn (square_injective large)]

theorem coverage {p q H D : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q)
    (op : p≠2) (oq : q≠2) (pl : 2*(H*D)<p) (ql : 2*(H*D)<q) :
    rate (p*q) (menu (p*q) H D)=
      ((primitive H D).card:ℚ)/(p-1)+((primitive H D).card:ℚ)/(q-1) := by
  have unit (z) (h : z∈rectangle H D) : z.2.Coprime (p*q) :=
    (denom h pl).mul_right (denom h ql)
  rw [rate_eq diff op oq,cover_count (dvd_mul_right p q) pl unit,cover_count (dvd_mul_left q p) ql unit]

/-- Every pair with both entries even duplicates a smaller fraction.
This supplies an explicit loss estimate, including at finite budgets. -/
theorem duplication_bound (H D : ℕ) :
    (primitive H D).card+(H/2)*(D/2)≤H*D := by
  let double := fun v : ℕ×ℕ => (2*v.1,2*v.2)
  have size (h d : ℕ) : (rectangle h d).card=h*d := by simp [rectangle,Nat.card_Icc]
  let evens := (rectangle (H/2) (D/2)).image double
  have ec : evens.card=(H/2)*(D/2) := by
    unfold evens
    rw [card_image_of_injective _ (show Function.Injective double by
      intro x y eq
      have hx := congrArg Prod.fst eq
      have hy := congrArg Prod.snd eq
      exact Prod.ext (by dsimp [double] at hx; omega) (by dsimp [double] at hy; omega)),size]
  have sub : primitive H D ∪ evens ⊆ rectangle H D := by
    intro z h
    rcases mem_union.mp h with a|b
    · exact (mem_filter.mp a).1
    · obtain ⟨v,vm,rfl⟩ := mem_image.mp b
      obtain ⟨⟨l,h⟩,⟨k,g⟩⟩ := in_rect.mp vm
      exact in_rect.mpr ⟨⟨by dsimp [double]; omega,by dsimp [double]; omega⟩,
        ⟨by dsimp [double]; omega,by dsimp [double]; omega⟩⟩
  have separate : Disjoint (primitive H D) evens := by
    apply disjoint_left.mpr
    intro z prim even
    obtain ⟨v,vm,rfl⟩ := mem_image.mp even
    have cp := (mem_filter.mp prim).2
    change Nat.gcd (2*v.1) (2*v.2)=1 at cp
    rw [Nat.gcd_mul_left] at cp
    omega
  simpa only [card_union_of_disjoint separate,ec,size] using card_le_card sub

private noncomputable def multiples (H D m : ℕ) : Finset (ℕ×ℕ) :=
  (rectangle (H/m) (D/m)).image fun v => (m*v.1,m*v.2)

private theorem mem_multiples {H D m : ℕ} {v : ℕ×ℕ} (mem : v∈rectangle H D) (pos : 0<m)
    (num : m∣v.1) (den : m∣v.2) : v∈multiples H D m := by
  obtain ⟨⟨a,b⟩,⟨c,d⟩⟩ := in_rect.mp mem
  exact mem_image.mpr ⟨(v.1/m,v.2/m),in_rect.mpr
    ⟨⟨Nat.div_pos (Nat.le_of_dvd a num) pos,Nat.div_le_div_right b⟩,
     ⟨Nat.div_pos (Nat.le_of_dvd c den) pos,Nat.div_le_div_right d⟩⟩,
    Prod.ext (Nat.mul_div_cancel' num) (Nat.mul_div_cancel' den)⟩

private theorem box_count (H D : ℕ) :
    H*D≤(primitive H D).card+(H/2)*(D/2)+∑ i∈range H, (H/(2*i+3))*(D/(2*i+3)) := by
  let oddBoxes := (range H).biUnion fun i => multiples H D (2*i+3)
  have sub : rectangle H D⊆(primitive H D ∪ multiples H D 2) ∪ oddBoxes := by
    intro v mem
    by_cases cp : v.1.Coprime v.2
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem,cp⟩))
    obtain ⟨r,pr,dv⟩ := Nat.exists_prime_and_dvd (show v.1.gcd v.2≠1 from cp)
    have n := dv.trans (Nat.gcd_dvd_left ..)
    have d := dv.trans (Nat.gcd_dvd_right ..)
    by_cases two : r=2
    · subst r
      exact mem_union_left _ (mem_union_right _ (mem_multiples mem (by decide) n d))
    have rle := (Nat.le_of_dvd (in_rect.mp mem).1.1 n).trans (in_rect.mp mem).1.2
    have parity := Nat.odd_iff.mp (pr.odd_of_ne_two two)
    have rp := pr.two_le
    have shape : 2*(r/2-1)+3=r := by omega
    apply mem_union_right
    refine mem_biUnion.mpr ⟨r/2-1,mem_range.mpr (by omega),?_⟩
    rw [shape]
    exact mem_multiples mem pr.pos n d
  have size (h d : ℕ) : (rectangle h d).card=h*d := by simp [rectangle,Nat.card_Icc]
  have bound (m : ℕ) : (multiples H D m).card≤(H/m)*(D/m) := card_image_le.trans_eq (size ..)
  calc H*D = (rectangle H D).card := (size ..).symm
       _ ≤ _ := card_le_card sub
       _ ≤ ((primitive H D).card+(multiples H D 2).card)+oddBoxes.card :=
         (card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _)
       _ ≤ _ := Nat.add_le_add (Nat.add_le_add_left (bound 2) _)
         (card_biUnion_le.trans (sum_le_sum fun i _ => bound _))

private theorem telescopes (L : ℕ) :
    (∑ i∈range L, (1:ℚ)/((i:ℚ)+1)/((i:ℚ)+2))=1-1/((L:ℚ)+1) := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    rw [sum_range_succ,ih,Nat.cast_succ]
    have one : (L:ℚ)+1≠0 := by positivity
    have two : (L:ℚ)+2≠0 := by positivity
    rw [show (L:ℚ)+1+1=L+2 by ring]
    field_simp
    ring

/-- More than half the positive grid cells are primitive. The finite bound
counts all even pairs and overcounts other losses by summing odd multiples. -/
theorem majority {H D : ℕ} (hp : 0<H) (dp : 0<D) : H*D<2*(primitive H D).card := by
  let A := (H:ℚ)*D
  have ap : 0<A := mul_pos (Nat.cast_pos.mpr hp) (Nat.cast_pos.mpr dp)
  have term (m : ℕ) : ((H/m:ℕ):ℚ)*((D/m:ℕ):ℚ)≤A/(m:ℚ)^2 := calc
    _ ≤ ((H:ℚ)/m)*((D:ℚ)/m) := mul_le_mul Nat.cast_div_le Nat.cast_div_le (by positivity) (by positivity)
    _ = _ := by simp only [A,sq,div_mul_div_comm]
  have even : ((H/2:ℕ):ℚ)*((D/2:ℕ):ℚ)≤A/4 := by simpa using term 2
  have odd (i : ℕ) : ((H/(2*i+3):ℕ):ℚ)*((D/(2*i+3):ℕ):ℚ)≤A/4*(1/((i:ℚ)+1)/((i:ℚ)+2)) := by
    apply (term _).trans
    push_cast
    have weights : 4*((i:ℚ)+1)*((i:ℚ)+2)≤(2*i+3)^2 := by nlinarith
    calc
      A/(2*(i:ℚ)+3)^2 ≤ A/(4*((i:ℚ)+1)*((i:ℚ)+2)) :=
        div_le_div_of_nonneg_left ap.le (by positivity) weights
      _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  have tail := sum_le_sum (s:=range H) (fun i _ => odd i)
  rw [←mul_sum,telescopes] at tail
  have bound : A≤((primitive H D).card:ℚ)+((H/2:ℕ):ℚ)*((D/2:ℕ):ℚ)+
      ∑ i∈range H,((H/(2*i+3):ℕ):ℚ)*((D/(2*i+3):ℕ):ℚ) := by dsimp only [A]; exact_mod_cast box_count H D
  have positive : 0<A/4*(1/((H:ℚ)+1)) := by positivity
  change H*D<2*(primitive H D).card
  have result : A<2*((primitive H D).card:ℚ) := by linarith
  dsimp only [A] at result
  exact_mod_cast result

/-- The small rectangle and a consecutive interval of F coordinates have
exactly the same coverage, with F the number of primitive pairs. -/
theorem equivalent_prefix {p q H D : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q)
    (op : p≠2) (oq : q≠2) (pl : 2*(H*D)<p) (ql : 2*(H*D)<q) :
    rate (p*q) (menu (p*q) H D)=rate (p*q) (Icc 1 (primitive H D).card) := by
  have loss := duplication_bound H D
  rw [coverage diff op oq pl ql,first_hit diff op oq,
    min_eq_left (by omega : (primitive H D).card≤(p-1)/2),
    min_eq_left (by omega : (primitive H D).card≤(q-1)/2)]

/-- With both sides at least two, spending one coordinate per grid cell on
the early consecutive interval strictly increases the uniform hit rate. -/
theorem strict_loss {p q H D : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (diff : p≠q)
    (op : p≠2) (oq : q≠2) (h : 2≤H) (d : 2≤D) (pl : 2*(H*D)<p) (ql : 2*(H*D)<q) :
    rate (p*q) (menu (p*q) H D)<rate (p*q) (Icc 1 (H*D)) := by
  have loss := duplication_bound H D
  have even : 0<(H/2)*(D/2) := Nat.mul_pos (by omega) (by omega)
  have cap : ((primitive H D).card:ℚ)<(H*D:ℕ) := by exact_mod_cast (show (primitive H D).card<H*D by omega)
  rw [coverage diff op oq pl ql,first_hit diff op oq,
    min_eq_left (by omega : H*D≤(p-1)/2),min_eq_left (by omega : H*D≤(q-1)/2)]
  apply add_lt_add <;> apply div_lt_div_of_pos_right cap
  · exact sub_pos.mpr (by exact_mod_cast hp.out.one_lt)
  · exact sub_pos.mpr (by exact_mod_cast hq.out.one_lt)

/-- At 11·13 the four rectangular cells represent just three slopes.
They hit 33 of 60 negative targets, against 44 for four consecutive positions. -/
theorem control :
    (primitive 2 2).card=3 ∧
    rate 143 (menu 143 2 2)=11/20 ∧ rate 143 (Icc 1 4)=11/15 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have card : (primitive 2 2).card=3 := by decide +kernel
  refine ⟨card,?_,?_⟩
  · change rate (11*13) (menu (11*13) 2 2)=_
    rw [coverage (by decide) (by decide) (by decide) (by decide) (by decide),card]
    norm_num
  · change rate (11*13) (Icc 1 4)=_
    rw [first_hit (by decide) (by decide) (by decide)]
    norm_num

/-- The probability calculation measures the gcd test on the original integers. -/
theorem gcd_hit {n H D : ℕ} [NeZero n] (units : ∀ z∈rectangle H D, z.2.Coprime n) (t : ZMod n) :
    t∈hits n (menu n H D) ↔ t∈targets n ∧ ∃ z∈rectangle H D,
      n.gcd (((z.1:ℤ)^2-(t.val:ℤ)*(z.2:ℤ)^2).natAbs)≠1 := by
  rw [hits,mem_filter]
  apply and_congr_right
  intro _
  have one (z) (mem : z∈rectangle H D) :
      point n z∈CircleBranchCount.marked n t.val ↔ n.gcd (((z.1:ℤ)^2-(t.val:ℤ)*(z.2:ℤ)^2).natAbs)≠1 := by
    have h := PrimeFactors.CircleMarkPackedMenu.clear_test (x:=point n z) (k:=(z.2:ZMod n)) (h:=(z.1:ZMod n)) t.val
      ((ZMod.isUnit_iff_coprime z.2 n).mpr (units z mem))
      (by simpa only [mul_comm] using clear_point z (units z mem))
    change _ ↔ ¬ n.Coprime (((z.1:ℤ)^2-(t.val:ℤ)*(z.2:ℤ)^2).natAbs)
    rw [←PrimeFactors.CircleMarkAutocorrelation.abs_coprime]
    simpa only [Int.cast_sub,Int.cast_pow,Int.cast_mul,Int.cast_natCast] using h
  constructor
  · rintro ⟨j,hj,hm⟩
    obtain ⟨z,zm,rfl⟩ := mem_image.mp hj
    rw [ZMod.natCast_zmod_val] at hm
    exact ⟨z,zm,(one z zm).mp hm⟩
  · rintro ⟨z,zm,hm⟩
    exact ⟨_,mem_image.mpr ⟨z,zm,rfl⟩,by rw [ZMod.natCast_zmod_val]; exact (one z zm).mpr hm⟩

end PrimeFactors.CircleMarkRationalFrequency
