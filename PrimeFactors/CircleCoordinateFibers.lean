import PrimeFactors.SphereCircleIdentity

/-! How many modular circle points share their first coordinate. -/
namespace PrimeFactors.CircleCoordinateFibers

open Finset SphereCircleIdentity
open scoped BigOperators

section Ring
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

/-- Second coordinates over the given first coordinate at the supplied target. -/
noncomputable def fiber (t x : R) : Finset R := univ.filter fun y => x^2+y^2=t

@[simp] theorem mem_fiber {t x y : R} : y∈fiber t x ↔ x^2+y^2=t := by simp [fiber]

/-- First coordinates with a specified number of second coordinates. -/
noncomputable def level (R : Type*) [CommRing R] [Fintype R] [DecidableEq R] (t : R) (k : ℕ) :
    Finset R := univ.filter fun x => (fiber t x).card=k

@[simp] theorem mem_level {t x : R} {k : ℕ} : x∈level R t k ↔ (fiber t x).card=k := by simp [level]

theorem total (t : R) : (circle R t).card=∑ x : R,(fiber t x).card := by
  simp only [circle,fiber,card_filter,Fintype.sum_prod_type]

/-- Count actual circle points whose first coordinate has exactly k lifts. -/
theorem points_at_level (t : R) (k : ℕ) :
    ((circle R t).filter (fun w => (fiber t w.1).card=k)).card=k*(level R t k).card := by
  have each (x : R) : (∑ y : R,if x^2+y^2=t ∧ (fiber t x).card=k then 1 else 0) =
      k*(if (fiber t x).card=k then 1 else 0) := by
    by_cases eqn : (fiber t x).card=k
    · simp only [eqn,and_true,if_true,mul_one]
      simpa only [fiber,card_filter] using eqn
    · simp only [eqn,and_false,if_false,mul_zero,sum_const_zero]
  simp only [circle,filter_filter,card_filter,Fintype.sum_prod_type,Function.comp_apply,
    each,level,mul_sum]

/-- Ordered pairs of points with equal first coordinate, including repeated points. -/
noncomputable def collisions (R : Type*) [CommRing R] [Fintype R] [DecidableEq R] (t : R) : ℕ :=
  ∑ x : R, (fiber t x ×ˢ fiber t x).card
end Ring

section Field
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem lifts {t x y : F} (h : y∈fiber t x) : fiber t x={y,-y} := by
  ext z
  have root := mem_fiber.mp h
  simp only [mem_fiber,mem_insert,mem_singleton]
  rw [←sq_eq_sq_iff_eq_or_eq_neg]
  exact ⟨fun hz => by linear_combination hz-root,fun hz => by linear_combination hz+root⟩

omit [Fintype F] [DecidableEq F] in
private theorem diff (odd : (2:F)≠0) {y : F} (nz : y≠0) : y≠-y := by
  intro h
  apply (mul_ne_zero odd nz)
  linear_combination h

theorem at_most_two (t x : F) : (fiber t x).card≤2 := by
  by_cases h : (fiber t x).Nonempty
  · obtain ⟨y,hy⟩ := h
    rw [lifts hy]
    exact card_le_two
  · simp only [not_nonempty_iff_eq_empty.mp h,card_empty,Nat.zero_le]

theorem one_iff (odd : (2:F)≠0) (t x : F) : (fiber t x).card=1 ↔ x^2=t := by
  constructor
  · intro one
    obtain ⟨y,hy⟩ := card_pos.mp (by omega : 0<(fiber t x).card)
    by_cases zero : y=0
    · simpa [zero] using mem_fiber.mp hy
    · rw [lifts hy,card_pair (diff odd zero)] at one
      omega
  · intro sq
    have zero : (0:F)∈fiber t x := by simp [sq]
    simp [lifts zero]

theorem local_counts (t : F) :
    (circle F t).card=(level F t 1).card+2*(level F t 2).card := by
  have bound (x : F) : (fiber t x).card=(if (fiber t x).card=1 then 1 else 0)+
      2*(if (fiber t x).card=2 then 1 else 0) := by
    have := at_most_two t x
    split_ifs <;> omega
  rw [total]
  calc
    _ = ∑ x : F, ((if (fiber t x).card=1 then 1 else 0)+2*(if (fiber t x).card=2 then 1 else 0)) :=
      sum_congr rfl fun x _ => bound x
    _ = (level F t 1).card+2*(level F t 2).card := by
      rw [sum_add_distrib,←mul_sum]; simp only [level,card_filter]

theorem zero_one (odd : (2:F)≠0) : (fiber (1:F) 0).card=2 := by
  have extEq : fiber (1:F) 0={1,-1} := by
    ext x
    simp only [mem_fiber,zero_pow (by decide : 2≠0),zero_add,sq_eq_one_iff,mem_insert,mem_singleton]
  rw [extEq,card_pair (diff odd one_ne_zero)]

theorem field_levels (F : Type*) [Field F] [Fintype F] [DecidableEq F] (odd : (2:F)≠0) :
    (level F 1 1).card=2 ∧ (circle F 1).card=2+2*(level F 1 2).card := by
  have one : level F 1 1={1,-1} := by ext x; simp only [mem_level,one_iff odd,sq_eq_one_iff,mem_insert,mem_singleton]
  have single : (level F 1 1).card=2 := by rw [one,card_pair (diff odd one_ne_zero)]
  exact ⟨single,by rw [local_counts,single]⟩

end Field

theorem fiber_crt {p q : ℕ} [NeZero p] [NeZero q] (cop : p.Coprime q) (t x : ZMod (p*q)) :
    (fiber t x).card=(fiber (ZMod.chineseRemainder cop t).1 (ZMod.chineseRemainder cop x).1).card*(fiber (ZMod.chineseRemainder cop t).2 (ZMod.chineseRemainder cop x).2).card := by
  let e := ZMod.chineseRemainder cop
  have eq : (fiber t x).map e.toEquiv.toEmbedding=fiber (e t).1 (e x).1 ×ˢ fiber (e t).2 (e x).2 := by
    ext v
    obtain ⟨y,rfl⟩ := e.toEquiv.surjective v
    simp only [mem_map_equiv,Equiv.symm_apply_apply,mem_product,mem_fiber]
    rw [←e.injective.eq_iff,map_add,map_pow,map_pow,Prod.ext_iff]
    rfl
  simpa only [card_map,card_product] using congrArg Finset.card eq

/-- If two lifts over the same x are neither equal nor global negatives,
the signs of their second coordinates agree at one prime and reverse at the other. -/
theorem mixed_signs {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) {t x y z : ZMod (p*q)} (hy : y∈fiber t x) (hz : z∈fiber t x)
    (ne : z≠y) (notNeg : z≠ -y) :
    let e := ZMod.chineseRemainder cop
    ((e z).1=(e y).1 ∧ (e z).2= -(e y).2) ∨ ((e z).1= -(e y).1 ∧ (e z).2=(e y).2) := by
  dsimp only
  let e := ZMod.chineseRemainder cop
  have sqs : z^2=y^2 := add_left_cancel ((mem_fiber.mp hz).trans (mem_fiber.mp hy).symm)
  have prod := congrArg e sqs
  rw [map_pow,map_pow,Prod.ext_iff] at prod
  have signsP := sq_eq_sq_iff_eq_or_eq_neg.mp (show (e z).1^2=(e y).1^2 from prod.1)
  have signsQ := sq_eq_sq_iff_eq_or_eq_neg.mp (show (e z).2^2=(e y).2^2 from prod.2)
  have failP : ¬ ((e z).1=(e y).1 ∧ (e z).2=(e y).2) := fun h => ne (e.injective (Prod.ext h.1 h.2))
  have failN : ¬ ((e z).1= -(e y).1 ∧ (e z).2= -(e y).2) := by
    rintro ⟨a,b⟩
    apply notNeg (e.injective ?_)
    rw [map_neg]
    exact Prod.ext a b
  change ((e z).1=(e y).1 ∧ (e z).2= -(e y).2) ∨ ((e z).1= -(e y).1 ∧ (e z).2=(e y).2)
  tauto

/-- For a semiprime, the one-, two- and four-lift coordinate counts are
determined by the two local histograms at the given target. -/
theorem histogram {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q) (t : ZMod (p*q)) :
    let e := ZMod.chineseRemainder cop
    let a (i : ℕ) := (level (ZMod p) (e t).1 i).card
    let b (i : ℕ) := (level (ZMod q) (e t).2 i).card
    (level (ZMod (p*q)) t 1).card=a 1*b 1 ∧
    (level (ZMod (p*q)) t 2).card=a 1*b 2+a 2*b 1 ∧
    (level (ZMod (p*q)) t 4).card=a 2*b 2 := by
  dsimp only
  let e := ZMod.chineseRemainder cop
  let A (i : ℕ) := level (ZMod p) (e t).1 i
  let B (i : ℕ) := level (ZMod q) (e t).2 i
  have image (k : ℕ) (V : Finset (ZMod p×ZMod q))
      (cond : ∀ w : ZMod p×ZMod q,
        (fiber (e t).1 w.1).card*(fiber (e t).2 w.2).card=k ↔ w∈V) :
      (level (ZMod (p*q)) t k).card=V.card := by
    have eq : (level (ZMod (p*q)) t k).map e.toEquiv.toEmbedding=V := by
      ext w
      obtain ⟨x,rfl⟩ := e.toEquiv.surjective w
      simp only [mem_map_equiv,Equiv.symm_apply_apply,mem_level]
      rw [fiber_crt cop]
      exact cond (e x)
    simpa only [card_map] using congrArg Finset.card eq
  have factors {i j : ℕ} (il : i≤2) (jl : j≤2) :
      (i*j=1 ↔ i=1 ∧ j=1) ∧
      (i*j=2 ↔ i=1 ∧ j=2 ∨ i=2 ∧ j=1) ∧
      (i*j=4 ↔ i=2 ∧ j=2) := by interval_cases i <;> interval_cases j <;> decide
  have localCases (w : ZMod p×ZMod q) := factors (at_most_two (e t).1 w.1) (at_most_two (e t).2 w.2)
  have one := image 1 (A 1 ×ˢ B 1) (fun w => by simpa only [A,B,mem_product,mem_level] using (localCases w).1)
  have two := image 2 ((A 1 ×ˢ B 2) ∪ (A 2 ×ˢ B 1)) (fun w => by
    simpa only [A,B,mem_union,mem_product,mem_level] using (localCases w).2.1)
  have four := image 4 (A 2 ×ˢ B 2) (fun w => by simpa only [A,B,mem_product,mem_level] using (localCases w).2.2)
  have dis : Disjoint (A 1 ×ˢ B 2) (A 2 ×ˢ B 1) := by
    apply disjoint_left.mpr
    intro w hw hw'
    have x := mem_level.mp (mem_product.mp hw).1
    have x' := mem_level.mp (mem_product.mp hw').1
    omega
  rw [card_union_of_disjoint dis,card_product,card_product] at two
  exact ⟨one.trans (card_product ..),two,four.trans (card_product ..)⟩

/-- Counts in the three nonempty types for the norm-one circle.
A four-lift first coordinate allows independent choices of the sign
of the second coordinate at each prime. -/
theorem norm_one_histogram {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (op : p≠2) (oq : q≠2) :
    let C := fun (r : ℕ) [NeZero r] => (circle (ZMod r) 1).card
    (level (ZMod (p*q)) 1 1).card=4 ∧
    (level (ZMod (p*q)) 1 2).card + 4 = C p+C q ∧
    4*(level (ZMod (p*q)) 1 4).card=(C p-2)*(C q-2) := by
  dsimp only
  have hp := field_levels (ZMod p) (Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n]))
  have hq := field_levels (ZMod q) (Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n]))
  obtain ⟨h1,h2,h4⟩ := histogram cop (1:ZMod (p*q))
  simp only [map_one,Prod.fst_one,Prod.snd_one,hp.1,hq.1] at h1 h2 h4
  rw [h1,h2,h4,hp.2,hq.2]
  simp only [Nat.add_sub_cancel_left]
  exact ⟨by decide,by ring,by ring⟩


/-- Count first-coordinate collisions using independent components at both moduli. -/
theorem collisions_crt {p q : ℕ} [NeZero p] [NeZero q] (cop : p.Coprime q) (t : ZMod (p*q)) :
    collisions (ZMod (p*q)) t=collisions (ZMod p) (ZMod.chineseRemainder cop t).1*
      collisions (ZMod q) (ZMod.chineseRemainder cop t).2 := by
  let e := ZMod.chineseRemainder cop
  let f (x : ZMod p) := (fiber (e t).1 x).card ^ 2
  let g (x : ZMod q) := (fiber (e t).2 x).card ^ 2
  have equate : (∑ x : ZMod (p*q), (fiber t x).card^2) =
      ∑ w : ZMod p×ZMod q, f w.1*g w.2 := by
    apply Fintype.sum_equiv e.toEquiv
    intro x
    rw [fiber_crt cop,mul_pow]; rfl
  rw [Fintype.sum_prod_type] at equate
  simp_rw [←mul_sum] at equate
  rw [←sum_mul] at equate
  simpa only [collisions,card_product,←sq,f,g] using equate

private theorem field_collisions {F : Type*} [Field F] [Fintype F] [DecidableEq F] (t : F) :
    collisions F t=(level F t 1).card+4*(level F t 2).card := by
  have each (x : F) : (fiber t x).card*(fiber t x).card =
      (if (fiber t x).card=1 then 1 else 0)+4*(if (fiber t x).card=2 then 1 else 0) := by
    generalize eqn : (fiber t x).card=n
    have le : n≤2 := eqn ▸ at_most_two t x
    interval_cases n <;> decide
  simp only [collisions,card_product,each,sum_add_distrib,←mul_sum,level,card_filter]

theorem norm_one_collisions {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (op : p≠2) (oq : q≠2) :
    collisions (ZMod (p*q)) 1 =
    (2*(circle (ZMod p) 1).card-2)*(2*(circle (ZMod q) 1).card-2) := by
  have field (r : ℕ) [Fact r.Prime] (odd : r≠2) :
      collisions (ZMod r) 1=2*(circle (ZMod r) 1).card-2 := by
    obtain ⟨one,two⟩ := field_levels (ZMod r) (Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n]))
    rw [field_collisions,one,two]; omega
  simp only [collisions_crt cop,map_one,Prod.fst_one,Prod.snd_one,field p op,field q oq]

/-- For the same first coordinate, discard both equality and global negation
of the second coordinate. Every remaining ordered pair has opposite local
sign choices at the two primes. -/
noncomputable def mixed (R : Type*) [CommRing R] [Fintype R] [DecidableEq R] (t : R) : ℕ :=
  ∑ x : R, ∑ y∈fiber t x, ((fiber t x) \ {y,-y}).card

private theorem subtract_signs {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (t x : R) (two : IsUnit (2:R)) :
    (∑ y∈fiber t x,((fiber t x) \ {y,-y}).card)+2*(fiber t x).card =
    (fiber t x).card^2+(if x^2=t then 1 else 0) := by
  let s := fiber t x
  have each (y : R) (hy : y∈s) : (s \ {y,-y}).card+2=s.card+(if y=0 then 1 else 0) := by
    have negy : -y∈s := by simpa only [s,mem_fiber,neg_sq] using hy
    have sub : {y,-y} ⊆ s := by
      intro z hz
      rcases mem_insert.mp hz with e|e
      · exact e ▸ hy
      · exact (mem_singleton.mp e) ▸ negy
    have h := card_sdiff_add_card_eq_card sub
    by_cases zero : y=0
    · simp only [zero,neg_zero,insert_eq_of_mem,mem_singleton_self,card_singleton,if_true] at h ⊢
      omega
    · have ne : y≠-y := fun e => zero (two.mul_left_cancel (b:=y) (c:=0) (by linear_combination e))
      rw [card_pair ne] at h
      simp only [if_neg zero,add_zero]; exact h
  have eq := sum_congr (s₁:=s) rfl each
  rw [sum_add_distrib,sum_add_distrib] at eq
  simp only [sum_const,nsmul_eq_mul] at eq
  have coord : (∑ y∈s,if y=0 then 1 else 0)=(if x^2=t then 1 else 0) := by
    by_cases h : x^2=t <;> simp [s,h]
  rw [coord] at eq
  simpa only [s,Nat.cast_id,Nat.mul_comm 2,sq] using eq

/-- Two global choices coincide precisely at a zero second coordinate. -/
theorem mixed_identity {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (t : R) (two : IsUnit (2:R)) :
    mixed R t+2*(circle R t).card=collisions R t+(fiber t 0).card := by
  have eq := sum_congr (s₁:=univ) rfl (fun x _ => subtract_signs t x two)
  rw [sum_add_distrib,sum_add_distrib,←mul_sum] at eq
  have zeros : (fiber t 0).card=∑ x : R, if x^2=t then 1 else 0 := by
    simp only [fiber,card_filter,zero_pow (by decide : 2≠0),zero_add]
  simpa only [mixed,total,collisions,card_product,←sq,zeros] using eq

theorem norm_one_mixed {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (op : p≠2) (oq : q≠2) :
    mixed (ZMod (p*q)) 1=2*((circle (ZMod p) 1).card-2)*((circle (ZMod q) 1).card-2) := by
  have cp := ((Fact.out : p.Prime).odd_of_ne_two op).coprime_two_left
  have cq := ((Fact.out : q.Prime).odd_of_ne_two oq).coprime_two_left
  have two : IsUnit (2:ZMod (p*q)) := (ZMod.isUnit_iff_coprime 2 _).mpr (cp.mul_right cq)
  have zer (r : ℕ) [Fact r.Prime] (odd : r≠2) : (fiber (1:ZMod r) 0).card=2 :=
    zero_one (Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n]))
  have id := mixed_identity (1:ZMod (p*q)) two
  rw [norm_one_collisions cop op oq,SphereCircleIdentity.circle_crt cop,fiber_crt cop] at id
  simp only [map_one,map_zero,Prod.fst_one,Prod.snd_one,Prod.fst_zero,Prod.snd_zero,zer p op,zer q oq] at id
  have pc := (field_levels (ZMod p) (Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n]))).2
  have qc := (field_levels (ZMod q) (Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n]))).2
  rw [pc,qc] at id ⊢
  simp only [Nat.add_sub_cancel_left,Nat.mul_add] at id ⊢
  have simplify (m : ℕ) : 2*2+2*(2*m)-2=2+4*m := by omega
  rw [simplify,simplify] at id
  nlinarith only [id]

/-- The circles modulo 3 and 5 each have four points. Over 15, four x
coordinates have one lift, four have two, and zero is the unique x with four. -/
theorem fifteen :
    (level (ZMod 15) 1 1).card=4 ∧ (level (ZMod 15) 1 2).card=4 ∧
    (level (ZMod 15) 1 4).card=1 ∧ collisions (ZMod 15) 1=36 ∧ mixed (ZMod 15) 1=8 ∧
    (0:ZMod 15)∈level (ZMod 15) 1 4 ∧ (1:ZMod 15)∈fiber 1 0 ∧
      (4:ZMod 15)∈fiber 1 0 ∧ (4:ZMod 15)≠1 ∧ (4:ZMod 15)≠ -1 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have p3 := prime_unit (p:=3) (by decide) 1 one_ne_zero
  have p5 := prime_unit (p:=5) (by decide) 1 one_ne_zero
  norm_num [ThreeSquareRadiusCounts.sign] at p3 p5
  have cop : Nat.Coprime 3 5 := by decide
  obtain ⟨h1,h2,h4⟩ := norm_one_histogram cop (by decide) (by decide)
  have c := norm_one_collisions cop (by decide) (by decide)
  have m := norm_one_mixed cop (by decide) (by decide)
  have cp : (circle (ZMod 3) 1).card=4 := by exact_mod_cast p3
  have cq : (circle (ZMod 5) 1).card=4 := by exact_mod_cast p5
  dsimp only at h2 h4
  simp only [cp,cq] at h2 h4 c m
  have at_zero : (fiber (1:ZMod 15) 0).card=4 := by
    change (fiber (1:ZMod (3*5)) 0).card=4
    rw [fiber_crt cop,map_one,map_zero]
    have z (r : ℕ) [Fact r.Prime] (odd : r≠2) : (fiber (1:ZMod r) 0).card=2 :=
      zero_one (Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n]))
    change (fiber (1:ZMod 3) 0).card*(fiber (1:ZMod 5) 0).card=4
    rw [z 3 (by decide),z 5 (by decide)]
  change 4*(level (ZMod (3*5)) 1 4).card=4*1 at h4
  exact ⟨h1,Nat.add_right_cancel h2,Nat.eq_of_mul_eq_mul_left (by decide : 0<4) h4,c,m,
    mem_level.mpr at_zero,mem_fiber.mpr (by decide),mem_fiber.mpr (by decide),by decide,by decide⟩

end PrimeFactors.CircleCoordinateFibers
