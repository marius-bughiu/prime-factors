import PrimeFactors.JacobiMomentPeriod
import PrimeFactors.FrobeniusFixedCounts
import Mathlib.GroupTheory.Index
import PrimeFactors.PartialOrderLift

/-!
# Exact periods after striding the complete even Jacobi moments

Sampling at degrees 2s, 4s, … groups the signed weights by their s-th powers.
When the fibers have odd size, only the fiber containing 4 can vanish. An
image of size at least three contains two distinct inverse generators, so
one of them forces the entire image order to survive in the scalar period.
-/

namespace PrimeFactors.JacobiScalarStride
open Finset JacobiMomentRecurrence

private theorem power_fiber_size {G : Type*} [CommGroup G] [Fintype G] [IsCyclic G]
    [DecidableEq G] (s : ℕ) (y : (powMonoidHom (α:=G) s).range) :
    (univ.filter fun z:G => z^s=y.val).card = s.gcd (Fintype.card G) := by
  let f : G →* G := powMonoidHom s
  have h := MonoidHom.card_fiber_eq_of_mem_range f y.property (show (1:G)∈f.range from ⟨1,f.map_one⟩)
  exact h.trans (FrobeniusFixedCounts.cyclic_count G s)

private theorem power_range_size {G : Type*} [CommGroup G] [Fintype G] [IsCyclic G]
    [DecidableEq G] (s : ℕ) :
    Fintype.card (powMonoidHom (α:=G) s).range = Fintype.card G / s.gcd (Fintype.card G) := by
  let f : G →* G := powMonoidHom s
  have h : Fintype.card G = ∑ y : f.range, (univ.filter fun x:G => f.rangeRestrict x=y).card := by
    simpa using card_eq_sum_card_fiberwise (s := (univ : Finset G)) (t := (univ : Finset f.range))
      (f := f.rangeRestrict) (by simp)
  have same (y:f.range) : (univ.filter fun x:G => f.rangeRestrict x=y).card = s.gcd (Fintype.card G) := by
    convert power_fiber_size s y using 2
    ext x
    simp [Subtype.ext_iff]; rfl
  simp only [same,sum_const,card_univ,nsmul_eq_mul] at h
  exact Nat.eq_div_of_mul_eq_right (Nat.gcd_pos_of_pos_right _ Fintype.card_pos).ne' (by
    change s.gcd (Fintype.card G) * Fintype.card f.range = Fintype.card G
    rw [Nat.mul_comm]; exact h.symm)

/-- An odd number of signs, fewer than the characteristic, has nonzero field sum. -/
private theorem odd_signs {p : ℕ} [Fact p.Prime] {I : Type*} (S : Finset I)
    (w : I → ℤ) (signs : ∀ i∈S, w i=1 ∨ w i= -1) (odd : Odd S.card) (small : S.card < p) :
    ((∑ i∈S,w i : ℤ) : ZMod p) ≠ 0 := by
  classical
  let nneg := (S.filter (fun i => w i= -1)).card
  have count : (∑ i∈S, w i) = (S.card:ℤ)-2*nneg := by
    have wt (i) (hi:i∈S) : w i = 1 - 2*(if w i= -1 then (1:ℤ) else 0) := by
      rcases signs i hi with h | h <;> simp [h]
    simp_rw [sum_congr rfl wt,Finset.sum_sub_distrib,←Finset.mul_sum]
    simp [nneg]
  have negLe : nneg ≤ S.card := card_filter_le ..
  obtain ⟨t,ht⟩ := odd
  intro zero
  have dv := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp zero
  have pp : (0:ℤ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have m := Int.eq_zero_of_abs_lt_dvd dv (by rw [count]; exact abs_lt.mpr ⟨by omega,by omega⟩)
  omega

/-- An embedded cyclic group's exponential sum determines every spectral weight. -/
private theorem frequency_zero {G F : Type*} [Fintype G] [Field F]
    (embed : G → F) (inj : Function.Injective embed) (w : G → F)
    (h : ∀ k:ℕ, ∑ z:G, w z*(embed z)^k=0) : ∀ z, w z=0 := by
  classical
  let e : G ≃ Fin (Fintype.card G) := Fintype.equivFin G
  have sum (i : Fin (Fintype.card G)) : ∑ j : Fin (Fintype.card G), w (e.symm j)*(embed (e.symm j))^(i:ℕ)=0 := by
    exact (Equiv.sum_comp e.symm _).trans (h i)
  have zero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (inj.comp e.symm.injective) sum
  intro z
  simpa using congrFun zero (e z)

/-- Exact period of a decimated Fourier sum with odd fibers and one allowed zero
weight. The character must have a sign away from that point. -/
theorem odd_fiber_period {p : ℕ} [Fact p.Prime] {G : Type*}
    [CommGroup G] [Fintype G] [IsCyclic G] [DecidableEq G]
    (embed : G →* ZMod p) (inj : Function.Injective embed) (w : G → ℤ)
    (exception : G) (signs : ∀ x, x≠exception → w x=1 ∨ w x= -1)
    (s t : ℕ) (odd : Odd (s.gcd (Fintype.card G))) (small : s.gcd (Fintype.card G)<p)
    (large : 3≤Fintype.card G / s.gcd (Fintype.card G)) :
    Function.Periodic (fun k:ℕ => ∑ x:G, (w x:ZMod p)*(embed (x^s))^(k+1)) t ↔
      Fintype.card G / s.gcd (Fintype.card G) ∣ t := by
  classical
  let f : G →* G := powMonoidHom s
  let H := f.range
  let v (y:H) : ZMod p := embed y.val
  let weights (y:H) : ZMod p := ∑ x ∈ (univ.filter fun x:G => f.rangeRestrict x=y), (w x : ZMod p)
  have size : Fintype.card H = _ := power_range_size (G:=G) s
  have vi : Function.Injective v := inj.comp Subtype.val_injective
  have vn (y:H) : v y ≠ 0 := (show IsUnit (v y) from (Group.isUnit y.val).map embed).ne_zero
  have rep (k:ℕ) : (∑ x:G, (w x:ZMod p)*(embed (x^s))^(k+1)) =
      ∑ y:H, (weights y*v y)*(v y)^k := by
    rw [←sum_fiberwise (univ:Finset G) f.rangeRestrict (fun x => (w x:ZMod p)*(embed (x^s))^(k+1))]
    apply sum_congr rfl
    intro y _
    simp only [weights,Finset.sum_mul]
    apply sum_congr rfl
    intro x hx
    have e := congrArg Subtype.val (mem_filter.mp hx).2
    change x^s=y.val at e
    rw [e,pow_succ]
    dsimp [v]; ring
  have good (y:H) (other : y≠f.rangeRestrict exception) : weights y ≠ 0 := by
    let S := (univ.filter fun x:G => f.rangeRestrict x=y)
    have count : S.card = s.gcd (Fintype.card G) := by
      convert power_fiber_size s y using 2
      ext x
      simp [S,Subtype.ext_iff]; rfl
    have h := odd_signs (p:=p) S w (fun x hx => signs x (fun eqn => other (eqn ▸ (mem_filter.mp hx).2).symm))
      (count ▸ odd) (count ▸ small)
    simpa [weights,S] using h
  constructor
  · intro periodic
    have h (k:ℕ) : ∑ y:H, ((weights y*v y)*(v y^t-1))*v y^k=0 := by
      have eqn := periodic k
      dsimp only at eqn
      rw [rep,rep] at eqn
      rw [←sub_eq_zero] at eqn
      rw [←Finset.sum_sub_distrib] at eqn
      convert eqn using 1
      apply sum_congr rfl
      intro y _
      rw [pow_add]; ring
    have roots := frequency_zero v vi _ h
    have works (y:H) (other : y≠f.rangeRestrict exception) : y^t=1 := by
      apply Subtype.ext
      apply inj
      have eqn := (mul_eq_zero.mp (roots y)).resolve_left (mul_ne_zero (good y other) (vn y))
      simpa [v] using sub_eq_zero.mp eqn
    obtain ⟨y,gen⟩ := IsCyclic.exists_generator (α:=H)
    have full : orderOf y=Fintype.card H := (orderOf_eq_card_of_forall_mem_zpowers gen).trans Nat.card_eq_fintype_card
    have ydiff : y≠y⁻¹ := by
      intro hi
      have square : y^2=1 := by calc
        y^2 = y*y⁻¹ := by nth_rw 1 [←hi]; rw [pow_two]
        _ = 1 := mul_inv_cancel y
      have d := (orderOf_dvd_iff_pow_eq_one.mpr square)
      have := Nat.le_of_dvd (by decide : 0<2) d
      omega
    rw [←size,←full]
    apply orderOf_dvd_iff_pow_eq_one.mpr
    by_cases ey : y=f.rangeRestrict exception
    · have hp := works y⁻¹ (fun h => ydiff (ey.trans h.symm))
      simpa only [inv_pow,inv_eq_one] using hp
    · exact works y ey
  · intro divides k
    dsimp only
    rw [rep,rep]
    apply sum_congr rfl
    intro y _
    have d : orderOf y ∣ t := orderOf_dvd_card.trans (size ▸ divides)
    have hy := congrArg (fun z:H => embed z.val) (orderOf_dvd_iff_pow_eq_one.mp d)
    change embed _ = _ at hy
    have ht : v y^t=1 := by simpa [v] using hy
    rw [pow_add,ht,mul_one]
private abbrev SquareUnits (p : ℕ) [Fact p.Prime] :=
  (powMonoidHom (α := (ZMod p)ˣ) 2).range

private def squareValue {p : ℕ} [Fact p.Prime] : SquareUnits p →* ZMod p :=
  (Units.coeHom _).comp (SquareUnits p).subtype

private theorem square_inj {p : ℕ} [Fact p.Prime] :
    Function.Injective (squareValue (p := p)) :=
  fun _ _ h => Subtype.ext (Units.ext h)

private theorem square_card {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    Fintype.card (SquareUnits p) = (p-1)/2 := by
  classical
  rw [power_range_size, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
  have ⟨j, hj⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  have divides : 2 ∣ p-1 := ⟨j, by omega⟩
  rw [Nat.gcd_eq_left divides]

private theorem square_signal {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (n : ℕ) :
    component p (2*(n+1)) =
      2*∑ z : SquareUnits p, weight (squareValue z) * (squareValue z)^(n+1) := by
  classical
  let S : Finset (ZMod p) := univ.image (squareValue (p:=p))
  have subset : evenBases p ⊆ S := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    have nz : x≠0 := by
      have hx' : x≠0 ∧ x≠2 ∧ x≠ -2 := by simpa [active] using hx
      exact hx'.1
    let u := Units.mk0 x nz
    exact mem_image.mpr ⟨⟨u^2, ⟨u,rfl⟩⟩,mem_univ _, rfl⟩
  have vanishes (z : ZMod p) (hz : z ∈ S) (out : z ∉ evenBases p) : weight z = 0 := by
    obtain ⟨u,_,rfl⟩ := mem_image.mp hz
    obtain ⟨v, hv⟩ := u.property
    have eqn : (v : ZMod p)^2 = squareValue u := congrArg Units.val hv
    have four : squareValue u = 4 := by
      by_contra hf
      apply out
      apply mem_image.mpr
      refine ⟨v, ?_, eqn⟩
      have non : (v:ZMod p) ≠ 0 := v.ne_zero
      have neq : (v:ZMod p) ≠ 2 := by
        intro h
        exact hf (by rw [←eqn,h]; ring)
      have nen : (v:ZMod p) ≠ -2 := by
        intro h
        exact hf (by rw [←eqn,h]; ring)
      simpa [active] using And.intro non (And.intro neq nen)
    simp [weight,four]
  rw [component_even hp, signal]
  calc
    _ = 2*∑ z ∈ evenBases p, weight z*z^(n+1) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro z _
      rw [pow_succ]; ring
    _ = 2*∑ z ∈ S, weight z*z^(n+1) := by
      congr 1
      exact sum_subset subset (fun z hz out => by simp [vanishes z hz out])
    _ = _ := by dsimp only [S]; rw [sum_image square_inj.injOn]

/-- For the moment degrees 2s, 4s, … the period is exactly the index
of the kernel of the stride power map when its fibers have odd size and
its image has at least three elements. -/
theorem local_period {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (s t : ℕ)
    (pos : 0 < s) (odd : Odd (s.gcd ((p-1)/2)))
    (large : 3 ≤ (p-1)/2 / s.gcd ((p-1)/2)) :
    Function.Periodic (fun k : ℕ => component p (2*(s*(k+1)))) t ↔
      (p-1)/2 / s.gcd ((p-1)/2) ∣ t := by
  classical
  let e := squareValue (p:=p)
  have two : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  let u := Units.mk0 (2 : ZMod p) two
  let four : SquareUnits p := ⟨u^2, ⟨u,rfl⟩⟩
  have ef : e four = 4 := by change (2 : ZMod p)^2 = 4; ring
  let w (z : SquareUnits p) : ℤ := -quadraticChar (ZMod p) (e z-4)
  have signs (z : SquareUnits p) (ne : z ≠ four) : w z=1 ∨ w z= -1 := by
    have reg : e z-4 ≠ 0 := sub_ne_zero.mpr (by rw [←ef]; exact fun h => ne (square_inj h))
    rcases sq_eq_one_iff.mp (quadraticChar_sq_one reg) with h | h
    · right; exact congrArg Neg.neg h
    · left; exact (congrArg Neg.neg h).trans (by decide)
  have sc := square_card hp
  have hsmall : s.gcd ((p-1)/2) < p := by
    obtain ⟨j,hj⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
    have := (Fact.out : p.Prime).two_le
    have le := Nat.le_of_dvd (show 0 < (p-1)/2 by omega) (Nat.gcd_dvd_right s ((p-1)/2))
    omega
  have h := odd_fiber_period e square_inj w four signs s t (sc ▸ odd) (sc ▸ hsmall) (sc ▸ large)
  rw [sc] at h
  rw [←h]
  have rep (k : ℕ) : component p (2*(s*(k+1))) =
      2*∑ z : SquareUnits p, (w z : ZMod p)*(e (z^s))^(k+1) := by
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.mul_pos pos (Nat.succ_pos k)).ne'
    rw [hn, square_signal hp]
    apply congrArg (fun x : ZMod p => 2*x)
    apply sum_congr rfl
    intro z _
    simp only [map_pow, ←pow_mul, hn, w, Int.cast_neg, weight, e]
  constructor
  · intro per k
    exact mul_left_cancel₀ two (by simpa only [rep] using per k)
  · intro per k
    simpa only [rep] using congrArg (fun x : ZMod p => 2*x) (per k)

/-- Sampling complete moments at degrees 2s, 4s, … . -/
noncomputable def sampled (N : ℕ) [NeZero N] (s k : ℕ) : ZMod N :=
  ProjectiveWordMoments.moment N (2*(s*(k+1)))

/-- Size of the image of the stride power map on the local square group. -/
def imageSize (p s : ℕ) : ℕ := (p-1)/2 / s.gcd ((p-1)/2)

/-- When the two kernel sizes are odd and both images have at least three
elements, the lcm of their sizes is the least period of the actual scalar sequence. -/
theorem composite_period {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p ≠ 2) (hq : q ≠ 2) (s t : ℕ) (pos : 0 < s)
    (oddp : Odd (s.gcd ((p-1)/2))) (oddq : Odd (s.gcd ((q-1)/2)))
    (sizep : 3 ≤ imageSize p s) (sizeq : 3 ≤ imageSize q s) :
    Function.Periodic (sampled (p*q) s) t ↔ (imageSize p s).lcm (imageSize q s) ∣ t := by
  rw [Nat.lcm_dvd_iff]
  change _ ↔ (p-1)/2 / s.gcd ((p-1)/2) ∣ t ∧ (q-1)/2 / s.gcd ((q-1)/2) ∣ t
  rw [← local_period hp s t pos oddp sizep, ←local_period hq s t pos oddq sizeq]
  let e := ZMod.chineseRemainder cop
  have crt (k : ℕ) : e (sampled (p*q) s k) =
      (component p (2*(s*(k+1))), component q (2*(s*(k+1)))) :=
    ProjectiveWordMoments.components cop hp hq _
  constructor
  · intro h
    have pair (k) := (crt (k+t)).symm.trans ((congrArg e (h k)).trans (crt k))
    exact ⟨fun k => congrArg Prod.fst (pair k), fun k => congrArg Prod.snd (pair k)⟩
  · rintro ⟨h₁,h₂⟩ k
    apply e.injective
    exact (crt _).trans ((Prod.ext (h₁ k) (h₂ k)).trans (crt k).symm)

private theorem predecessor_gcd (a b : ℕ) :
    (((2*a+1)*(2*b+1)-1)/2).gcd a = a.gcd b := by
  have expand : (2*a+1)*(2*b+1) = 2*(b+a*(2*b+1))+1 := by ring
  rw [expand, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by decide : 0<2),
    Nat.gcd_add_mul_left_left, Nat.gcd_comm]

/-- With the public stride (N−1)/2 the two fibers have the same cardinality,
gcd(a,b), for a=(p−1)/2 and b=(q−1)/2. When that cardinality is odd the
period is the product of the two reduced indices. -/
theorem predecessor_period {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p ≠ 2) (hq : q ≠ 2) (t : ℕ) :
    let a := (p-1)/2
    let b := (q-1)/2
    let g := a.gcd b
    Odd g → 3 ≤ a/g → 3 ≤ b/g →
      (Function.Periodic (sampled (p*q) ((p*q-1)/2)) t ↔ (a/g)*(b/g) ∣ t) := by
  intro a b g odd la lb
  obtain ⟨x,hx⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨y,hy⟩ := (Fact.out : q.Prime).odd_of_ne_two hq
  have px : p = 2*a+1 := by dsimp [a]; omega
  have qy : q = 2*b+1 := by dsimp [b]; omega
  have gp : ((p*q-1)/2).gcd a = g := by
    nth_rw 1 [px,qy]; exact predecessor_gcd a b
  have gq : ((p*q-1)/2).gcd b = g := by
    rw [Nat.mul_comm p q]; nth_rw 1 [px,qy]
    exact (predecessor_gcd b a).trans (Nat.gcd_comm b a)
  have ip : imageSize p ((p*q-1)/2) = a/g := by change a/_=a/g; rw [gp]
  have iq : imageSize q ((p*q-1)/2) = b/g := by change b/_=b/g; rw [gq]
  have pp := (Fact.out : p.Prime).two_le
  have pq := (Fact.out : q.Prime).two_le
  have pos : 0 < (p*q-1)/2 := by
    have hh : 4 ≤ p*q := by nlinarith
    omega
  rw [composite_period cop hp hq _ t pos (gp ▸ odd) (gq ▸ odd) (ip ▸ la) (iq ▸ lb),
    ip,iq]
  have cop' : (a/g).Coprime (b/g) := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left b (by dsimp [a]; omega))
  rw [cop'.lcm_eq_mul]

/-- Arithmetic readout if the reduced product A*B has been determined.
Each hidden predecessor is 2g times one of A,B. -/
private theorem reduced_readout (g A B : ℕ) (ha : 0 < A) (hb : 0 < B) :
    let N := (2*g*A+1)*(2*g*B+1)
    let L := A*B
    (N/(4*L)).sqrt = g := by
  intro N L
  have pos : 0 < 4*L := Nat.mul_pos (by decide) (Nat.mul_pos ha hb)
  apply Nat.le_antisymm
  · apply Nat.le_of_lt_succ
    apply Nat.sqrt_lt.mpr
    apply (Nat.div_lt_iff_lt_mul pos).mpr
    have left : 2*g*A+1 < 2*(g+1)*A := by nlinarith
    have right : 2*g*B+1 ≤ 2*(g+1)*B := by nlinarith
    have upper := Nat.mul_lt_mul_of_lt_of_le left right (by omega)
    dsimp [N,L]
    nlinarith
  · apply Nat.le_sqrt.mpr
    apply (Nat.le_div_iff_mul_le pos).mpr
    dsimp [N,L]
    nlinarith

/-- Given the exact period for the public predecessor stride, recover the
factor sum by integer division and square root. Computing the period itself
is a separate prerequisite. -/
theorem sum_from_predecessor_period {p q L : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : p ≠ 2) (hq : q ≠ 2)
    (known : ∀ t, Function.Periodic (sampled (p*q) ((p*q-1)/2)) t ↔ L ∣ t) :
    let a := (p-1)/2
    let b := (q-1)/2
    let g := a.gcd b
    Odd g → 3 ≤ a/g → 3 ≤ b/g →
      p+q = p*q+1-4*((p*q/(4*L)).sqrt)^2*L := by
  intro a b g odd la lb
  let A := a/g
  let B := b/g
  have spec (t : ℕ) := predecessor_period cop hp hq t odd la lb
  have period : L=A*B := Nat.dvd_antisymm ((known _).mp ((spec _).mpr dvd_rfl))
    ((spec _).mp ((known _).mpr dvd_rfl))
  obtain ⟨x,hx⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨y,hy⟩ := (Fact.out : q.Prime).odd_of_ne_two hq
  have ag : g*A=a := by rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left a b)]
  have bg : g*B=b := by rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_right a b)]
  have pa : p=2*g*A+1 := by rw [Nat.mul_assoc,ag]; dsimp only [a]; omega
  have qb : q=2*g*B+1 := by rw [Nat.mul_assoc,bg]; dsimp only [b]; omega
  rw [pa,qb,period,reduced_readout g A B (by dsimp [A]; omega) (by dsimp [B]; omega)]
  have eqn : (2*g*A+1)*(2*g*B+1)+1 = (2*g*A+1+(2*g*B+1))+4*g^2*(A*B) := by ring
  rw [eqn, Nat.add_sub_cancel]


private theorem oddpart_gcd {H a : ℕ} (hp : H ≠ 0) :
    (ordCompl[2] H).gcd a = ordCompl[2] (H.gcd a) := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_ordCompl_of_dvd_not_dvd
    · exact Nat.dvd_gcd ((Nat.gcd_dvd_left ..).trans (Nat.ordCompl_dvd H 2)) (Nat.gcd_dvd_right ..)
    · exact fun h => Nat.not_dvd_ordCompl Nat.prime_two hp (h.trans (Nat.gcd_dvd_left ..))
  · exact Nat.dvd_gcd (Nat.ordCompl_dvd_ordCompl_of_dvd (Nat.gcd_dvd_left ..) 2)
      ((Nat.ordCompl_dvd _ _).trans (Nat.gcd_dvd_right ..))

private theorem dyadic_correction {a b H g A B L : ℕ} (hp : H ≠ 0) (gp : 0 < g)
    (odd : Odd g) (left : g*A=a) (right : g*B=b) (given : A.lcm B = L)
    (full : H.gcd (a.lcm b) = a.gcd b) (oddpart : ordCompl[2] (a.gcd b) = g) :
    A.gcd B = (ordProj[2] H).gcd L := by
  have scaled : g*(A.gcd B) = a.gcd b := by rw [←Nat.gcd_mul_left, left, right]
  have lscaled : g*L = a.lcm b := by rw [←given,←Nat.lcm_mul_left, left, right]
  have pure : A.gcd B = ordProj[2] (a.gcd b) := by
    apply Nat.eq_of_mul_eq_mul_left gp
    rw [scaled, ←oddpart, Nat.mul_comm, Nat.ordProj_mul_ordCompl_eq_self]
  have div : a.gcd b ∣ H := by rw [←full]; exact Nat.gcd_dvd_left ..
  have hL : A.gcd B ∣ L := by rw [←given]; exact (Nat.gcd_dvd_left ..).trans (Nat.dvd_lcm_left ..)
  let c := (ordProj[2] H).gcd L
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (pure ▸ Nat.ordProj_dvd_ordProj_of_dvd hp div 2) hL
  · have cH : c ∣ H := (Nat.gcd_dvd_left ..).trans (Nat.ordProj_dvd H 2)
    have cL : c ∣ L := Nat.gcd_dvd_right ..
    have cd : c ∣ a.gcd b := by
      rw [←full,←lscaled]; exact Nat.dvd_gcd cH (dvd_mul_of_dvd_right cL g)
    have cop : c.Coprime g := Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left ..)
      (odd.coprime_two_left.pow_left _)
    exact cop.dvd_of_dvd_mul_left (scaled ▸ cd)

private theorem odd_predecessor_data {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) :
    let a := (p-1)/2
    let b := (q-1)/2
    let H := (p*q-1)/2
    let s := ordCompl[2] H
    let g := ordCompl[2] (a.gcd b)
    s.gcd a = g ∧ s.gcd b = g ∧ H.gcd (a.lcm b) = a.gcd b ∧
      0 < H ∧ 0 < s ∧ 0 < g ∧ Odd g := by
  intro a b H s g
  obtain ⟨x,hx⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨y,hy⟩ := (Fact.out : q.Prime).odd_of_ne_two hq
  have pp := (Fact.out : p.Prime).one_lt
  have pq := (Fact.out : q.Prime).one_lt
  have ap : p=2*a+1 := by dsimp [a]; omega
  have bq : q=2*b+1 := by dsimp [b]; omega
  have Hpos : 0 < H := by
    dsimp [H]; have prod : 4 ≤ p*q := by nlinarith
    omega
  have dpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (by dsimp [a]; omega)
  have halves : p*q-1=2*H := by
    obtain ⟨z,hz⟩ := ((Fact.out : p.Prime).odd_of_ne_two hp).mul ((Fact.out : q.Prime).odd_of_ne_two hq)
    dsimp [H]; omega
  have full := PartialOrderLift.exponent_gcd pp pq
  rw [show p-1=2*a by omega,show q-1=2*b by omega,halves,Nat.lcm_mul_left,
    Nat.gcd_mul_left,Nat.gcd_mul_left] at full
  have gp : H.gcd a = a.gcd b := by
    dsimp only [H]; nth_rw 1 [ap,bq]; exact predecessor_gcd a b
  have gq : H.gcd b = a.gcd b := by
    dsimp only [H]; rw [Nat.mul_comm p q]; nth_rw 1 [ap,bq]
    exact (predecessor_gcd b a).trans (Nat.gcd_comm b a)
  exact ⟨(oddpart_gcd Hpos.ne').trans (congrArg (fun n => ordCompl[2] n) gp),
    (oddpart_gcd Hpos.ne').trans (congrArg (fun n => ordCompl[2] n) gq),
    by rw [Nat.gcd_comm]; omega, Hpos, Nat.ordCompl_pos 2 Hpos.ne',
    Nat.ordCompl_pos 2 dpos.ne', Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two dpos.ne')⟩

/-- Using the odd part of (N−1)/2 as the public stride handles even common
predecessors as well. Only the requirement on the two image sizes remains. -/
theorem odd_predecessor_period {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : p ≠ 2) (hq : q ≠ 2) (t : ℕ) :
    let a := (p-1)/2
    let b := (q-1)/2
    let s := ordCompl[2] ((p*q-1)/2)
    let g := ordCompl[2] (a.gcd b)
    3 ≤ a/g → 3 ≤ b/g →
      (Function.Periodic (sampled (p*q) s) t ↔ (a/g).lcm (b/g) ∣ t) := by
  intro a b s g la lb
  obtain ⟨ga,gb,_,_,pos,_,odd⟩ := odd_predecessor_data hp hq
  have ia : imageSize p s=a/g := by change a/s.gcd a=a/g; rw [ga]
  have ib : imageSize q s=b/g := by change b/s.gcd b=b/g; rw [gb]
  simpa only [ia,ib] using composite_period cop hp hq s t pos (ga ▸ odd) (gb ▸ odd) (ia ▸ la) (ib ▸ lb)

/-- Recover the sum from the exact single-phase period for the odd stride.
The dyadic multiplier is the gcd of the period with the two-part of (N−1)/2. -/
theorem sum_from_odd_predecessor_period {p q L : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : p ≠ 2) (hq : q ≠ 2) :
    let a := (p-1)/2
    let b := (q-1)/2
    let H := (p*q-1)/2
    let s := ordCompl[2] H
    let g := ordCompl[2] (a.gcd b)
    let K := ((ordProj[2] H).gcd L)*L
    3 ≤ a/g → 3 ≤ b/g →
      (∀ t, Function.Periodic (sampled (p*q) s) t ↔ L ∣ t) →
      p+q = p*q+1-4*((p*q/(4*K)).sqrt)^2*K := by
  intro a b H s g K la lb known
  let A := a/g
  let B := b/g
  have spec (t : ℕ) := odd_predecessor_period cop hp hq t la lb
  have period : A.lcm B=L := Nat.dvd_antisymm ((spec _).mp ((known _).mpr dvd_rfl))
    ((known _).mp ((spec _).mpr dvd_rfl))
  obtain ⟨_,_,full,pos,_,gp,odd⟩ := odd_predecessor_data hp hq
  have ga : g*A=a := Nat.mul_div_cancel' ((Nat.ordCompl_dvd _ _).trans (Nat.gcd_dvd_left a b))
  have gb : g*B=b := Nat.mul_div_cancel' ((Nat.ordCompl_dvd _ _).trans (Nat.gcd_dvd_right a b))
  have corr := dyadic_correction pos.ne' gp odd ga gb period full rfl
  have product : K=A*B := by change _*_=A*B; rw [←corr,←period,Nat.gcd_mul_lcm]
  obtain ⟨x,hx⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨y,hy⟩ := (Fact.out : q.Prime).odd_of_ne_two hq
  have pa : p=2*g*A+1 := by rw [Nat.mul_assoc,ga]; dsimp only [a]; omega
  have qb : q=2*g*B+1 := by rw [Nat.mul_assoc,gb]; dsimp only [b]; omega
  rw [product,pa,qb,reduced_readout g A B (by dsimp [A]; omega) (by dsimp [B]; omega)]
  have eqn : (2*g*A+1)*(2*g*B+1)+1 = (2*g*A+1+(2*g*B+1))+4*g^2*(A*B) := by ring
  rw [eqn,Nat.add_sub_cancel]

/-- For p<q<2p, two public trial candidates cover all small-image exceptions
for the odd part of the predecessor stride. -/
theorem balanced_image_sizes {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (ordered : p<q) (balanced : q<2*p) :
    let N := p*q
    let H := (N-1)/2
    p = ((8*N+1).sqrt+1)/4 ∨ p = ((24*N+1).sqrt+1)/6 ∨
      3 ≤ imageSize p (ordCompl[2] H) ∧ 3 ≤ imageSize q (ordCompl[2] H) := by
  intro N H
  let a := (p-1)/2
  let b := (q-1)/2
  let g := ordCompl[2] (a.gcd b)
  let A := a/g
  let B := b/g
  have ga : g*A=a := Nat.mul_div_cancel' ((Nat.ordCompl_dvd _ _).trans (Nat.gcd_dvd_left a b))
  have gb : g*B=b := Nat.mul_div_cancel' ((Nat.ordCompl_dvd _ _).trans (Nat.gcd_dvd_right a b))
  obtain ⟨x,hx⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨y,hy⟩ := (Fact.out : q.Prime).odd_of_ne_two hq
  have pa : p=2*g*A+1 := by rw [Nat.mul_assoc,ga]; dsimp only [a]; omega
  have qb : q=2*g*B+1 := by rw [Nat.mul_assoc,gb]; dsimp only [b]; omega
  have pos : 0 < A := by
    apply Nat.pos_of_ne_zero
    intro zero
    have := (Fact.out : p.Prime).one_lt
    rw [zero, Nat.mul_zero] at pa
    omega
  have ord : A < B := by
    apply lt_of_not_ge
    intro h
    have le := Nat.mul_le_mul_left (2*g) h
    omega
  have cap : B ≤ 2*A := by
    apply le_of_not_gt
    intro h
    have le := Nat.mul_le_mul_left (2*g) (Nat.succ_le_of_lt h)
    obtain ⟨_,_,_,_,_,gp,_⟩ := odd_predecessor_data hp hq
    change 0<g at gp
    nlinarith
  by_cases large : 3 ≤ A
  · right; right
    obtain ⟨g₁,g₂,_⟩ := odd_predecessor_data hp hq
    change 3 ≤ a/_ ∧ 3 ≤ b/_
    rw [g₁, g₂]
    exact ⟨large,large.trans ord.le⟩
  by_cases doubled : B=2*A
  · left
    have sq : 8*N+1=(2*p+q)^2 := by dsimp only [N]; rw [pa,qb,doubled]; ring
    have relation : q+1=2*p := by rw [pa,qb,doubled]; ring
    rw [sq,Nat.sqrt_eq']; omega
  · right; left
    have ai : A=2 := by omega
    have bi : B=3 := by omega
    have sq : 24*N+1=(3*p+2*q)^2 := by dsimp only [N]; rw [pa,qb,ai,bi]; ring
    have relation : 2*q+1=3*p := by rw [pa,qb,ai,bi]; ring
    rw [sq,Nat.sqrt_eq']; omega

/-- For p<q<2p, two public trial candidates cover all small-image exceptions.
After they fail division, the exact odd-stride scalar period always gives the
sum by the dyadically corrected readout. -/
theorem balanced_readout {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : p ≠ 2) (hq : q ≠ 2) (ordered : p<q) (balanced : q<2*p) :
    let N := p*q
    let H := (N-1)/2
    p = ((8*N+1).sqrt+1)/4 ∨ p = ((24*N+1).sqrt+1)/6 ∨
      ∀ L, (∀ t, Function.Periodic (sampled N (ordCompl[2] H)) t ↔ L ∣ t) →
        let K := ((ordProj[2] H).gcd L)*L
        p+q=N+1-4*((N/(4*K)).sqrt)^2*K := by
  intro N H
  rcases balanced_image_sizes hp hq ordered balanced with first | second | ⟨largep,largeq⟩
  · exact Or.inl first
  · exact Or.inr (Or.inl second)
  · right; right
    obtain ⟨g₁,g₂,_⟩ := odd_predecessor_data hp hq
    unfold imageSize at largep largeq
    rw [g₁] at largep
    rw [g₂] at largeq
    exact fun L given => sum_from_odd_predecessor_period cop hp hq largep largeq given

/-- On this small control the public stride cuts the original period
105 down to 15. The factors are supplied to check the example. -/
theorem control3053 (t : ℕ) :
    (Function.Periodic (JacobiMomentPeriod.completeEven 3053) t ↔ 105 ∣ t) ∧
    (Function.Periodic (sampled 3053 1526) t ↔ 15 ∣ t) := by
  letI : Fact (Nat.Prime 43) := ⟨by decide⟩
  letI : Fact (Nat.Prime 71) := ⟨by decide⟩
  exact ⟨JacobiMomentPeriod.composite_iff (p:=43) (q:=71) (by decide) (by decide) (by decide) t,
    predecessor_period (p:=43) (q:=71) (by decide) (by decide) (by decide) t (by decide) (by decide) (by decide)⟩

private def reduced (p k : ℕ) [Fact p.Prime] : ZMod p :=
  -(∑ x : ZMod p, x^((220*(k+1)-1)%(p-1)+1) * (x^2-4)^(p/2))

private theorem component_reduced {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (k : ℕ) :
    component p (220*(k+1)) = reduced p k := by
  unfold component reduced
  apply congrArg Neg.neg
  apply sum_congr rfl
  intro z _
  rw [quadraticChar_eq_pow_of_char_ne_two' (by rwa [ZMod.ringChar_zmod_n]), ZMod.card]
  congr 1
  by_cases zero : z=0
  · simp [zero]
  have d := Nat.mod_add_div (220*(k+1)-1) (p-1)
  conv_lhs => rw [show 220*(k+1) = ((220*(k+1)-1)%(p-1)+1)+(p-1)*((220*(k+1)-1)/(p-1)) by omega]
  rw [pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one zero, one_pow, mul_one]

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

private def pair221 : Fin 6 → ZMod 13 × ZMod 17 :=
  ![(6,6),(5,2),(2,6),(6,2),(5,6),(2,2)]

private theorem local_table (k : ℕ) :
    (component 13 (220*(k+1)), component 17 (220*(k+1))) = pair221 (Fin.ofNat' 6 k) := by
  have table : ∀ i : Fin 12, (reduced 13 i, reduced 17 i) =
      pair221 (Fin.ofNat' 6 (i:ℕ)) := by decide +kernel
  rw [component_reduced (by decide),component_reduced (by decide)]
  have reduce (p : ℕ) [Fact p.Prime] (eqn : (220*(k+1)-1)%(p-1) =
      (220*(k%12+1)-1)%(p-1)) : reduced p k = reduced p (k%12) := by
    simp only [reduced,eqn]
  rw [reduce 13 (by omega), reduce 17 (by omega)]
  have same : Fin.ofNat' 6 (k%12) = Fin.ofNat' 6 k := by apply Fin.ext; change k%12%6 = k%6; omega
  exact (table (Fin.ofNat' 12 k)).trans (congrArg pair221 same)

/-- For 221 the stride 110 has even fibers of size two. The power images have
orders three and four, yet cancellation gives the sampled scalar period six. -/
theorem control221 (t : ℕ) :
    (imageSize 13 110).lcm (imageSize 17 110) = 12 ∧
    (Function.Periodic (sampled 221 110) t ↔ 6 ∣ t) := by
  refine ⟨by decide, ?_⟩
  unfold sampled
  let e := ZMod.chineseRemainder (show Nat.Coprime 13 17 by decide)
  have pair (k : ℕ) : e (ProjectiveWordMoments.moment 221 (2*(110*(k+1)))) =
      pair221 (Fin.ofNat' 6 k) := by
    have h := ProjectiveWordMoments.components (p:=13) (q:=17) (by decide) (by decide) (by decide) (220*(k+1))
    change e _ = (component 13 _, component 17 _) at h
    rw [show 2*(110*(k+1))=220*(k+1) by ring]
    exact h.trans (local_table k)
  constructor
  · intro per
    have eqn := congrArg e (per 0)
    dsimp only [Nat.zero_add] at eqn
    rw [pair,pair] at eqn
    have injective : Function.Injective pair221 := by decide +kernel
    have idx := congrArg Fin.val (injective eqn)
    exact Nat.dvd_of_mod_eq_zero (by simpa only [Nat.zero_add] using idx)
  · intro divides k
    apply e.injective
    dsimp only
    rw [pair,pair]
    apply congrArg pair221
    apply Fin.ext
    change (k+t)%6=k%6
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd divides]

/-- Stripping the factor of two from stride 110 restores period 24 at 221.
The resulting dyadic multiplier is two and the corrected sum is 30. -/
theorem odd_control221 (t : ℕ) :
    (Function.Periodic (sampled 221 55) t ↔ 24 ∣ t) ∧
    (2:ℕ).gcd 24 = 2 ∧ 221+1-4*((221/(4*(2*24)):ℕ).sqrt)^2*(2*24)=30 :=
  ⟨composite_period (p:=13) (q:=17) (by decide) (by decide) (by decide) 55 t
      (by decide) (by decide) (by decide) (by decide) (by decide), by decide, by decide⟩

/-- Prime factor certificate for the shortened-period control. -/
theorem control3053_factors : ExactFactorization 3053 [43,71] := by
  norm_num [ExactFactorization]

end PrimeFactors.JacobiScalarStride
