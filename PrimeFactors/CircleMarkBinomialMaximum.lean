import PrimeFactors.CircleMarkBinomialMask
import PrimeFactors.FrobeniusFixedCounts

/-! Exact local character sums for squared binomial masks, and optimization
of their magnitudes over exponents and constants. -/
namespace PrimeFactors.CircleMarkBinomialMaximum

open Finset Polynomial CircleMarkBinomialFibers CircleMarkBinomialMask CircleMarkJacobiMask
open scoped Classical
open private PrimeFactors.CircleMarkBinomialFibers.positiveUnits PrimeFactors.CircleMarkBinomialFibers.kernel
  PrimeFactors.CircleMarkBinomialFibers.positive_size PrimeFactors.CircleMarkBinomialFibers.fiber_count
  from PrimeFactors.CircleMarkBinomialFibers
open CircleMarkBinomialFibers (positiveUnits kernel positive_size fiber_count)

private theorem kernel_card {r : ℕ} [Fact r.Prime] (odd : r≠2) (e : ℕ) :
    Nat.card (kernel r e) = e.gcd ((r-1)/2) := by
  let S := univ.filter (fun x : positiveUnits r => x^e=1)
  let f : kernel r e ≃ ↥S := {
    toFun := fun x => ⟨⟨x.val,x.property.1⟩,mem_filter.mpr ⟨mem_univ _,Subtype.ext x.property.2⟩⟩
    invFun := fun x => ⟨x.val.val,x.val.property,congrArg Subtype.val (mem_filter.mp x.property).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have eqn : Nat.card (kernel r e) = S.card := (Nat.card_congr f).trans (by simp)
  have size : Fintype.card (positiveUnits r)=(r-1)/2 := (Nat.card_eq_fintype_card ..).symm.trans (positive_size r odd)
  exact eqn.trans ((FrobeniusFixedCounts.cyclic_count (positiveUnits r) e).trans (congrArg _ size))

private theorem signs_total {r : ℕ} [Fact r.Prime] (e : ℕ) :
    (fiber r e 1 1).card + (fiber r e 1 (-1)).card = e.gcd (r-1) := by
  let A := fiber r e 1 1
  let B := fiber r e 1 (-1)
  have dj : Disjoint A B := by
    apply disjoint_left.mpr
    intro t a b
    have s := (mem_filter.mp a).2.2
    have h := (mem_filter.mp b).2.2
    omega
  change A.card+B.card=_
  rw [←card_union_of_disjoint dj]
  let S := univ.filter (fun x : (ZMod r)ˣ => x^e=1)
  have eqn : S.card=(A ∪ B).card := by
    apply card_bij (fun (x : (ZMod r)ˣ) _ => (x:ZMod r))
    · intro x hx
      have power : (x:ZMod r)^e=1 := by simpa using congrArg Units.val (mem_filter.mp hx).2
      rcases quadraticChar_dichotomy x.ne_zero with s|s
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,power,s⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,power,s⟩)
    · exact fun x _ y _ h => Units.ext h
    · intro y hy
      have data : y^e=1 ∧ y≠0 := by
        rcases mem_union.mp hy with h|h <;>
          obtain ⟨power,sign⟩ := (mem_filter.mp h).2 <;>
          exact ⟨power,by intro z; rw [z,quadraticChar_zero] at sign; contradiction⟩
      let x := Units.mk0 y data.2
      exact ⟨x,mem_filter.mpr ⟨mem_univ _,Units.ext (by simpa [x] using data.1)⟩,rfl⟩
  rw [←eqn]
  simpa only [S,Fintype.card_units,ZMod.card] using FrobeniusFixedCounts.cyclic_count (ZMod r)ˣ e

private theorem one_sum {r : ℕ} [Fact r.Prime] (odd : r≠2) (e : ℕ) :
    localSum r (binomial e 1) = (e.gcd (r-1):ℤ)-2*(e.gcd ((r-1)/2):ℤ) := by
  have nonempty : (1:ZMod r) ∈ fiber r e 1 1 := mem_filter.mpr ⟨mem_univ _,one_pow _,map_one _⟩
  have pos := (fiber_count r e 1 1 (by decide)).resolve_left (card_pos.mpr ⟨_,nonempty⟩).ne'
  rw [kernel_card odd] at pos
  have sum := signs_total (r:=r) e
  rw [local_difference r odd,Int.cast_one]
  omega

private theorem weighted {r : ℕ} [Fact r.Prime] (odd : r≠2) (e : ℕ) (c : ℤ) :
    localSum r (binomial e c) = -(∑ t : ZMod r, if t^e=(c:ZMod r) then quadraticChar (ZMod r) t else 0) := by
  simp [local_eq odd, CircleMarkJacobiMask.rootSet, binomial, sub_eq_zero, sum_filter]

private theorem translate {r : ℕ} [Fact r.Prime] (odd : r≠2) (e : ℕ) (c : ℤ)
    (x : (ZMod r)ˣ) (root : (x:ZMod r)^e=(c:ZMod r)) :
    localSum r (binomial e c) = quadraticChar (ZMod r) (x:ZMod r)*localSum r (binomial e 1) := by
  rw [weighted odd,weighted odd,mul_neg, neg_inj, mul_sum]
  let equivalence := Equiv.mulLeft₀ (x:ZMod r) x.ne_zero
  apply Fintype.sum_equiv equivalence.symm
  intro t
  obtain ⟨u,rfl⟩ := equivalence.surjective t
  rw [equivalence.symm_apply_apply]
  change (if ((x:ZMod r)*u)^e=(c:ZMod r) then quadraticChar (ZMod r) ((x:ZMod r)*u) else 0) = _
  rw [mul_pow,←root,map_mul,Int.cast_one]
  by_cases pow : u^e=1
  · simp [pow]
  · have miss : (x:ZMod r)^e*u^e≠(x:ZMod r)^e := by
      intro eqn
      exact pow (mul_left_cancel₀ (pow_ne_zero e x.ne_zero) (eqn.trans (mul_one _).symm))
    simp [pow,miss]

/-- Exact local magnitude, including the empty unit fiber. When a unit root
exists its character determines the sign relative to the mask with c=1. -/
theorem local_exact {r : ℕ} [Fact r.Prime] (odd : r≠2) (e : ℕ) (c : ℤ) :
    (localSum r (binomial e c)).natAbs =
      if ∃ x : (ZMod r)ˣ, (x:ZMod r)^e=(c:ZMod r)
      then ((e.gcd (r-1):ℤ)-2*(e.gcd ((r-1)/2):ℤ)).natAbs else 0 := by
  split_ifs with root
  · obtain ⟨x,hx⟩ := root
    rw [translate odd e c x hx,one_sum odd,Int.natAbs_mul]
    rcases quadraticChar_dichotomy x.ne_zero with pos|neg
    · simp [pos]
    · simp [neg]
  · rw [weighted odd]
    have zero (t : ZMod r) : (if t^e=(c:ZMod r) then quadraticChar (ZMod r) t else 0) = 0 := by
      split_ifs with ht
      · by_cases z : t=0
        · rw [z,quadraticChar_zero]
        · exact (root ⟨Units.mk0 t z,ht⟩).elim
      · rfl
    simp only [zero,sum_const_zero,neg_zero,Int.natAbs_zero]


private theorem dyadic_gcd {a b : ℕ} (i j : ℕ) (ao : Odd a) (bo : Odd b) :
    (2^i*a).gcd (2^j*b) = 2^(min i j)*a.gcd b := by
  have ordered {s t : ℕ} (sto : s≤t) (x y : ℕ) (xo : Odd x) :
      (2^s*x).gcd (2^t*y) = 2^s*x.gcd y := by
    have split : 2^t*y=2^s*(2^(t-s)*y) := by
      rw [←mul_assoc,←pow_add]; congr 2; omega
    rw [split,Nat.gcd_mul_left]
    exact congrArg _ (((Nat.coprime_two_left.mpr xo).pow_left (t-s)).gcd_mul_left_cancel_right y)
  rcases le_total i j with le|le
  · rw [min_eq_left le,ordered le a b ao]
  · rw [min_eq_right le,Nat.gcd_comm,ordered le b a bo,Nat.gcd_comm b]

/-- At c=1 the magnitude has a simple parity cutoff. Write the local half-period
as 2^a*m and the positive exponent as 2^j*s, with m and s odd. -/
theorem one_dyadic {r a m s : ℕ} [hr : Fact r.Prime] (odd : r≠2)
    (shape : (r-1)/2=2^a*m) (mo : Odd m) (so : Odd s) (j : ℕ) :
    (localSum r (binomial (2^j*s) 1)).natAbs = if j≤a then 2^j*s.gcd m else 0 := by
  obtain ⟨h,rh⟩ := hr.out.odd_of_ne_two odd
  have full : r-1=2^(a+1)*m := by
    rw [pow_succ]; have eqn : 2*((r-1)/2)=r-1 := by omega
    rw [shape] at eqn
    nlinarith only [eqn]
  rw [one_sum odd,shape,full,dyadic_gcd _ _ so mo,dyadic_gcd _ _ so mo]
  split_ifs with h
  · rw [min_eq_left h,min_eq_left (by omega : j≤a+1)]
    have same (x : ℕ) : ((x:ℤ)-2*x).natAbs=x := by rw [show (x:ℤ)-2*x= -x by ring]; simp
    exact same _
  · rw [min_eq_right (by omega : a≤j),min_eq_right (by omega : a+1≤j),pow_succ]
    push_cast
    rw [show (2:ℤ)^a*2*(s.gcd m)-2*(2^a*(s.gcd m))=0 by ring]
    rfl

private theorem local_le_one {r : ℕ} [Fact r.Prime] (odd : r≠2) (e : ℕ) (c : ℤ) :
    (localSum r (binomial e c)).natAbs ≤ (localSum r (binomial e 1)).natAbs := by
  rw [local_exact odd,one_sum odd]
  split_ifs <;> omega

private theorem zero_one {r : ℕ} [hr : Fact r.Prime] (odd : r≠2) :
    (localSum r (binomial 0 1)).natAbs=0 := by
  obtain ⟨s,eq⟩ := hr.out.odd_of_ne_two odd
  rw [one_sum odd,Nat.gcd_zero_left,Nat.gcd_zero_left]
  have half : (r-1)/2=s := by omega
  have twice : r-1=2*s := by omega
  rw [half,twice]
  simp

/-- The closed maximum given dyadic decompositions of the local half-periods.
The common power of two is the smaller of the two local powers of two. -/
theorem dyadic_maximum {p q a b m n : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2)
    (ps : (p-1)/2=2^a*m) (qs : (q-1)/2=2^b*n) (mo : Odd m) (no : Odd n) :
    let w := min a b
    let peak := (2^w*m)*(2^w*n)
    (globalSum (p*q) (binomial (2^w*(m*n)) 1)).natAbs = peak ∧
      ∀ e c, (globalSum (p*q) (binomial e c)).natAbs ≤ peak := by
  dsimp only
  have mp : 0<m := by obtain ⟨k,h⟩ := mo; omega
  have np : 0<n := by obtain ⟨k,h⟩ := no; omega
  constructor
  · rw [factorization diff,Int.natAbs_mul,one_dyadic op ps mo (mo.mul no),
      one_dyadic oq qs no (mo.mul no),if_pos (min_le_left ..),if_pos (min_le_right ..),
      Nat.gcd_eq_right (dvd_mul_right m n),Nat.gcd_eq_right (dvd_mul_left n m)]
  · intro e c
    rw [factorization diff,Int.natAbs_mul]
    apply (Nat.mul_le_mul (local_le_one op e c) (local_le_one oq e c)).trans
    by_cases ez : e=0
    · simp [ez,zero_one op]
    obtain ⟨j,s,so,rfl⟩ := Nat.exists_eq_two_pow_mul_odd ez
    rw [one_dyadic op ps mo so,one_dyadic oq qs no so]
    by_cases ja : j≤a
    · by_cases jb : j≤b
      · rw [if_pos ja,if_pos jb]
        have power := Nat.pow_le_pow_right (by decide : 0<2) (le_min ja jb)
        exact Nat.mul_le_mul (Nat.mul_le_mul power (Nat.le_of_dvd mp (Nat.gcd_dvd_right ..))) (Nat.mul_le_mul power (Nat.le_of_dvd np (Nat.gcd_dvd_right ..)))
      · simp [jb]
    · simp [ja]


/-- Exponent of two in the local half-period. -/
noncomputable def twoOrder (r : ℕ) := ((r-1)/2).factorization 2

/-- Odd part of the local half-period. -/
noncomputable def oddPart (r : ℕ) := ((r-1)/2)/2^(twoOrder r)

noncomputable def maximizingExponent (p q : ℕ) := 2^(min (twoOrder p) (twoOrder q))*(oddPart p*oddPart q)

noncomputable def ceiling (p q : ℕ) :=
  (2^(min (twoOrder p) (twoOrder q))*oddPart p)*(2^(min (twoOrder p) (twoOrder q))*oddPart q)

private theorem decomposition (r : ℕ) : (r-1)/2 = 2^(twoOrder r)*oddPart r :=
  (Nat.ordProj_mul_ordCompl_eq_self ((r-1)/2) 2).symm

private theorem odd_part {r : ℕ} [h : Fact r.Prime] (odd : r≠2) : Odd (oddPart r) := by
  have two := h.out.two_le
  exact Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (show (r-1)/2≠0 by omega))

/-- Sharp maximum over every exponent and integer constant; the single
constant one realizes it at the explicit common exponent. -/
theorem maximum {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (op : p≠2) (oq : q≠2) :
    (globalSum (p*q) (binomial (maximizingExponent p q) 1)).natAbs=ceiling p q ∧
      ∀ e c, (globalSum (p*q) (binomial e c)).natAbs ≤ ceiling p q :=
  dyadic_maximum diff op oq (decomposition p) (decomposition q) (odd_part op) (odd_part oq)

/-- Relative to the full product of half-periods, every unmatched factor of
two in their dyadic orders costs one factor of two in the exact maximum. -/
theorem ceiling_ratio (p q : ℕ) :
    ceiling p q * 2^(max (twoOrder p) (twoOrder q)-min (twoOrder p) (twoOrder q)) =
      ((p-1)/2)*((q-1)/2) := by
  let a := twoOrder p
  let b := twoOrder q
  let w := min a b
  have exponents : w+w+(max a b-w)=a+b := by dsimp [w]; omega
  rw [decomposition p,decomposition q]
  change (2^w*oddPart p)*(2^w*oddPart q)*2^(max a b-w) = (2^a*oddPart p)*(2^b*oddPart q)
  calc _ = 2^(w+w+(max a b-w))*(oddPart p*oddPart q) := by rw [pow_add,pow_add]; ring
       _ = _ := by rw [exponents,pow_add]; ring

/-- For 2183 the exact maximum is 261, attained at exponent 261. -/
theorem example_2183 :
    (globalSum 2183 (binomial 261 1)).natAbs=261 ∧
      ∀ e c, (globalSum 2183 (binomial e c)).natAbs≤261 := by
  letI : Fact (Nat.Prime 37) := ⟨by decide⟩
  letI : Fact (Nat.Prime 59) := ⟨by decide⟩
  exact dyadic_maximum (p:=37) (q:=59) (a:=1) (b:=0) (m:=9) (n:=29)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end PrimeFactors.CircleMarkBinomialMaximum
