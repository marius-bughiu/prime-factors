import PrimeFactors.ThreeSquareTwistExamples

/-! A twist with negative Jacobi symbol at the semiprime has opposite signs
at the two primes. The supplied three-square count then singles out the
prime with positive local sign, via Hirschhorn–Sellers equation (4). -/

namespace PrimeFactors.AdaptiveThreeSquareTwist

open FiniteThreeSquareTwists

/-- A negative product sign already forces the twist to be coprime to the radius. -/
theorem unit_of_negative {N d : ℕ} (pos : 0<N) (negative : jacobiSym (-(d:ℤ)) N= -1) :
    d.Coprime N := by
  letI : NeZero N := ⟨pos.ne'⟩
  have cop : (-(d:ℤ)).gcd N=1 := by
    by_contra h
    have zero := jacobiSym.eq_zero_iff_not_coprime.mpr h
    omega
  simpa only [Int.gcd_eq_natAbs,Int.natAbs_neg,Int.natAbs_natCast] using cop

section
attribute [local irreducible] r₃

/-- A factor with positive local sign contributes itself as the multiplier.
The other contributes itself plus two. No positivity of the base count
is required for the multiplicative identity. -/
theorem mixed (formula : HirschhornSellers) {p q d : ℕ} (pp : p.Prime) (qp : q.Prime)
    (op : Odd p) (oq : Odd q) (ne : p≠q) (negative : jacobiSym (-(d:ℤ)) (p*q)= -1) :
    (jacobiSym (-(d:ℤ)) p=1 ∧ jacobiSym (-(d:ℤ)) q= -1 ∧
      r₃ (d*(p*q)^2)=r₃ d*(p*q+2*p)) ∨
    (jacobiSym (-(d:ℤ)) p= -1 ∧ jacobiSym (-(d:ℤ)) q=1 ∧
      r₃ (d*(p*q)^2)=r₃ d*(p*q+2*q)) := by
  have cop := unit_of_negative (Nat.mul_pos pp.pos qp.pos) negative
  have pc := cop.of_dvd_right (dvd_mul_right p q)
  have qc := cop.of_dvd_right (dvd_mul_left q p)
  have count := ThreeSquareTwistExamples.two_primes formula pp qp op oq ne
    (pp.coprime_iff_not_dvd.mp pc.symm) (qp.coprime_iff_not_dvd.mp qc.symm)
  rw [jacobiSym.mul_right' _ pp.ne_zero qp.ne_zero] at negative
  have cases : jacobiSym (-(d:ℤ)) p=1 ∧ jacobiSym (-(d:ℤ)) q= -1 ∨
      jacobiSym (-(d:ℤ)) p= -1 ∧ jacobiSym (-(d:ℤ)) q=1 := by
    rcases jacobiSym.trichotomy (-(d:ℤ)) p with h|h|h
    · simp [h] at negative
    · exact Or.inl ⟨h,by simpa only [h,one_mul] using negative⟩
    · rw [h,neg_one_mul] at negative
      exact Or.inr ⟨h,by omega⟩
  rcases cases with ⟨ps,qs⟩|⟨ps,qs⟩
  · refine Or.inl ⟨ps,qs,Int.ofNat_inj.mp ?_⟩
    push_cast
    rw [count,ps,qs]
    ring
  · refine Or.inr ⟨ps,qs,Int.ofNat_inj.mp ?_⟩
    push_cast
    rw [count,ps,qs]
    ring

private theorem quotient {C B : ℕ} (N r : ℕ) (pos : 0<B) (h : C=B*(N+2*r)) :
    (C/B-N)/2=r := by
  rw [h,Nat.mul_div_cancel_left _ pos,Nat.add_sub_cancel_left,Nat.mul_div_cancel_left _ (by decide)]

/-- With a positive base count the integer quotient is exact, and its
excess over the known radius is twice the prime with positive local sign. -/
theorem reading (formula : HirschhornSellers) {p q d : ℕ} (pp : p.Prime) (qp : q.Prime)
    (op : Odd p) (oq : Odd q) (ne : p≠q) (negative : jacobiSym (-(d:ℤ)) (p*q)= -1)
    (represented : 0<r₃ d) :
    let value := (r₃ (d*(p*q)^2)/r₃ d-p*q)/2
    (value=p ∨ value=q) ∧ jacobiSym (-(d:ℤ)) value=1 := by
  dsimp only
  rcases mixed formula pp qp op oq ne negative with ⟨ps,_,count⟩|⟨_,qs,count⟩
  · rw [quotient (p*q) p represented count]
    exact ⟨Or.inl rfl,ps⟩
  · rw [quotient (p*q) q represented count]
    exact ⟨Or.inr rfl,qs⟩

end

private theorem base_twenty_three : r₃ 23=0 := by decide +kernel

attribute [local irreducible] r₃

private theorem two_at_fifteen : jacobiSym (-2) 15= -1 :=
  (jacobiSym.at_neg_two (b:=15) (by decide)).trans (by decide)

/-- At radius 15, twists 1 and 2 have negative global sign and select
opposite primes. The count at 225 is the prior direct census. The
count at 450 follows from the recurrence and the small base count. -/
theorem fifteen (formula : HirschhornSellers) :
    jacobiSym (-1) 15= -1 ∧ jacobiSym (-2) 15= -1 ∧
    jacobiSym (-1) 5=1 ∧ jacobiSym (-2) 3=1 ∧
    r₃ 1=6 ∧ r₃ 225=150 ∧ r₃ 2=12 ∧ r₃ 450=252 := by
  have plus : jacobiSym (-2) 3=1 :=
    (jacobiSym.at_neg_two (b:=3) (by decide)).trans (by decide)
  obtain ⟨b2,_,_,_,b1,_⟩ := small_counts
  refine ⟨(jacobiSym.at_neg_one (b:=15) (by decide)).trans (by decide),two_at_fifteen,
    (jacobiSym.at_neg_one (b:=5) (by decide)).trans (by decide),plus,b1,
    (radius 15).trans ThreeSquareRadiusCounts.toy_fifteen.1,b2,?_⟩
  have signs := mixed (p:=3) (q:=5) (d:=2) formula (by decide) (by decide)
    (by decide) (by decide) (by decide) two_at_fifteen
  rcases signs with ⟨_,_,count⟩|⟨bad,_,_⟩
  · change r₃ (2*(3*5)^2)=252
    rw [count,b2]
  · exact False.elim ((by decide : (1:ℤ)≠ -1) (plus.symm.trans bad))

/-- A negative public sign can coexist with a zero base count. The
multiplicative identity still holds, with both sides zero. -/
theorem unrepresented (formula : HirschhornSellers) :
    jacobiSym (-23) 15= -1 ∧ r₃ 23=0 ∧ r₃ (23*15^2)=0 := by
  have sign : jacobiSym (-23) 15= -1 := by
    rw [show jacobiSym (-23) 15=jacobiSym (-2*2^2) 15 from jacobiSym.mod_left' (by decide),
      jacobiSym.mul_left,jacobiSym.sq_one' (by decide : (2:ℤ).gcd (15:ℕ)=1),mul_one]
    exact two_at_fifteen
  have dichotomy := mixed (p:=3) (q:=5) (d:=23) formula (by decide) (by decide)
    (by decide) (by decide) (by decide) sign
  refine ⟨sign,base_twenty_three,?_⟩
  rcases dichotomy with ⟨_,_,h⟩|⟨_,_,h⟩ <;> simpa only [base_twenty_three,zero_mul] using h

end PrimeFactors.AdaptiveThreeSquareTwist
