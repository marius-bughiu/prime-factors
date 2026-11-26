import PrimeFactors.GeometricPrecisionReadout

/-! A single scalar in direction −1 measures the local multiplicities of a
geometric product up to the chosen public precision, for any finite label set. -/

namespace PrimeFactors.GeometricMultiplicityProbe

open Finset Polynomial

/-- Original matches, before the public lift and perturbation. -/
noncomputable def localHits (I : Finset ℕ) (p E : ℕ) (g : ℤ) : Finset ℕ :=
  I.filter fun i => g^i ≡ g^E [ZMOD (p:ℤ)]

/-- The public scalar whose representative is computed modulo N^(R+1). -/
noncomputable def reading (I : Finset ℕ) (n E : ℕ) (g : ℤ) : ℤ :=
  let G := g^n
  ∏ i∈I, (G^E*(1-(n:ℤ))-(G*(1+n))^i)

private theorem leading {p n E : ℕ} (hp : p.Prime) (cop : n.Coprime (p-1))
    (I : Finset ℕ) (room : ∀ i∈I, i+1<p) (g : ℤ) (base : (g:ZMod p)≠0) :
    let G := g^n
    (((GeometricReadingLift.product I (G^E) G (-1)).coeff (localHits I p E g).card : ℤ)
      : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let G := g^n
  let Y := G^E
  let H := localHits I p E g
  let cast := Int.castRingHom (ZMod p)
  have sub : H⊆I := filter_subset _ _
  have same (i : ℕ) (mem : i∈I) : i∈H ↔ (G:ZMod p)^i=(Y:ZMod p) := by
    have e := GeometricPrecisionReadout.same_hits hp cop base 1 i E
    simp only [pow_one] at e
    change (i∈I.filter _) ↔ _
    rw [mem_filter,and_iff_right mem,←e,← ZMod.intCast_eq_intCast_iff]
    simp only [G,Y,Int.cast_pow]
  have nz : (Y:ZMod p)≠0 := by
    simpa only [Y,G,Int.cast_pow] using pow_ne_zero E (pow_ne_zero n base)
  have outside : ∀ i∈I\H, (Y:ZMod p)-(G:ZMod p)^i≠0 := by
    intro i hi eq
    exact (mem_sdiff.mp hi).2 ((same i (mem_sdiff.mp hi).1).mpr (sub_eq_zero.mp eq).symm)
  have avoid : ∀ i∈H, (-1:ZMod p)-(i:ZMod p)≠0 := by
    intro i hi eq
    have z : ((i+1:ℕ):ZMod p)=0 := by
      rw [Nat.cast_add,Nat.cast_one,←sub_eq_zero.mp eq,neg_add_cancel]
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (room i (sub hi)))
      ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp z)
  change cast ((GeometricReadingLift.product I Y G (-1)).coeff H.card)≠0
  rw [←coeff_map,GeometricPrecisionReadout.map_product]
  simp only [map_neg,map_one,GeometricReadingLift.product]
  rw [show cast Y=(Y:ZMod p) from rfl,show cast G=(G:ZMod p) from rfl,
    GeometricMatchMoments.directional_reading sub _ _ _ (fun i hi => (same i (sub hi)).mp hi)]
  exact mul_ne_zero (mul_ne_zero (prod_ne_zero_iff.mpr outside) (pow_ne_zero _ nz))
    (prod_ne_zero_iff.mpr avoid)

private theorem divisibility_transport {v w d : ℤ} (h : v ≡ w [ZMOD d]) : d∣v ↔ d∣w := by
  rw [←Int.modEq_zero_iff_dvd,←Int.modEq_zero_iff_dvd]
  exact ⟨h.symm.trans,h.trans⟩

/-- Exact local order of the untruncated scalar, even when the match count is zero. -/
private theorem exact_order {p q E : ℕ} (hp : p.Prime) (cop : (p*q).Coprime (p-1))
    (unitQ : ¬p∣q) (I : Finset ℕ) (room : ∀ i∈I,i+1<p) (g : ℤ) (base : (g:ZMod p)≠0) :
    let r := (localHits I p E g).card
    (p:ℤ)^r∣reading I (p*q) E g ∧ ¬(p:ℤ)^(r+1)∣reading I (p*q) E g := by
  letI : Fact p.Prime := ⟨hp⟩
  let n := p*q
  let G := g^n
  let Y := G^E
  let H := localHits I p E g
  let f := GeometricMatchMoments.directionalFactor Y G (-1)
  let c := (GeometricReadingLift.product I Y G (-1)).coeff H.card
  have sub : H⊆I := filter_subset _ _
  have high (i : ℕ) (hi : i∈H) : (p:ℤ)^2∣(f i).coeff 0 := by
    have e : g^i ≡ g^E [ZMOD (p:ℤ)] := (mem_filter.mp hi).2
    have h := GeometricPrincipalLift.lift (dvd_mul_right p q) 1 e
    have swap (j : ℕ) : G^j=(g^j)^n := by dsimp [G]; rw [←pow_mul, ←pow_mul,mul_comm]
    simpa only [f,GeometricMatchMoments.directionalFactor,coeff_zero_eq_eval_zero,eval_sub,
      eval_add,eval_mul,eval_C,eval_X,eval_pow,eval_one,mul_zero,add_zero,one_pow,mul_one,
      Y,swap,pow_one] using h.dvd
  have eq := GeometricLiftedDigit.local_digit hp.pos (q:ℤ) sub f high
  change (GeometricReadingLift.product I Y G (-1)).eval ((p:ℤ)*q) ≡
    ((p:ℤ)*q)^H.card*c [ZMOD (p:ℤ)^(H.card+1)] at eq
  rw [GeometricReadingLift.eval_product] at eq
  have eval : reading I n E g ≡ ((p:ℤ)*q)^H.card*c [ZMOD (p:ℤ)^(H.card+1)] := by
    simpa only [reading,n,Nat.cast_mul,neg_one_mul,sub_eq_add_neg,Y,G] using eq
  have nz : (c:ZMod p)≠0 := leading hp cop I room g base
  have qnz : (q:ZMod p)≠0 := fun h => unitQ ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h)
  have unit : ¬(p:ℤ)∣(q:ℤ)^H.card*c := by
    intro divides
    have z := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr divides
    push_cast at z
    exact mul_ne_zero (pow_ne_zero _ qnz) nz z
  obtain ⟨t,ht⟩ := Int.modEq_iff_add_fac.mp eval.symm
  have eqv : reading I n E g=(p:ℤ)^H.card*((q:ℤ)^H.card*c+p*t) := by
    rw [ht,mul_pow,pow_succ]; ring
  change _∣reading I n E g ∧ ¬_∣reading I n E g
  rw [eqv]
  refine ⟨dvd_mul_right ..,?_⟩
  rw [pow_succ,mul_dvd_mul_iff_left (pow_ne_zero _ (show (p:ℤ)≠0 by exact_mod_cast hp.ne_zero))]
  intro h
  exact unit ((dvd_add_left (dvd_mul_right ..)).mp h)

/-- Every locally observable power-divisibility test agrees with the count of
the original matches. No count or witness subset is supplied to the reading. -/
theorem local_powers {p q E R : ℕ} (hp : p.Prime) (cop : (p*q).Coprime (p-1))
    (unitQ : ¬p∣q) (I : Finset ℕ) (room : ∀ i∈I,i+1<p) (g v : ℤ) (base : (g:ZMod p)≠0)
    (sample : v ≡ reading I (p*q) E g [ZMOD ((p:ℤ)*q)^(R+1)]) :
    ∀ j≤R+1, (p:ℤ)^j∣v ↔ j≤(localHits I p E g).card := by
  obtain ⟨low,high⟩ := exact_order hp cop unitQ I room g base (E:=E)
  intro j hj
  have modulus := (pow_dvd_pow (p:ℤ) hj).trans (pow_dvd_pow_of_dvd (dvd_mul_right (p:ℤ) (q:ℤ)) (R+1))
  rw [divisibility_transport (sample.of_dvd modulus)]
  exact ⟨fun h => le_of_not_gt (fun bad => high ((pow_dvd_pow _ (by omega)).trans h)),
    fun h => (pow_dvd_pow _ h).trans low⟩

private theorem digit_dvd {a b s : ℕ} {v : ℤ} (apos : 0<a) (cop : a.Coprime b)
    (divides : ((a:ℤ)*b)^s∣v) :
    a ∣ (v / ((a:ℤ)*b)^s).natAbs ↔ (a:ℤ)^(s+1)∣v := by
  let u := v / ((a:ℤ)*b)^s
  have eq : v=(a:ℤ)^s*((b:ℤ)^s*u) := by
    rw [←mul_assoc,←mul_pow]
    exact (Int.mul_ediv_cancel' divides).symm
  have integer : IsCoprime (a:ℤ) (b:ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using cop)
  change a∣u.natAbs ↔ _
  rw [←Int.natCast_dvd,eq,pow_succ,mul_dvd_mul_iff_left
    (pow_ne_zero _ (show (a:ℤ)≠0 by exact_mod_cast apos.ne'))]
  exact ⟨fun h => dvd_mul_of_dvd_right h _,integer.pow_right.dvd_of_dvd_mul_left⟩

/-- Classify a digit's gcd from its two local divisibility tests. -/
private theorem digit_gcd {p q d : ℕ} (hp : p.Prime) (hq : q.Prime) (cop : p.Coprime q)
    {P Q : Prop} [Decidable P] [Decidable Q] (left : p∣d ↔ P) (right : q∣d ↔ Q) :
    (p*q).gcd d = (if P then p else 1)*(if Q then q else 1) := by
  by_cases lp : P <;> by_cases lq : Q <;> simp only [lp,lq,if_true,if_false,mul_one,one_mul]
  · exact Nat.gcd_eq_left (cop.mul_dvd_of_dvd_of_dvd (left.mpr lp) (right.mpr lq))
  · rw [Nat.mul_comm p q]
    exact Nat.gcd_mul_of_coprime_of_dvd (hq.coprime_iff_not_dvd.mpr (mt right.mp lq)) (left.mpr lp)
  · exact Nat.gcd_mul_of_coprime_of_dvd (hp.coprime_iff_not_dvd.mpr (mt left.mp lp)) (right.mpr lq)
  · exact (Nat.coprime_mul_iff_left.mpr ⟨hp.coprime_iff_not_dvd.mpr (mt left.mp lp),
      hq.coprime_iff_not_dvd.mpr (mt right.mp lq)⟩).gcd_eq_one

/-- Successively divide a single negative-direction representative by N. At
each observable order below both counts the gcd is N. At the smaller count it
is the higher-count prime, or 1 when the counts agree. If both counts exceed
the cap the entire representative is zero modulo N^(R+1). -/
theorem automatic {p q E R : ℕ} (hp : p.Prime) (hq : q.Prime) (po : Odd p) (qo : Odd q)
    (lt : p<q) (balance : q≤2*p) (I : Finset ℕ) (room : ∀ i∈I,i+1<p) (g v : ℤ)
    (gp : (g:ZMod p)≠0) (gq : (g:ZMod q)≠0)
    (sample : v ≡ reading I (p*q) E g [ZMOD ((p:ℤ)*q)^(R+1)]) :
    let rp := (localHits I p E g).card
    let rq := (localHits I q E g).card
    let N := (p:ℤ)*q
    (∀ j≤R+1, N^j∣v ↔ j≤min rp rq) ∧
    (∀ s≤R, s≤min rp rq → (p*q).gcd (v/N^s).natAbs =
      (if s<rp then p else 1)*(if s<rq then q else 1)) := by
  have cop := (Nat.coprime_primes hp hq).mpr lt.ne
  have group := GeometricPrincipalLift.balanced_coprime hp hq po qo lt balance
  have lp := local_powers hp group.1 (hp.coprime_iff_not_dvd.mp cop)
    I room g v gp sample
  have lq := local_powers (p:=q) (q:=p) hq (by simpa only [Nat.mul_comm q p] using group.2)
    (hq.coprime_iff_not_dvd.mp cop.symm) I (fun i hi => (room i hi).trans lt) g v gq
    (E:=E) (R:=R) (by simpa only [Nat.mul_comm q p,mul_comm (q:ℤ) (p:ℤ)] using sample)
  have integer : IsCoprime (p:ℤ) (q:ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using cop)
  have both (j : ℕ) (hj : j≤R+1) :
      ((p:ℤ)*q)^j∣v ↔ j≤min (localHits I p E g).card (localHits I q E g).card := by
    rw [mul_pow,le_min_iff,←lp j hj,←lq j hj]
    exact ⟨fun h => ⟨(dvd_mul_right ..).trans h,(dvd_mul_left ..).trans h⟩,
      fun ⟨a,b⟩ => integer.pow_left.pow_right.mul_dvd a b⟩
  refine ⟨both,?_⟩
  intro s hs before
  have div := (both s (by omega)).mpr before
  apply digit_gcd hp hq cop
  · exact (digit_dvd hp.pos cop div).trans (lp (s+1) (by omega))
  · have alt := digit_dvd (s:=s) hq.pos cop.symm (v:=v) (by simpa only [mul_comm (q:ℤ) (p:ℤ)] using div)
    rw [mul_comm (q:ℤ) (p:ℤ)] at alt
    exact alt.trans (lq (s+1) (by omega))

end PrimeFactors.GeometricMultiplicityProbe
