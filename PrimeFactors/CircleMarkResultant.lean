import PrimeFactors.CircleMarkCrossTargets

/-! Eliminating a starting coordinate from two shifted circle marks.
The shift must be a unit. A known square multiplier of the target preserves
its local quadratic signs, so the remaining count is a public gcd expression. -/
namespace PrimeFactors.CircleMarkResultant

open Finset CircleBranchCount CircleMarkCrossTargets
open scoped Classical

/-- The resultant of the two monic quadratics in the starting coordinate. -/
def resultant {R : Type*} [CommRing R] (a b h : R) : R := (b-a-h^2)^2-4*h^2*a

/-- One gcd with the product, on integer representatives. -/
noncomputable def commonGcd (n : ℕ) (a b h : ℤ) : ℕ := n.gcd (resultant a b h).natAbs

/-- The difference of the two square equations is linear. At a nonzero
shift in odd characteristic this fixes the only possible starting point. -/
theorem field_iff {F : Type*} [Field F] {a b h x : F} (two : (2:F)≠0) (nz : h≠0) :
    x^2=a ∧ (x+h)^2=b ↔ x=(b-a-h^2)/(2*h) ∧ resultant a b h=0 := by
  have denom := mul_ne_zero two nz
  constructor
  · rintro ⟨left,right⟩
    have linear : x*(2*h)=b-a-h^2 := by linear_combination right-left
    refine ⟨(eq_div_iff denom).mpr linear,?_⟩
    rw [resultant,←linear]
    linear_combination 4*h^2*left
  · rintro ⟨only,zero⟩
    have linear := (eq_div_iff denom).mp only
    rw [resultant,←linear] at zero
    have scaled : (x^2-a)*(2*h)^2=0 := by linear_combination zero
    have left := sub_eq_zero.mp ((mul_eq_zero.mp scaled).resolve_right (pow_ne_zero 2 denom))
    exact ⟨left,by linear_combination linear+left⟩

private theorem nz_cast {r : ℕ} [rp : Fact r.Prime] {h : ℤ} (cop : h.natAbs.Coprime r) :
    (h:ZMod r)≠0 := by
  rw [ne_eq,ZMod.intCast_zmod_eq_zero_iff_dvd,Int.natCast_dvd]
  exact rp.out.coprime_iff_not_dvd.mp cop.symm

private theorem vanishes (r : ℕ) (a b h : ℤ) :
    r∣(resultant a b h).natAbs ↔ resultant (a:ZMod r) (b:ZMod r) (h:ZMod r)=0 := by
  rw [← Int.natCast_dvd,←ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp [resultant]

/-- Counts the actual translated intersection over one prime field. -/
theorem local_count {p : ℕ} [Fact p.Prime] (odd : p≠2) (a b h : ℤ)
    (unit : h.natAbs.Coprime p) :
    (cut (roots p a) (roots p b) (h:ZMod p)).card =
      if p∣(resultant a b h).natAbs then 1 else 0 := by
  have two : (2:ZMod p)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  let x0 := ((b:ZMod p)-(a:ZMod p)-(h:ZMod p)^2)/(2*(h:ZMod p))
  split_ifs with dv
  · have zero := (vanishes p a b h).mp dv
    have eq : cut (roots p a) (roots p b) (h:ZMod p) = {x0} := by
      ext x
      simp only [cut, roots, mem_filter, mem_univ, true_and, mem_singleton]
      simp [field_iff two (nz_cast unit),zero,x0]
    simp [eq]
  · have zero := mt (vanishes p a b h).mpr dv
    have eq : cut (roots p a) (roots p b) (h:ZMod p) = ∅ := by
      ext x
      simp only [cut, roots, mem_filter, mem_univ, true_and, not_mem_empty, iff_false]
      simp [field_iff two (nz_cast unit),zero]
    simp [eq]

/-- A nonsquare initial target rules out a local zero of the resultant. -/
theorem nonsquare_misses {q : ℕ} [Fact q.Prime] (odd : q≠2) {a b h : ℤ}
    (negative : legendreSym q a= -1) (unit : h.natAbs.Coprime q) :
    ¬q∣(resultant a b h).natAbs := by
  intro dv
  have two : (2:ZMod q)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have zero := (vanishes q a b h).mp dv
  have solution := (field_iff two (nz_cast unit)).mpr ⟨rfl,zero⟩
  exact (legendreSym.eq_neg_one_iff q).mp negative ((isSquare_iff_exists_sq _).mpr ⟨_,solution.1.symm⟩)

private theorem negative_product {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] {a : ℤ}
    (sp : legendreSym p a=1) (nq : legendreSym q a= -1) : jacobiSym a (p*q)= -1 := by
  rw [jacobiSym.mul_right' a hp.out.ne_zero hq.out.ne_zero,
    ← jacobiSym.legendreSym.to_jacobiSym,← jacobiSym.legendreSym.to_jacobiSym,sp,nq,one_mul]

/-- For two targets square at p and nonsquare at q, divisibility of the
resultant at p determines both the overlap and its public gcd. -/
theorem oriented {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a b h : ℤ} (pa : legendreSym p a=1)
    (pb : legendreSym p b=1) (qa : legendreSym q a= -1) (qb : legendreSym q b= -1)
    (unit : h.natAbs.Coprime (p*q)) :
    (cross (p*q) a b h, commonGcd (p*q) a b h) =
       if p∣(resultant a b h).natAbs then (q,p) else (0,1) := by
  have cp := unit.of_dvd_right (dvd_mul_right p q)
  have cq := unit.of_dvd_right (dvd_mul_left q p)
  have no := nonsquare_misses (b:=b) oq qa cq
  have primec := hq.out.coprime_iff_not_dvd.mpr no
  have count := factor_count ((Nat.coprime_primes hp.out hq.out).mpr diff)
    (negative_product pa qa) (negative_product pb qb) h
  simp [side,pa,pb,qa,qb,local_count op a b h cp] at count
  rw [count]
  split_ifs with dv
  · have g : commonGcd (p*q) a b h=p := by
      rw [commonGcd,Nat.mul_comm]
      exact Nat.gcd_mul_of_coprime_of_dvd primec dv
    simp [g]
  · have g : commonGcd (p*q) a b h=1 :=
      (Nat.coprime_mul_iff_left.mpr ⟨hp.out.coprime_iff_not_dvd.mpr dv,primec⟩).gcd_eq_one
    simp [g]

private theorem oriented_formula {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a b h : ℤ} (pa : legendreSym p a=1)
    (pb : legendreSym p b=1) (qa : legendreSym q a= -1) (qb : legendreSym q b= -1)
    (unit : h.natAbs.Coprime (p*q)) :
    cross (p*q) a b h = if commonGcd (p*q) a b h=1 then 0 else (p*q)/commonGcd (p*q) a b h := by
  have pair := oriented diff op oq pa pb qa qb unit
  split_ifs at pair
  · have c := congrArg Prod.fst pair
    have g := congrArg Prod.snd pair
    simp only [Prod.fst,Prod.snd] at c g
    simp [c,g,hp.out.ne_one,hp.out.pos]
  · have c := congrArg Prod.fst pair
    have g := congrArg Prod.snd pair
    simp only [Prod.fst,Prod.snd] at c g
    simp [c,g]

/-- Same local signs suffice. The formula itself uses only N, the targets and the lag. -/
theorem same_sides {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a b h : ℤ}
    (na : jacobiSym a (p*q)= -1) (nb : jacobiSym b (p*q)= -1)
    (same : legendreSym p a=legendreSym p b) (unit : h.natAbs.Coprime (p*q)) :
    cross (p*q) a b h = if commonGcd (p*q) a b h=1 then 0 else (p*q)/commonGcd (p*q) a b h := by
  rcases opposite na with A|A <;> rcases opposite nb with B|B
  · exact oriented_formula diff op oq A.1 B.1 A.2 B.2 unit
  · omega
  · omega
  · let P (n : ℕ) : Prop := ∀ nz : NeZero n,
      @cross n nz a b h = if commonGcd n a b h=1 then 0 else n/commonGcd n a b h
    have rev : P (q*p) := fun _ =>
      oriented_formula diff.symm oq op A.2 B.2 A.1 B.1 (by simpa only [Nat.mul_comm q p] using unit)
    exact (Nat.mul_comm q p ▸ rev : P (p*q)) inferInstance

/-- For a known square multiplier the resultant factors over the integers. -/
theorem scaled_resultant (a d h : ℤ) :
    resultant a (a*d^2) h=(h^2-a*(d-1)^2)*(h^2-a*(d+1)^2) := by
  unfold resultant
  ring

/-- A public square multiplier preserves the local signs. The overlap at
a unit lag needs just one gcd and, in the positive case, a division. -/
theorem scaled {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a d h : ℤ} (na : jacobiSym a (p*q)= -1)
    (du : d.natAbs.Coprime (p*q)) (unit : h.natAbs.Coprime (p*q)) :
    let g := (p*q).gcd ((h^2-a*(d-1)^2)*(h^2-a*(d+1)^2)).natAbs
    cross (p*q) a (a*d^2) h = if g=1 then 0 else (p*q)/g := by
  have pD := legendreSym.sq_one' p (nz_cast (h:=d) (du.of_dvd_right (dvd_mul_right p q)))
  have qD := legendreSym.sq_one' q (nz_cast (h:=d) (du.of_dvd_right (dvd_mul_left q p)))
  have P : legendreSym p (a*d^2)=legendreSym p a := by rw [legendreSym.mul,pD,mul_one]
  have Q : legendreSym q (a*d^2)=legendreSym q a := by rw [legendreSym.mul,qD,mul_one]
  have nb : jacobiSym (a*d^2) (p*q)= -1 := by
    rw [jacobiSym.mul_right' _ hp.out.ne_zero hq.out.ne_zero,
      ← jacobiSym.legendreSym.to_jacobiSym,← jacobiSym.legendreSym.to_jacobiSym,P,Q]
    simpa only [jacobiSym.mul_right' a hp.out.ne_zero hq.out.ne_zero,
      ← jacobiSym.legendreSym.to_jacobiSym] using na
  simpa only [commonGcd,scaled_resultant] using same_sides diff op oq na nb P.symm unit

/-- Swapping the targets does not change the discriminant. -/
theorem resultant_comm {R : Type*} [CommRing R] (a b h : R) :
    resultant a b h=resultant b a h := by
  unfold resultant
  ring

/-- Opposite local orientations give the unit gcd at every unit lag.
Thus a gcd of one is compatible with the four-point intersection. -/
theorem opposite_gcd {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (op : p≠2) (oq : q≠2) {a b h : ℤ} (na : jacobiSym a (p*q)= -1)
    (nb : jacobiSym b (p*q)= -1) (different : legendreSym p a≠legendreSym p b)
    (unit : h.natAbs.Coprime (p*q)) : commonGcd (p*q) a b h=1 := by
  have miss (r : ℕ) [Fact r.Prime] (odd : r≠2) (ur : h.natAbs.Coprime r)
      (sign : legendreSym r a= -1 ∨ legendreSym r b= -1) : r.Coprime (resultant a b h).natAbs := by
    apply (Fact.out : r.Prime).coprime_iff_not_dvd.mpr
    rcases sign with neg|neg
    · exact nonsquare_misses odd neg ur
    · rw [resultant_comm]
      exact nonsquare_misses odd neg ur
  apply (Nat.coprime_mul_iff_left.mpr ?_).gcd_eq_one
  rcases opposite na with A|A <;> rcases opposite nb with B|B
  · exact (different (A.1.trans B.1.symm)).elim
  · exact ⟨miss p op (unit.of_dvd_right (dvd_mul_right p q)) (.inr B.1),
      miss q oq (unit.of_dvd_right (dvd_mul_left q p)) (.inl A.2)⟩
  · exact ⟨miss p op (unit.of_dvd_right (dvd_mul_right p q)) (.inl A.1),
      miss q oq (unit.of_dvd_right (dvd_mul_left q p)) (.inr B.2)⟩
  · exact (different (A.1.trans B.1.symm)).elim

/-- Changing target 2 by the square multiplier 4 gives an eleven-point
intersection at lag 3 and disjoint mark sets at lag 1. -/
theorem seventy_seven : cross 77 2 8 3=11 ∧ cross 77 2 8 1=0 ∧
    commonGcd 77 2 8 3=7 ∧ commonGcd 77 2 8 1=1 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have control (h : ℤ) := scaled (p:=7) (q:=11) (a:=2) (d:=2) (h:=h) (by decide)
    (by decide) (by decide) (by norm_num) (by decide)
  refine ⟨(control 3 (by decide)).trans ?_,(control 1 (by decide)).trans ?_,?_,?_⟩ <;> decide

end PrimeFactors.CircleMarkResultant
