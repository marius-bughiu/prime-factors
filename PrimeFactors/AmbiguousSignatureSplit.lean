import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace PrimeFactors.AmbiguousSignatureSplit

/-- A nonempty bucket's count and first moment give a single annihilating exponent;
the finite index set allows repeated labels. -/
theorem aggregate {G ι : Type*} [CommGroup G] (g : G) (I : Finset ι)
    (s : ι → ℕ) (target : ℕ) (cap : ∀ i ∈ I, s i ≤ target)
    (pass : ∀ i ∈ I, g^(s i) = g^target) :
    g^(I.card * target - ∑ i ∈ I, s i) = 1 := by
  have sumEq := I.sum_tsub_distrib (f := fun _ => target) (g := s) cap
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id] at sumEq
  rw [← sumEq, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_eq_one
  intro i h
  apply mul_right_cancel (b := g^(s i))
  rw [← pow_add, Nat.sub_add_cancel (cap i h), one_mul, pass i h]

/-- For a base killed by 2^f times an odd u, one level of the public squaring
chain equals its Legendre symbol. A prime with p−1=2^(i+1)r, r odd, determines the level. -/
theorem local_sign {p : ℕ} [Fact p.Prime] {a i r f u : ℕ}
    (shape : p = 2*(2^i*r)+1) (ro : Odd r) (uo : Odd u)
    (unit : (a : ZMod p) ≠ 0) (kill : (a : ZMod p)^(2^f*u)=1) :
    (a : ZMod p)^(u*2^i) = (legendreSym p (a:ℤ) : ZMod p) := by
  let y := (a : ZMod p)^(u*2^i)
  have half : p/2=2^i*r := by omega
  have yr : y^r = (legendreSym p (a:ℤ) : ZMod p)^u := by
    rw [legendreSym.eq_pow, half, Int.cast_natCast]
    dsimp [y]; rw [← pow_mul, ← pow_mul]; congr 1; ac_rfl
  have fermat := ZMod.pow_card_sub_one_eq_one unit
  have yr2 : (y^2)^r=1 := by
    calc
      _ = ((a:ZMod p)^(p-1))^u := by
        dsimp [y]; rw [← pow_mul,← pow_mul,← pow_mul,show p-1=2*(2^i*r) by omega]; congr 1; ac_rfl
      _ = 1 := by rw [fermat,one_pow]
  have yf : (y^2)^(2^f)=1 := by
    calc
      _ = ((a:ZMod p)^(2^f*u))^(2^i*2) := by
        dsimp [y]; rw [← pow_mul,← pow_mul,← pow_mul]; congr 1; ac_rfl
      _ = 1 := by rw [kill,one_pow]
  have square := pow_gcd_eq_one (y^2) yr2 yf
  rw [(ro.coprime_two_right.pow_right f).gcd_eq_one,pow_one] at square
  obtain ⟨j,hj⟩ := ro
  rw [hj, pow_add, pow_mul, square, one_pow, pow_one, one_mul] at yr
  rcases legendreSym.eq_one_or_neg_one p (by simpa using unit : ((a:ℤ):ZMod p)≠0) with pos|neg
  · simpa [pos] using yr
  · simpa [neg,uo.neg_one_pow] using yr

private theorem project_power {n p a z : ℕ} [NeZero n] (dv : p∣n) :
    ((((a : ZMod n)^z).val : ℕ) : ZMod p) = (a : ZMod p)^z := by
  simpa only [map_natCast, map_pow] using
    congrArg (ZMod.castHom dv (ZMod p)) (ZMod.natCast_zmod_val ((a:ZMod n)^z))

private theorem project_one {n p a z : ℕ} (dv : p∣n) (h : (a : ZMod n)^z=1) :
    (a : ZMod p)^z=1 := by
  simpa only [map_natCast,map_pow,map_one] using congrArg (ZMod.castHom dv (ZMod p)) h

private theorem factor_gcd {p q x : ℕ} [hp : Fact p.Prime] (big : 2<p)
    (plus : (x : ZMod p)=1) (minus : (x : ZMod q)= -1) : (p*q).gcd (x+1)=q := by
  apply Nat.gcd_mul_of_coprime_of_dvd
  · apply hp.out.coprime_iff_not_dvd.mpr
    intro divides
    have z := (ZMod.natCast_zmod_eq_zero_iff_dvd (x+1) p).mpr divides
    rw [Nat.cast_add,Nat.cast_one,plus,one_add_one_eq_two] at z
    have dv := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).mp z
    exact (not_le_of_gt big) (Nat.le_of_dvd (by decide) dv)
  · apply (ZMod.natCast_zmod_eq_zero_iff_dvd (x+1) q).mp
    simp [Nat.cast_add,minus]

/-- The same level yields opposite local signs at primes with equal predecessor
2-adic valuations. The position i is strictly within the public chain of length f.
The gcd uses only the modular residue and the product. -/
theorem split {p q a i r t f u : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (ps : p=2*(2^i*r)+1) (qs : q=2*(2^i*t)+1) (ro : Odd r) (to' : Odd t)
    (uo : Odd u) (jac : jacobiSym (a:ℤ) (p*q)= -1)
    (kill : (a : ZMod (p*q))^(2^f*u)=1) :
    let x := ((a : ZMod (p*q))^(u*2^i)).val
    i<f ∧ (x : ZMod (p*q))^2=1 ∧ ((p*q).gcd (x+1)=p ∨ (p*q).gcd (x+1)=q) := by
  letI : NeZero (p*q) := ⟨mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
  let x := ((a : ZMod (p*q))^(u*2^i)).val
  have oddBig (z w : ℕ) (sh : z=2*(2^i*w)+1) (oddw : Odd w) : 2<z := by
    have wp : 0<w := by obtain ⟨v,hv⟩ := oddw; omega
    have v := Nat.mul_pos (by positivity : 0<2^i) wp
    omega
  have pb := oddBig p r ps ro
  have qb := oddBig q t qs to'
  have op : (a:ZMod p)^(2^f*u)=1 := project_one (dvd_mul_right p q) kill
  have oq : (a:ZMod q)^(2^f*u)=1 := project_one (dvd_mul_left q p) kill
  have nz {l : ℕ} [Fact l.Prime] (o : (a:ZMod l)^(2^f*u)=1) : (a:ZMod l)≠0 := by
    intro zero
    have up : 0<u := by obtain ⟨v,hv⟩ := uo; omega
    rw [zero,zero_pow (show 2^f*u ≠ 0 by positivity)] at o
    exact zero_ne_one o
  rw [jacobiSym.mul_right' _ hp.out.ne_zero hq.out.ne_zero,
    ← jacobiSym.legendreSym.to_jacobiSym p, ← jacobiSym.legendreSym.to_jacobiSym q] at jac
  have xp : (x:ZMod p)=(legendreSym p (a:ℤ):ZMod p) :=
    (project_power (dvd_mul_right p q)).trans (local_sign ps ro uo (nz op) op)
  have xq : (x:ZMod q)=(legendreSym q (a:ℤ):ZMod q) :=
    (project_power (dvd_mul_left q p)).trans (local_sign qs to' uo (nz oq) oq)
  have level {l : ℕ} [Fact l.Prime] (big : 2<l) (o : (a:ZMod l)^(2^f*u)=1)
      (dv : l∣p*q) (neg : (x:ZMod l)= -1) : i<f := by
    apply Nat.lt_of_not_ge
    intro le
    obtain ⟨k,hk⟩ := Nat.pow_dvd_pow 2 le
    have eq1 : (a : ZMod l)^(u*2^i)=1 := by
      rw [hk,show u*(2^f*k)=(2^f*u)*k by ac_rfl,pow_mul,o,one_pow]
    have opposite := (project_power (a:=a) (z:=u*2^i) dv).trans eq1
    letI : Fact (2<l) := ⟨big⟩
    exact ZMod.neg_one_ne_one (neg.symm.trans opposite)
  have sq (z : ℕ) (l : ℕ) (s : (z:ZMod l)=1 ∨ (z:ZMod l)= -1) : (z:ZMod l)^2=1 := by
    rcases s with h|h <;> simp [h]
  have out (sp : (x:ZMod p)=1 ∨ (x:ZMod p)= -1) (sq' : (x:ZMod q)=1 ∨ (x:ZMod q)= -1) :
      (x:ZMod (p*q))^2=1 := by
    have cp : p.Coprime q := (Nat.coprime_primes hp.out hq.out).mpr (by
      rintro rfl
      have alt := legendreSym.eq_one_or_neg_one p (by simpa using nz op : ((a:ℤ):ZMod p)≠0)
      rcases alt with sign|sign <;> simp [sign] at jac)
    apply (ZMod.chineseRemainder cp).injective
    rw [map_pow,map_natCast,map_one]
    exact Prod.ext (sq x p sp) (sq x q sq')
  rcases legendreSym.eq_one_or_neg_one p (by simpa using nz op : ((a:ℤ):ZMod p)≠0) with pos|neg
  · rw [pos,one_mul] at jac
    rw [pos,Int.cast_one] at xp
    rw [jac,Int.cast_neg,Int.cast_one] at xq
    exact ⟨level qb oq (dvd_mul_left q p) xq,out (.inl xp) (.inr xq),.inr (factor_gcd pb xp xq)⟩
  · rw [neg,neg_one_mul] at jac
    have pos : legendreSym q a=1 := by omega
    rw [neg,Int.cast_neg,Int.cast_one] at xp
    rw [pos,Int.cast_one] at xq
    exact ⟨level pb op (dvd_mul_right p q) xp,out (.inr xp) (.inl xq),
      .inl (by simpa only [Nat.mul_comm q p] using factor_gcd qb xq xp)⟩

/-- These are precisely the local tests at 4, 3 and 5 in the example. A residue x
serves as a factor of the public product modulo m if x(s−x)≡N (mod m). -/
def exampleLocal (s : ℕ) : Bool :=
  [4,3,5].all fun m => (List.range m).any fun x => (x*s)%m == (109969+x*x)%m

private theorem period_example (z : ℕ) : (35 : ZMod 109969)^z = 35^(z%12) := by
  have period : (35 : ZMod 109969)^12=1 := by decide +kernel
  calc
    _ = (35 : ZMod 109969)^(z%12+12*(z/12)) := by rw [Nat.mod_add_div]
    _ = _ := by rw [pow_add,pow_mul,period,one_pow,mul_one]

/-- Kernel-checked one-base join. The wrong sum 686 and the true sum 674 survive;
the count and sum of both rows yield a mixed root and its two gcd factors. -/
theorem example_109969 :
    Nat.Prime 277 ∧ Nat.Prime 397 ∧ 277*397=109969 ∧ 277+397=674 ∧
    jacobiSym 35 109969= -1 ∧ Nat.gcd (34*35*36) 109969=1 ∧
    (List.range' 664 40).filter exampleLocal = [670,674,686,694] ∧
    ((List.range' 664 40).filter exampleLocal).filter
      (fun s => ((35 : ZMod 109969)^s == 35^109970)) = [674,686] ∧
    2*109970-(674+686)=218580 ∧ 218580=4*54645 ∧
    (35 : ZMod 109969)^54645=43272 ∧ (43272 : ZMod 109969)^2=23821 ∧
    (23821 : ZMod 109969)^2=1 ∧ Nat.gcd 23820 109969=397 ∧
    Nat.gcd 23822 109969=277 := by
  have localRows : (List.range' 664 40).filter exampleLocal = [670,674,686,694] := by decide +kernel
  refine ⟨by norm_num,by norm_num,by decide,by decide,by norm_num,by decide,
    localRows,?_,by decide,by decide,?_,by decide +kernel,by decide +kernel,by decide,by decide⟩
  · rw [localRows]
    have eqF : (fun s : ℕ => ((35 : ZMod 109969)^s == 35^109970)) =
        (fun s : ℕ => ((35 : ZMod 109969)^(s%12) == 35^(109970%12))) := by
      funext s
      rw [period_example s, period_example 109970]
    rw [eqF]; decide +kernel
  · rw [period_example];decide +kernel

end PrimeFactors.AmbiguousSignatureSplit
