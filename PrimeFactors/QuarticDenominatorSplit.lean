import PrimeFactors.LeastPrimitiveQuarticDenominator
import Mathlib.Algebra.GCDMonoid.Basic

/-! The denominator of a supplied primitive quartic representation splits
between its two coprime integer factors. -/
namespace PrimeFactors.QuarticDenominatorSplit

open RecognizingQuarticProducts

private theorem odd_numerator {a b d n : ℕ} (prim : a.Coprime b)
    (odd : Odd n) (point : d^4*n=a^4+4*b^4) : Odd a := by
  have den := LeastPrimitiveQuarticDenominator.two_not_dvd prim point
  have dodd : Odd d := Nat.odd_iff.mpr (by omega)
  have h := (dodd.pow (n := 4)).mul odd
  rw [point] at h
  have parity := Nat.odd_iff.mp h
  have fourth : a^4%2=a%2 := by
    rcases Nat.mod_two_eq_zero_or_one a with h|h <;> rw [Nat.pow_mod,h]
  exact Nat.odd_iff.mpr (by omega)

/-- The two integer Sophie Germain factors of primitive coordinates with odd
first coordinate are coprime. -/
theorem factors_coprime {a b : ℕ} (prim : a.Coprime b) (ao : Odd a) :
    (factors a b).1.Coprime (factors a b).2 := by
  have no_sub : 2*a*b≤a^2+2*b^2 := by have h := two_mul_le_add_sq a b; omega
  have diff : (factors a b).2=(factors a b).1+4*a*b := by
    dsimp [factors]
    nlinarith only [Nat.sub_add_cancel no_sub]
  apply Nat.coprime_of_dvd
  intro l lp da db
  have delta : l∣4*a*b := (Nat.dvd_add_iff_right da).mpr (diff ▸ db)
  change l∣a^2+2*b^2+2*a*b at db
  have not2 : ¬l∣2 := by
    intro div
    have eq := ((Nat.dvd_prime Nat.prime_two).mp div).resolve_left lp.ne_one
    subst l
    have aodd := Nat.odd_iff.mp (ao.pow (n := 2))
    rw [show 2*a*b=2*(a*b) by ring] at db
    omega
  have not4 : ¬l∣4 := fun div => not2 (lp.dvd_of_dvd_pow (show l∣2^2 from div))
  rcases lp.dvd_mul.mp delta with left|lb
  · have la := (lp.dvd_mul.mp left).resolve_left not4
    have cross : l∣2*a*b := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right la 2) b
    have base := (Nat.dvd_add_iff_left cross).mpr db
    have bs := (Nat.dvd_add_iff_right (la.trans (dvd_pow_self a (by decide : 2≠0)))).mpr base
    have lb := lp.dvd_of_dvd_pow ((lp.dvd_mul.mp bs).resolve_left not2)
    exact lp.not_dvd_one (prim.gcd_eq_one ▸ Nat.dvd_gcd la lb)
  · have base := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right lb (2*a))).mpr db
    have bs := dvd_mul_of_dvd_right (lb.trans (dvd_pow_self b (by decide : 2≠0))) 2
    have la := lp.dvd_of_dvd_pow ((Nat.dvd_add_iff_left bs).mpr base)
    exact lp.not_dvd_one (prim.gcd_eq_one ▸ Nat.dvd_gcd la lb)

private theorem opposite {p q A B : ℕ} (pp : p.Prime) (qp : q.Prime)
    (cop : A.Coprime B) (ap : 0<A) (bp : 0<B) (smallA : A<p*q) (smallB : B<p*q)
    (both : p*q∣A*B) : (p∣A ∧ q∣B) ∨ (q∣A ∧ p∣B) := by
  have no_side {X Y : ℕ} (xy : X.Coprime Y) (pos : 0<X) (small : X<p*q)
      (div : p*q∣X*Y) (px : p∣X) (qx : q∣X) : False := by
    have cp : (p*q).Coprime Y :=
      Nat.coprime_mul_iff_left.mpr ⟨xy.of_dvd_left px,xy.of_dvd_left qx⟩
    exact Nat.not_dvd_of_pos_of_lt pos small (cp.dvd_of_dvd_mul_right div)
  have qs := qp.dvd_mul.mp ((dvd_mul_left q p).trans both)
  rcases pp.dvd_mul.mp ((dvd_mul_right p q).trans both) with pa|pb
  · exact Or.inl ⟨pa,qs.resolve_left (no_side cop ap smallA both pa)⟩
  · have rev : p*q∣B*A := by rwa [Nat.mul_comm B A]
    exact Or.inr ⟨qs.resolve_right (no_side cop.symm bp smallB rev pb),pb⟩

private theorem fourth_coefficients {p q A B d : ℕ} (pp : 0<p) (qp : 0<q)
    (cop : A.Coprime B) (prod : A*B=d^4*(p*q)) (pa : p∣A) (qb : q∣B) :
    ∃ u v : ℕ, d=u*v ∧ u.Coprime v ∧ A=u^4*p ∧ B=v^4*q := by
  obtain ⟨c,rfl⟩ := pa
  obtain ⟨l,rfl⟩ := qb
  have cl : c.Coprime l := cop.of_dvd (dvd_mul_left c p) (dvd_mul_left l q)
  have rel : c*l=d^4 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos pp qp) (calc
    (p*q)*(c*l) = (p*c)*(q*l) := by ring
    _ = d^4*(p*q) := prod
    _ = (p*q)*d^4 := Nat.mul_comm _ _)
  obtain ⟨u,hu⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr cl.gcd_eq_one) rel
  obtain ⟨v,hv⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr cl.symm.gcd_eq_one)
    (show l*c=d^4 by rwa [Nat.mul_comm l c])
  have split : d=u*v := (Nat.pow_left_inj (by decide : 4≠0)).mp (by rw [←rel,hu,hv,mul_pow])
  subst c l
  exact ⟨u,v,split,cl.of_dvd (dvd_pow_self u (by decide : 4≠0))
    (dvd_pow_self v (by decide : 4≠0)),Nat.mul_comm _ _,Nat.mul_comm _ _⟩

private theorem size_bounds {U V r s : ℕ} (rp : 0<r) (sp : 0<s)
    (rs : r≤2*s) (sr : s≤2*r) (order : U*r≤V*s) (ratio : V*s<6*(U*r)) :
    U≤12*V ∧ V≤12*U := by
  have a : U*r≤(2*V)*r := order.trans ((Nat.mul_le_mul_left V sr).trans_eq (by ring))
  have b : V*s≤(12*U)*s := ratio.le.trans (calc
    6*(U*r) ≤ 6*(U*(2*s)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ rs)
    _ = (12*U)*s := by ring)
  have ua := Nat.le_of_mul_le_mul_right a rp
  exact ⟨by omega,Nat.le_of_mul_le_mul_right b sp⟩

/-- The two coprime denominator parts contribute exact fourth powers to
opposite factors. Their fourth powers are within a factor of twelve. -/
theorem partition {p q a b d : ℕ} (pp : p.Prime) (qp : q.Prime)
    (po : Odd p) (qo : Odd q) (ordered : p≤q) (balanced : q≤2*p)
    (bp : 0<b) (prim : a.Coprime b) (point : d^4*(p*q)=a^4+4*b^4)
    (size : 6*d^4≤p*q) :
    ∃ u v : ℕ, d=u*v ∧ u.Coprime v ∧
      (((factors a b).1=u^4*p ∧ (factors a b).2=v^4*q) ∨
       ((factors a b).1=u^4*q ∧ (factors a b).2=v^4*p)) ∧
      u^4≤12*v^4 ∧ v^4≤12*u^4 := by
  let A := (factors a b).1
  let B := (factors a b).2
  have cop : A.Coprime B := factors_coprime prim (odd_numerator prim (po.mul qo) point)
  have prod : A*B=d^4*(p*q) := (factor_product a b).trans point.symm
  have ratio : B<6*A := RationalQuarticFactorPair.ratio bp
  have ord : A≤B := by dsimp [A,B,factors]; omega
  have bpos : 0<B := by dsimp [B,factors]; positivity
  have apos : 0<A := by omega
  have sq := Nat.mul_lt_mul_of_pos_right ratio bpos
  have hi : B^2<(p*q)^2 := calc
    _ < 6*(A*B) := by nlinarith only [sq]
    _ = (6*d^4)*(p*q) := by rw [prod]; ring
    _ ≤ _ := by simpa only [pow_two] using Nat.mul_le_mul_right (p*q) size
  have bsmall := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp hi
  have both : p*q∣A*B := prod ▸ dvd_mul_left (p*q) (d^4)
  rcases opposite pp qp cop apos bpos (ord.trans_lt bsmall) bsmall both with h|h
  · obtain ⟨u,v,split,uv,left,right⟩ := fourth_coefficients pp.pos qp.pos cop prod h.1 h.2
    rw [left,right] at ord ratio
    exact ⟨u,v,split,uv,Or.inl ⟨left,right⟩,size_bounds pp.pos qp.pos (by omega) balanced ord ratio⟩
  · have rev : A*B=d^4*(q*p) := by rwa [Nat.mul_comm q p]
    obtain ⟨u,v,split,uv,left,right⟩ := fourth_coefficients qp.pos pp.pos cop rev h.1 h.2
    rw [left,right] at ord ratio
    exact ⟨u,v,split,uv,Or.inr ⟨left,right⟩,size_bounds qp.pos pp.pos balanced (by omega) ord ratio⟩

end PrimeFactors.QuarticDenominatorSplit
