import PrimeFactors.RecognizingQuarticProducts
import PrimeFactors.FactorSum

/-! A supplied rational point on the quartic gives an integer factor pair of
a semiprime when its denominator is small enough. The hypothesis supplies all
three coordinates. No construction of a rational point from N is assumed. -/
namespace PrimeFactors.RationalQuarticFactorPair

open RecognizingQuarticProducts

/-- The two integer factors in the quartic identity always differ by a ratio
strictly below six. The strict inequality holds even for very unequal coordinates. -/
theorem ratio {a b : ℕ} (pos : 0<b) :
    (factors a b).2<6*(factors a b).1 := by
  have no_sub : 2*a*b≤a^2+2*b^2 := by have h := two_mul_le_add_sq a b; omega
  have ab := Nat.sub_add_cancel no_sub
  have apos : (0:ℤ)<b^2 := by positivity
  zify [factors,no_sub] at *
  nlinarith only [sq_nonneg (5*(a:ℤ)-7*(b:ℤ)),apos]

private theorem small_factor {p q A B : ℕ} (pp : p.Prime) (qp : q.Prime)
    (distinct : p≠q) (both : p*q∣A*B) (below : A<p*q) (below' : B<p*q)
    (apos : 0<A) (bpos : 0<B) :
    (p∣A ∧ q∣B ∧ ¬q∣A ∧ ¬p∣B) ∨ (q∣A ∧ p∣B ∧ ¬p∣A ∧ ¬q∣B) := by
  have cop := (Nat.coprime_primes pp qp).mpr distinct
  have no_a (l : p∣A) (r : q∣A) := (Nat.not_dvd_of_pos_of_lt apos below) (cop.mul_dvd_of_dvd_of_dvd l r)
  have no_b (l : p∣B) (r : q∣B) := (Nat.not_dvd_of_pos_of_lt bpos below') (cop.mul_dvd_of_dvd_of_dvd l r)
  have pEither := pp.dvd_mul.mp ((dvd_mul_right p q).trans both)
  have qEither := qp.dvd_mul.mp ((dvd_mul_left q p).trans both)
  rcases pEither with pa|pb
  · have qb := qEither.resolve_left (no_a pa)
    exact Or.inl ⟨pa,qb,no_a pa,fun h => no_b h qb⟩
  · have qa := qEither.resolve_right (no_b pb)
    exact Or.inr ⟨qa,pb,fun h => no_a h qa,no_b pb⟩

private theorem gcd_eq {p q A : ℕ} (qp : q.Prime) (left : p∣A) (right : ¬q∣A) :
    Nat.gcd (p*q) A=p := by
  obtain ⟨k,rfl⟩ := left
  have cop := qp.coprime_iff_not_dvd.mpr (fun h => right (h.trans (dvd_mul_left k p)))
  rw [Nat.gcd_mul_left,cop.gcd_eq_one,Nat.mul_one]

/-- A rational certificate N=(a/d)^4+4(b/d)^4 yields the unordered prime
pair via two gcds. Only the proof needs to name the unknown p and q. -/
theorem split {p q a b d : ℕ} (pp : p.Prime) (qp : q.Prime) (distinct : p≠q)
    (pos : 0<b) (point : d^4*(p*q)=a^4+4*b^4)
    (size : 6*d^4≤p*q) :
    let n := p*q
    let ab := factors a b
    (Nat.gcd n ab.1=p ∧ Nat.gcd n ab.2=q) ∨ (Nat.gcd n ab.1=q ∧ Nat.gcd n ab.2=p) := by
  let A := (factors a b).1
  let B := (factors a b).2
  let n := p*q
  have prod : A*B=d^4*n := (factor_product a b).trans point.symm
  have lt : B<6*A := ratio pos
  have ord : A≤B := by dsimp [A,B,factors]; omega
  have bp : 0<B := by dsimp [B,factors]; positivity
  have ap : 0<A := by omega
  have sq := Nat.mul_lt_mul_of_pos_right lt bp
  have hi : B^2<n^2 := calc
    _ < 6*(A*B) := by nlinarith only [sq]
    _ = (6*d^4)*n := by rw [prod]; ring
    _ ≤ _ := by simpa only [pow_two] using Nat.mul_le_mul_right n size
  have bsmall := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp hi
  have both : n∣A*B := prod ▸ dvd_mul_left n (d^4)
  change (Nat.gcd n A=p ∧ Nat.gcd n B=q) ∨ (Nat.gcd n A=q ∧ Nat.gcd n B=p)
  rcases small_factor pp qp distinct both (ord.trans_lt bsmall) bsmall ap bp with h|h
  · exact Or.inl ⟨gcd_eq qp h.1 h.2.2.1,by simpa [n,Nat.mul_comm q p] using gcd_eq pp h.2.1 h.2.2.2⟩
  · exact Or.inr ⟨by simpa [n,Nat.mul_comm q p] using gcd_eq pp h.1 h.2.2.1,gcd_eq qp h.2.1 h.2.2.2⟩

end PrimeFactors.RationalQuarticFactorPair
