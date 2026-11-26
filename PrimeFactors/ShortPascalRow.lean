import PrimeFactors.NormBatchGCD
import PrimeFactors.Certificate
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Dvd

/-! The prime divisors of a row of Pascal's triangle are bounded by its
row index. A short row ending between the two unknown primes captures just
the smaller one. -/
namespace PrimeFactors.ShortPascalRow

/-- Lower bound on the smaller factor if both belong to [B, 2B). -/
def lower (n B : ℕ) := max B ((n-1)/(2*B-1)+1)

/-- The numerator of this binomial coefficient contains every integer
from the public lower bound to the square root. -/
def entry (n B : ℕ) := n.sqrt.choose (n.sqrt+1-lower n B)

theorem prime_above_row {q u k : ℕ} (hq : q.Prime) (below : u<q) (hk : k≤u) :
    ¬q∣u.choose k := by
  intro dvd
  have fac : q ∣ u.factorial := by
    rw [←Nat.choose_mul_factorial_mul_factorial hk]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left dvd _) _
  exact (not_le_of_gt below) (hq.dvd_factorial.mp fac)

/-- When the row is strictly below twice p, both lower factorials have to
end before p. This characterizes every column that isolates the smaller prime. -/
theorem column_iff {p u k : ℕ} (hp : p.Prime) (hk : k≤u) (hit : p≤u)
    (short : u<2*p) : p∣u.choose k ↔ u-p<k ∧ k<p := by
  constructor
  · intro dvd
    letI : Fact p.Prime := ⟨hp⟩
    have lucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n:=u) (k:=k) (p:=p)
    have rowmod : u%p=u-p := by
      rw [Nat.mod_eq_sub_mod hit, Nat.mod_eq_of_lt (by omega)]
    have rowdiv : u/p=1 := by
      apply Nat.div_eq_of_lt_le <;> omega
    rw [rowmod,rowdiv] at lucas
    by_contra! bad
    by_cases ks : k<p
    · have kl : k≤u-p := by by_contra! h; exact (bad h).not_lt ks
      rw [Nat.mod_eq_of_lt ks, Nat.div_eq_of_lt ks] at lucas
      simp only [Nat.choose_zero_right,mul_one] at lucas
      exact prime_above_row hp (by omega : u-p<p) kl (Nat.dvd_of_mod_eq_zero (Eq.trans (Eq.symm lucas) (Nat.mod_eq_zero_of_dvd dvd)))
    · have km : k%p=k-p := by rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      have kd : k/p=1 := by apply Nat.div_eq_of_lt_le <;> omega
      rw [km,kd] at lucas
      simp only [Nat.choose_self,mul_one] at lucas
      exact prime_above_row hp (by omega : u-p<p) (by omega : k-p≤u-p)
        (Nat.dvd_of_mod_eq_zero (Eq.trans (Eq.symm lucas) (Nat.mod_eq_zero_of_dvd dvd)))
  · rintro ⟨a,b⟩
    exact hp.dvd_choose b (by omega) hit

theorem entry_gcd {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (order : p<q) (widthLo : B≤p) (widthHi : q<2*B) :
    (entry (p*q) B).gcd (p*q) = p := by
  have ps := hp.pos
  have qs := hq.pos
  have bot : p≤(p*q).sqrt := Nat.le_sqrt.mpr (Nat.mul_le_mul_left _ order.le)
  have top : (p*q).sqrt<q := Nat.sqrt_lt.mpr (Nat.mul_lt_mul_of_pos_right order qs)
  have partner : q≤2*B-1 := by omega
  have small : (p*q-1)/(2*B-1)<p := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by
    have pos := Nat.mul_pos ps qs
    have lim : p*q ≤ p*(2*B-1) := Nat.mul_le_mul_left p partner
    omega)
  have lowerLe : lower (p*q) B≤p := by unfold lower; exact max_le widthLo (by omega)
  have lowerGe : B≤lower (p*q) B := le_max_left _ _
  have col : (p*q).sqrt+1-lower (p*q) B≤(p*q).sqrt := by omega
  apply NormBatchGCD.one_batch hq
  · exact (column_iff hp col bot (by omega)).mpr ⟨by omega,by omega⟩
  · exact prime_above_row hq top col

/-- Certificate wrapper allowing a literal product to stay opaque to the evaluator. -/
theorem checked_gcd {n p q B : ℕ} (product : n=p*q) (hp : p.Prime) (hq : q.Prime)
    (order : p<q) (lo : B≤p) (hi : q<2*B) : (entry n B).gcd n=p := by
  subst n
  exact entry_gcd hp hq order lo hi

/-- Bundle recovery and primality without eagerly expanding a large closed entry. -/
def VerifiedRow (n B p q : ℕ) : Prop := (entry n B).gcd n=p ∧ ExactFactorization n [p,q]

theorem verify_row {n B p q : ℕ} (product : n=p*q) (hp : p.Prime) (hq : q.Prime)
    (order : p<q) (lo : B≤p) (hi : q<2*B) (fac : ExactFactorization n [p,q]) :
    VerifiedRow n B p q := ⟨checked_gcd product hp hq order lo hi,fac⟩

theorem entry_bits {n B : ℕ} (h : 0<n.sqrt) : entry n B < 2^n.sqrt :=
  Nat.choose_le_two_pow _ _ h

/-- Even the shortest admissible column may contain exponentially many bits. -/
theorem entry_floor {u k : ℕ} (width : 2*k≤u) : 2^k≤u.choose k := by
  apply le_trans _ (Nat.choose_le_choose k width)
  clear width u
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 2*(k+1)=2*k+1+1 by omega,Nat.choose_succ_succ,pow_succ]
    have l := Nat.choose_le_choose k (show 2*k≤2*k+1 by omega)
    have r : (2*k).choose k≤(2*k+1).choose (k+1) := by
      rw [Nat.choose_succ_succ]
      omega
    exact (Nat.mul_le_mul_right 2 ih).trans (by simpa [Nat.mul_two] using Nat.add_le_add l r)

/-- A symbolic size statement avoids evaluating the closed binomial coefficient. -/
def SizeBound (n B e : ℕ) : Prop := 2^(2^e)≤entry n B

theorem checked_size {n B u k e : ℕ}
    (sqlo : u*u≤n) (sqhi : n<(u+1)*(u+1)) (col : u+1-lower n B=k)
    (enough : 2*k≤u) (large : 2^e≤k) : SizeBound n B e := by
  have sq : n.sqrt=u := le_antisymm (Nat.le_of_lt_succ (Nat.sqrt_lt.mpr sqhi)) (Nat.le_sqrt.mpr sqlo)
  unfold SizeBound entry
  rw [sq,col]
  exact (Nat.pow_le_pow_right (by decide) large).trans (entry_floor enough)

end PrimeFactors.ShortPascalRow
