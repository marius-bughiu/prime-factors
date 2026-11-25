import PrimeFactors.DivisorWindowDimension
import PrimeFactors.ChebyshevQuarticScale
import PrimeFactors.CoupledDivisorWindow
import Mathlib.Tactic.Ring

namespace PrimeFactors.DivisorWindowThreshold

/-- Binary-log bounds with a common denominator s. Here a/s bounds log₂N from
above, b/s bounds log₂D from below, and c/s = 2 log₂W + 1. k is the degree. -/
def passes (a b c s m k : ℕ) : Prop :=
  (k+1)^(2*s*(k+1)) * 2^(2*a*m*(m+1)+c*k*(k+1)) < 2^(4*b*m*(k+1))

/-- The previous separate input bounds are the integer-log special case. -/
theorem independent (m k w : ℕ) : passes 2048 1023 (2*w+1) 1 m k ↔
    DivisorWindowDimension.sufficient k m w := by
  simp only [passes,DivisorWindowDimension.sufficient,Nat.mul_one]

private theorem raw_budget {a b c s m k : ℕ} (pass : passes a b c s m k) :
    2*a*m*(m+1)+c*k*(k+1) < 4*b*m*(k+1) := by
  apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
  apply lt_of_le_of_lt _ pass
  exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos _))

/-- No choice of dimension or admissible multiplicity makes the determinant
criterion succeed on or beyond its limiting boundary. -/
theorem necessary {a b c s m k : ℕ} (ha : 0<a) (hk : 0<k) (depth : m≤k)
    (pass : passes a b c s m k) : a*c < 2*b^2 := by
  by_contra! bad
  have H := raw_budget pass
  let A : ℤ := a
  let B : ℤ := b
  let C : ℤ := c
  let K : ℤ := k
  let M : ℤ := m
  have a0 : 0<A := by dsimp [A]; exact_mod_cast ha
  have k0 : 0<K := by dsimp [K]; exact_mod_cast hk
  have m0 : 0≤M := Int.natCast_nonneg _
  have mk : M≤K := by dsimp [M,K]; exact_mod_cast depth
  have cmp : 2*B^2≤A*C := by dsimp [A,B,C]; exact_mod_cast bad
  have strict : 0 < 4*B*M*(K+1) - (2*A*M*(M+1)+C*K*(K+1)) := by
    dsimp [A,B,C,M,K]; apply sub_pos.mpr; exact_mod_cast H
  have cert : 0 ≤ 2*(K+1)*(A*M-B*K)^2 + 2*A^2*M*(K-M) + (A*C-2*B^2)*K^2*(K+1) := by
    have diff : 0≤K-M := by omega
    have gap : 0≤A*C-2*B^2 := by omega
    positivity
  nlinarith only [cert, mul_pos (mul_pos a0 k0) strict]

private theorem square_le_pow {j : ℕ} (four : 4 ≤ j) : j^2 ≤ 2^j := by
  induction j, four using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [pow_succ]
    calc
      (n+1)^2 ≤ n^2*2 := by nlinarith [Nat.mul_le_mul_left n hn]
      _ ≤ _ := Nat.mul_le_mul_right 2 ih

/-- In the strict interior one rational slope m/k=b/a suffices. Scaling its
numerator and denominator pays even the dimension term in the LLL guarantee.
The deliberately large constructive witness proves existence, not optimal cost. -/
theorem attainable {a b c s : ℕ} (ha : 0<a) (hb : 0<b) (ba : b≤a) (gain : a*c<2*b^2) :
    ∃ k m : ℕ, 0<m ∧ m≤k ∧ passes a b c s m k := by
  let h := a+1
  let V := 2*s*(a+1)
  let U := 2*a*b+c*a+V*h
  let j := U+V+4
  let t := 2^j
  have j4 : 4 ≤ j := by dsimp [j]; omega
  have t0 : 0<t := Nat.pow_pos (by decide)
  have bound : U+V*j < t := by
    have cmp : V+1 ≤ j := by dsimp [j]; omega
    have uu : U < j := by dsimp [j]; omega
    have mult := Nat.mul_le_mul_right j cmp
    have sq := square_le_pow j4
    dsimp only [t]
    nlinarith only [mult,uu,sq]
  let k := a*t
  let m := b*t
  refine ⟨k,m,Nat.mul_pos hb t0,Nat.mul_le_mul_right t ba,?_⟩
  have rank : k+1 ≤ 2^(j+h) := by
    have dim : a+1 ≤ 2^h := Nat.le_of_lt (Nat.lt_two_pow_self)
    rw [pow_add,mul_comm]
    change a*t+1 ≤ 2^h*t
    exact (by nlinarith only [Nat.mul_le_mul_right t dim,t0])
  have cheap : 2*a*b+c*a+V*(j+h)<t := by
    dsimp only [U] at bound
    nlinarith only [bound]
  have sized : (j+h)*(2*s*(k+1)) ≤ V*(j+h)*t := by
    have r : k+1 ≤ (a+1)*t := by dsimp [k]; nlinarith only [t0]
    have H := Nat.mul_le_mul_left ((j+h)*(2*s)) r
    dsimp only [V]; nlinarith only [H]
  have gain' : a*c+1 ≤ 2*b^2 := gain
  have lead := Nat.mul_le_mul_right (a*t^2) gain'
  have ax := Nat.mul_le_mul_right (t^2) ha
  have strict := Nat.mul_lt_mul_of_pos_right cheap t0
  have exps : (j+h)*(2*s*(k+1))+(2*a*m*(m+1)+c*k*(k+1)) < 4*b*m*(k+1) := by
    dsimp only [m,k] at sized ⊢
    nlinarith only [sized,lead,ax,strict,Nat.zero_le (4*b^2*t)]
  unfold passes
  apply lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left rank _))
  rw [← pow_mul,← pow_add]
  exact Nat.pow_lt_pow_right (by decide) exps

/-- Sharp threshold for this family of height inequalities at rational input bounds. -/
theorem threshold {a b c s : ℕ} (hb : 0<b) (ba : b≤a) :
    (∃ k m : ℕ, 0<m ∧ m≤k ∧ passes a b c s m k) ↔ a*c < 2*b^2 := by
  constructor
  · rintro ⟨k,m,hm,mk,H⟩
    exact necessary (hb.trans_le ba) (hm.trans_le mk) mk H
  · exact attainable (hb.trans_le ba) hb ba

/-- The same one-polynomial estimate using the actual integer input and divisor floor. -/
def actual (n D w m k : ℕ) : Prop :=
  (k+1)^(2*(k+1)) * 2^((2*w+1)*k*(k+1)) * n^(2*m*(m+1)) < D^(4*m*(k+1))

private def scaled (n D s c m k : ℕ) : Prop :=
  (k+1)^(2*s*(k+1)) * n^(2*m*(m+1)) * 2^(c*k*(k+1)) < D^(4*m*(k+1))

private theorem pass_scaled (a b c s m k : ℕ) :
    passes a b c s m k ↔ scaled (2^a) (2^b) s c m k := by
  unfold passes scaled
  rw [pow_add,←pow_mul,←pow_mul]
  ac_nf

private theorem actual_scaled (n D s w m k : ℕ) (hs : 0 < s) :
    actual n D w m k ↔ scaled (n^s) (D^s) s (s*(2*w+1)) m k := by
  unfold actual scaled
  rw [← Nat.pow_lt_pow_iff_left hs.ne',mul_pow,mul_pow]
  simp only [← pow_mul]
  have left : (2*(k+1))*s = 2*s*(k+1) := by ring
  rw [left]
  ac_nf

private theorem mono {n n' D D' s c m k : ℕ} (nn : n≤n') (dd : D'≤D)
    (h : scaled n' D' s c m k) : scaled n D s c m k := by
  exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left nn _))).trans_lt
    (h.trans_le (Nat.pow_le_pow_left dd _))

theorem of_upper {a b s n D w m k : ℕ} (hs : 0<s) (up : n^s ≤ 2^a) (low : 2^b ≤ D^s)
    (p : passes a b (s*(2*w+1)) s m k) : actual n D w m k :=
  (actual_scaled n D s w m k hs).2 (mono up low ((pass_scaled a b (s*(2*w+1)) s m k).1 p))

theorem no_dimension {a b s n D w : ℕ} (ha : 0<a) (hs : 0<s) (low : 2^a ≤ n^s)
    (up : D^s ≤ 2^b) (bad : 2*b^2 ≤ a*(s*(2*w+1))) {m k : ℕ} (hm : 0<m) (mk : m≤k) :
    ¬ actual n D w m k := by
  intro works
  have optimistic := mono low up ((actual_scaled n D s w m k hs).1 works)
  exact (not_lt_of_ge bad) (necessary ha (hm.trans_le mk) mk ((pass_scaled a b (s*(2*w+1)) s m k).2 optimistic))

private theorem finite_bound {a b c s m k j : ℕ} (dim : (k+1)^2 ≤ 2^j)
    (room : j*s*(k+1) + (2*a*m*(m+1)+c*k*(k+1)) < 4*b*m*(k+1)) :
    passes a b c s m k := by
  unfold passes
  have h : (k+1)^(2*s*(k+1)) ≤ 2^(j*s*(k+1)) := by
    rw [mul_assoc 2 s (k+1),pow_mul (k+1) 2 (s*(k+1)),mul_assoc j s (k+1),pow_mul 2 j (s*(k+1))]
    exact Nat.pow_le_pow_left dim _
  apply lt_of_le_of_lt (Nat.mul_le_mul_right _ h)
  rw [←pow_add]
  exact Nat.pow_lt_pow_right (by decide) room

set_option exponentiation.threshold 40000 in
set_option maxRecDepth 16384 in
/-- At the public lower endpoint radius 2^511 passes on the fresh input. -/
theorem fresh_passes : actual ChebyshevQuarticScale.fresh (CoupledDivisorWindow.lower ChebyshevQuarticScale.fresh)
    511 1288 2576 := by
  apply of_upper (a:=32763) (b:=16378) (s:=16) (by decide) (by decide +kernel) (by decide +kernel)
  exact finite_bound (j:=23) (by decide) (by decide)

set_option exponentiation.threshold 40000 in
set_option maxRecDepth 16384 in
/-- With the same public floor recipe the crossed input fails for every multiplicity and degree. -/
theorem crossed_fails {m k : ℕ} (hm : 0<m) (mk : m≤k) :
    ¬actual ChebyshevQuarticScale.crossed (CoupledDivisorWindow.lower ChebyshevQuarticScale.crossed) 511 m k := by
  exact no_dimension (a:=32754) (b:=16371) (s:=16) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide) hm mk

end PrimeFactors.DivisorWindowThreshold
