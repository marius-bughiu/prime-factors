import PrimeFactors.QuarticTrace
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

namespace PrimeFactors.TraceDirection

open PrimeFactors.QuarticTrace

private theorem primitive_of_prime_norm {p : ℕ} (prime : p.Prime) {u v : ℤ}
    (norm : u^2+v^2=p) : IsCoprime u v := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  by_contra bad
  obtain ⟨l, lp, lg⟩ := Nat.exists_prime_and_dvd bad
  have lz := Int.natCast_dvd_natCast.mpr lg
  obtain ⟨a, ha⟩ := lz.trans (Int.gcd_dvd_left (a := u) (b := v))
  obtain ⟨b, hb⟩ := lz.trans (Int.gcd_dvd_right (a := u) (b := v))
  have square : (l*l : ℕ) ∣ p := by
    apply Int.natCast_dvd_natCast.mp
    refine ⟨a^2+b^2, ?_⟩
    push_cast
    rw [← norm, ha, hb]
    ring
  have eq := (prime.eq_one_or_self_of_dvd _ ((dvd_mul_right l l).trans square)).resolve_left lp.ne_one
  subst l
  have := Nat.le_of_dvd prime.pos square
  nlinarith [prime.two_le]

private theorem odd_half {t : ℤ} (parity : t ≡ 2 [ZMOD 4]) :
    Odd (t/2) ∧ t=2*(t/2) := by
  change t % 4 = 2 % 4 at parity
  rw [Int.odd_iff]
  omega

/-- The pair of public sums is a common odd multiple of four times a
primitive direction. The squared length of the direction is the prime
where the selector is a nonsquare. -/
theorem direction_of_traces (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (pc : p%4=1) (qc : q%4=1) (d : ℤ)
    (left : quadraticChar (ZMod p) (d : ZMod p) = -1)
    (right : quadraticChar (ZMod q) (d : ZMod q) = 1) :
    ∃ h u v : ℤ, Odd h ∧ Odd u ∧ IsCoprime u v ∧ u^2+v^2=p ∧
      complete (p*q) 1=4*h*u ∧ complete (p*q) d=4*h*v := by
  have split : quadraticChar (ZMod p) (-1)=1 := by
    apply (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
    exact FiniteField.isSquare_neg_one_iff.mpr (by simp [ZMod.card, pc])
  have localNorm := complementary_squares (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; omega) split left
  rw [ZMod.card] at localNorm
  obtain ⟨pu, pe⟩ := odd_half (base_parity p pc)
  obtain ⟨qh, qe⟩ := odd_half (base_parity q qc)
  have evenSum : Even (trace (1 : ZMod p)^2 + trace (d : ZMod p)^2) := by
    rw [localNorm]
    exact ⟨2*p, by ring⟩
  have evenBase : Even (trace (1 : ZMod p)^2) :=
    Int.even_pow.mpr ⟨⟨trace (1 : ZMod p)/2, by linear_combination pe⟩, by decide⟩
  obtain ⟨z, zdef⟩ := (Int.even_pow.mp ((Int.even_add.mp evenSum).mp evenBase)).1
  have dn : (d : ZMod q) ≠ 0 := fun e => by simp [e] at right
  obtain ⟨s, hs⟩ := (quadraticChar_one_iff_isSquare dn).mp right
  have sn : s ≠ 0 := fun e => dn (by simp [hs, e])
  let sign := quadraticChar (ZMod q) s
  have signSq : sign^2=1 := quadraticChar_sq_one sn
  have twist : trace (d : ZMod q)=sign*trace (1 : ZMod q) := by
    rw [show (d : ZMod q)=s^2*1 by simpa [sq] using hs, trace_scale sn]
  have halfNorm : (trace (1 : ZMod p)/2)^2+(sign*z)^2=p := by
    rw [mul_pow, signSq, one_mul]
    nlinarith only [localNorm, pe, zdef,
      congrArg (fun t : ℤ => t^2) pe, congrArg (fun t : ℤ => t^2) zdef]
  refine ⟨_, _, _, qh, pu, primitive_of_prime_norm (Fact.out : p.Prime) halfNorm, halfNorm, ?_, ?_⟩
  · rw [complete_eq p q cop]
    push_cast
    linear_combination (trace (1 : ZMod q))*pe + (2*(trace (1 : ZMod p)/2))*qe
  · rw [complete_eq p q cop, twist, zdef]
    linear_combination 2*z*sign*qe

/-- At modulus larger than its squared length, a primitive integer vector
is a shortest vector of its slope lattice, unique up to sign. The Bézout
identity is a certificate of primitivity. -/
theorem shortest_norm {u v x y M a b : ℤ}
    (primitive : a*u+b*v=1) (fits : u^2+v^2<M)
    (lattice : M ∣ u*y-v*x) (nonzero : x ≠ 0 ∨ y ≠ 0)
    (short : x^2+y^2 ≤ u^2+v^2) : x^2+y^2 = u^2+v^2 := by
  let Q := u^2+v^2
  have nonneg : 0 ≤ Q := by dsimp [Q]; positivity
  have area : (u*y-v*x)^2+(u*x+v*y)^2 = Q*(x^2+y^2) := by dsimp [Q]; ring
  have bound : (u*y-v*x)^2 ≤ Q^2 := by
    have := mul_le_mul_of_nonneg_left short nonneg
    change Q*(x^2+y^2) ≤ Q*Q at this
    nlinarith only [area, this, sq_nonneg (u*x+v*y)]
  have det := Int.eq_zero_of_abs_lt_dvd lattice ((abs_le_of_sq_le_sq bound nonneg).trans_lt fits)
  let k := a*x+b*y
  have hx : x=k*u := by dsimp [k]; linear_combination -x*primitive - b*det
  have hy : y=k*v := by dsimp [k]; linear_combination -y*primitive + a*det
  have kne : k ≠ 0 := by
    intro h
    simp [h] at hx hy
    exact nonzero.elim (fun h' => h' hx) (fun h' => h' hy)
  have ksq : 1 ≤ k^2 := by
    rcases lt_or_gt_of_ne kne with h | h
    · nlinarith only [h, mul_nonneg (show 0 ≤ -k-1 by omega) (show 0 ≤ -k+1 by omega)]
    · nlinarith only [mul_nonneg (show 0 ≤ k-1 by omega) (show 0 ≤ k+1 by omega)]
  have lower := mul_le_mul_of_nonneg_right ksq nonneg
  dsimp [Q] at lower
  rw [hx, hy] at short ⊢
  exact le_antisymm short (by nlinarith only [lower])

/-- Any two vectors with the same modular slope have determinant divisible
by the modulus. Neither first coordinate has to be invertible here. -/
theorem determinant_dvd {r M u v x y : ℤ} (hv : M ∣ v-r*u) (hy : M ∣ y-r*x) :
    M ∣ u*y-v*x := by
  obtain ⟨i, hi⟩ := hv
  obtain ⟨j, hj⟩ := hy
  exact ⟨u*j-i*x, by linear_combination u*hj - x*hi⟩

/-- A shortest nonzero vector computed using only the low k+2 bits of
each complete sum recovers the selected prime whenever that prime fits
strictly below 2^k. The slope and the vector are both public inputs. -/
theorem shortest_from_readings (p q : ℕ) [hp : Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (pc : p%4=1) (qc : q%4=1) (d : ℤ)
    (left : quadraticChar (ZMod p) (d : ZMod p) = -1)
    (right : quadraticChar (ZMod q) (d : ZMod q) = 1)
    (k : ℕ) (fits : (p : ℤ)<2^k) (r x y : ℤ)
    (reading : 4*2^k ∣ complete (p*q) d - r*complete (p*q) 1)
    (onSlope : 2^k ∣ y-r*x) (nz : x≠0 ∨ y≠0)
    (shortest : ∀ a b : ℤ, (a≠0 ∨ b≠0) → 2^k ∣ b-r*a → x^2+y^2 ≤ a^2+b^2) :
    x^2+y^2=p := by
  obtain ⟨h,u,v,oh,_,prim,norm,base,twist⟩ := direction_of_traces p q cop pc qc d left right
  obtain ⟨j,hj⟩ := oh
  have unit : IsCoprime (2 : ℤ) h := ⟨-j, 1, by rw [hj]; ring⟩
  obtain ⟨t,ht⟩ := reading
  rw [base,twist] at ht
  have trueSlope : (2 : ℤ)^k ∣ v-r*u :=
    (unit.pow_left (m := k)).dvd_of_dvd_mul_left ⟨t, by nlinarith only [ht]⟩
  have trueNz : u≠0 ∨ v≠0 := by
    by_contra! both
    rw [both.1, both.2] at norm
    simp [eq_comm, hp.out.ne_zero] at norm
  obtain ⟨a,b,bezout⟩ := prim
  rw [← norm]
  exact shortest_norm bezout (norm ▸ fits) (determinant_dvd trueSlope onSlope) nz
    (shortest u v trueNz trueSlope)

end PrimeFactors.TraceDirection
