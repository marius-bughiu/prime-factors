import PrimeFactors.MaskedRelations
import PrimeFactors.RootIntervalSlope

namespace PrimeFactors.NormDirections

/-- A root of -d modulo N supplies a positive norm in the first 2s-1
multiples of N. The denominator and the signed remainder are both bounded. -/
theorem short_norm {N d s L : ℕ} {z : ℤ} (np : 0<N) (dp : 0<d)
    (lp : 0<L) (disc : d≤s^2)
    (lower : s*L^2≤N) (upper : N<s*(L+1)^2)
    (root : z^2 ≡ -(d : ℤ) [ZMOD (N : ℤ)]) :
    ∃ (a : ℕ) (t : ℤ) (k : ℕ), 1≤a ∧ a≤L ∧
      t ≡ (a : ℤ)*z [ZMOD (N : ℤ)] ∧ |t| *((L : ℤ)+1)≤N ∧
      0<k ∧ k<2*s ∧ t^2+d*(a : ℤ)^2=(k : ℤ)*N := by
  obtain ⟨a, ap, al, j, close⟩ := boundedSlope_exists N L z np lp
  let t : ℤ := a*z-N*j
  have near : |t| *((L : ℤ)+1)≤N := close
  have nz : (0 : ℤ)<N := by exact_mod_cast np
  have sqnear : (|t| *((L : ℤ)+1))^2≤(N : ℤ)^2 :=
    sq_le_sq' (le_trans (by omega : -(N : ℤ) ≤ 0) (by positivity)) near
  rw [mul_pow, sq_abs] at sqnear
  have upperZ : (N : ℤ)<s*((L : ℤ)+1)^2 := by exact_mod_cast upper
  have tsmall : t^2<(N : ℤ)*s := by
    have strict := mul_lt_mul_of_pos_left upperZ nz
    by_contra! h
    have opp := mul_le_mul_of_nonneg_right h (sq_nonneg ((L : ℤ)+1))
    nlinarith only [strict, sqnear, opp]
  have asmall : d*a^2 ≤ s*N := calc
    d*a^2 ≤ s^2*L^2 := Nat.mul_le_mul disc (Nat.pow_le_pow_left al 2)
    _ = s*(s*L^2) := by ring
    _ ≤ s*N := Nat.mul_le_mul_left _ lower
  have posA : (0 : ℤ)<a := by exact_mod_cast ap
  have posD : (0 : ℤ)<d := by exact_mod_cast dp
  have normpos : 0<t^2+(d : ℤ)*(a : ℤ)^2 := by positivity
  have congr : t ≡ (a : ℤ)*z [ZMOD (N : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨j, by dsimp [t]; ring⟩
  obtain ⟨h, hh⟩ := Int.modEq_iff_dvd.mp root
  let m : ℤ := -(a : ℤ)^2*h-2*a*z*j+N*j^2
  have eqn : t^2+(d : ℤ)*(a : ℤ)^2 = m*N := by
    dsimp [t,m]
    linear_combination -(a : ℤ)^2 * hh
  have mp : 0<m := pos_of_mul_pos_left (eqn ▸ normpos) nz.le
  have asmallZ : (d : ℤ)*(a : ℤ)^2 ≤ s*N := by exact_mod_cast asmall
  have mlt : m<2*(s : ℤ) := by
    by_contra! h
    have opp := mul_le_mul_of_nonneg_right h nz.le
    nlinarith only [eqn,tsmall,asmallZ,opp]
  refine ⟨a,t,m.toNat,ap,al,congr,near,?_,?_,?_⟩
  · omega
  · exact_mod_cast (show (m.toNat : ℤ) < 2*(s : ℤ) by rwa [Int.toNat_of_nonneg mp.le])
  · rwa [Int.toNat_of_nonneg mp.le]

/-- The weighted squared length of the shorter vector of a Gauss-reduced
basis satisfies the two-dimensional Hermite bound. For d > 0 and a
supplied root z, start from (N,0), (z,1). With v first and w second,
subtract the nearest integer multiple of v from w in the weighted inner
product. If w becomes shorter than v, swap and repeat. Each swap strictly
decreases the positive integral squared length of the first vector. Both
operations preserve the lattice and the absolute determinant. -/
theorem reduced_bound {t a u b d N : ℤ} (dn : 0≤d)
    (det : (t*b-u*a)^2=N^2)
    (ordered : t^2+d*a^2≤u^2+d*b^2)
    (reduced : 2*|t*u+d*a*b|≤t^2+d*a^2) :
    3*(t^2+d*a^2)^2≤4*d*N^2 := by
  let V := t^2+d*a^2
  let W := u^2+d*b^2
  let dot := t*u+d*a*b
  have vnonneg : 0≤V := by dsimp [V]; positivity
  have comp : V*V≤V*W := mul_le_mul_of_nonneg_left ordered vnonneg
  have dotSq : (2*|dot|)^2≤V^2 :=
    sq_le_sq' ((neg_nonpos.mpr vnonneg).trans (by positivity)) reduced
  rw [mul_pow, sq_abs] at dotSq
  have area : V*W-dot^2=d*N^2 := by
    rw [← det]; dsimp [V,W,dot]; ring
  change 3*V^2≤4*d*N^2
  nlinarith only [comp, dotSq, area]

/-- Dividing the Hermite bound by N² gives an upper bound on the
represented multiplier that depends only on the chosen d. -/
theorem reduced_multiplier {t a u b d N k : ℤ} (np : 0 < N) (dn : 0 ≤ d)
    (det : (t*b-u*a)^2=N^2)
    (ordered : t^2+d*a^2≤u^2+d*b^2)
    (reduced : 2*|t*u+d*a*b|≤t^2+d*a^2) (norm : t^2+d*a^2=k*N) :
    3*k^2 ≤ 4*d := by
  have bound := reduced_bound dn det ordered reduced
  rw [norm, mul_pow, ← mul_assoc] at bound
  exact le_of_mul_le_mul_right bound (sq_pos_of_pos np)

/-- Comparing two representations works for any represented multiples of N
and any common d. Both tests against the global signs are explicit. -/
theorem cross_gcd {N : ℕ} [NeZero N] {t u a b d : ZMod N}
    (first : t^2+d*a^2=0) (second : u^2+d*b^2=0)
    (plus : t*b ≠ u*a) (minus : t*b ≠ -(u*a)) :
    1<(t*b-u*a).val.gcd N ∧ (t*b-u*a).val.gcd N<N := by
  apply PrimeFactors.maskedRelations_split _ plus minus
  linear_combination b^2*first - a^2*second

/-- The two sums of squares representing 65 give gcds 5 and 13. -/
theorem example_65 :
    1^2+8^2=(65 : ℕ) ∧ 4^2+7^2=(65 : ℕ) ∧
    Nat.gcd (4*8-1*7) 65=5 ∧ Nat.gcd (4*8+1*7) 65=13 := by decide

end PrimeFactors.NormDirections
