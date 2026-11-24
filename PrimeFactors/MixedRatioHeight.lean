import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

namespace PrimeFactors.MixedRatioHeight

/-- A mixed root interchanges the numerator and denominator of its own short fraction. -/
theorem reciprocal_rows {N u v : ℕ} {z : ZMod N} (row : (v : ZMod N)*z = u)
    (root : z^2 = 1) : (u : ZMod N)*z = v := by
  rw [← row, mul_assoc, ← sq, root, mul_one]

/-- A choice of factors AD = u² and CB = v² gives two representations of
one unit residue and fixes both heights before any common scaling. -/
theorem redistribute {N u v A B C D : ℕ} (left : A*D=u^2) (right : C*B=v^2)
    (mixed : (u : ZMod N)^2 = (v : ZMod N)^2) (bunit : IsUnit (B : ZMod N))
    {r : ZMod N} (row : (B : ZMod N)*r=A) :
    (D : ZMod N)*r=C ∧ (A*B)*(C*D)=(u*v)^2 := by
  constructor
  · apply bunit.mul_right_inj.mp
    calc
      _ = (A : ZMod N)*D := by rw [← row]; ring
      _ = (C : ZMod N)*B := by exact_mod_cast
        (show ((A*D : ℕ) : ZMod N) = ((C*B : ℕ) : ZMod N) by simpa [left,right] using mixed)
      _ = _ := mul_comm _ _
  · calc
      _ = (A*D)*(C*B) := by ring
      _ = _ := by rw [left,right,mul_pow]

private theorem lift_squares {p q : ℕ} {a : ℤ} (cop : p.Coprime q)
    (hp : IsSquare (a : ZMod p)) (hq : IsSquare (a : ZMod q)) : IsSquare (a : ZMod (p*q)) := by
  obtain ⟨x,hx⟩ := hp
  obtain ⟨y,hy⟩ := hq
  let e := ZMod.chineseRemainder cop
  refine ⟨e.symm (x,y),e.injective ?_⟩
  rw [map_intCast,map_mul, e.apply_symm_apply]
  exact Prod.ext hx hy

/-- For two primes congruent to three modulo four, a positive Jacobi sign
is enough to make one of the two global signs a square. -/
theorem square_or_neg_square {p q : ℕ} [pp : Fact p.Prime] [pq : Fact q.Prime]
    {a : ℤ} (cop : p.Coprime q) (hp : p%4 = 3) (hq : q%4 = 3)
    (sign : jacobiSym a (p*q)=1) : IsSquare (a : ZMod (p*q)) ∨ IsSquare (-a : ZMod (p*q)) := by
  rw [jacobiSym.mul_right' a pp.out.ne_zero pq.out.ne_zero] at sign
  have unit : (a : ZMod p) ≠ 0 := by
    intro h
    have zero := (legendreSym.eq_zero_iff p a).mpr h
    rw [jacobiSym.legendreSym.to_jacobiSym] at zero
    simp [zero] at sign
  rcases legendreSym.eq_one_or_neg_one p unit with plus | minus
  · rw [jacobiSym.legendreSym.to_jacobiSym] at plus
    rw [plus,one_mul] at sign
    exact Or.inl (lift_squares cop (ZMod.isSquare_of_jacobiSym_eq_one plus)
      (ZMod.isSquare_of_jacobiSym_eq_one sign))
  · rw [jacobiSym.legendreSym.to_jacobiSym] at minus
    rw [minus,neg_one_mul] at sign
    have reverse (k : ℕ) (hk : k%4=3) (ha : jacobiSym a k = -1) : jacobiSym (-a) k = 1 := by
      rw [jacobiSym.neg _ (Nat.odd_iff.mpr (by omega)), ZMod.χ₄_nat_three_mod_four hk, ha]
      decide
    have h := lift_squares cop (ZMod.isSquare_of_jacobiSym_eq_one (reverse p hp minus))
      (ZMod.isSquare_of_jacobiSym_eq_one (reverse q hq (by omega)))
    exact Or.inr (by simpa using h)

/-- The lower bound for Blum products. For heights g*d and g*e with d ≤ e
and d*e=W², D is the largest eligible positive-character divisor and L is a
lower bound for the first positive Jacobi nonresidue. -/
theorem blum_lower_bound {N W g d e D L : ℕ}
    (de : d*e = W^2) (ordered : d ≤ e) (gp : 0 < g)
    (squareClass : jacobiSym ((g*d : ℕ) : ℤ) N = 1)
    (unit : ((d : ℤ).gcd N) = 1)
    (largest : ∀ k : ℕ, k ∣ W^2 → k ≤ W → jacobiSym (k : ℤ) N = 1 → k ≤ D)
    (least : ∀ k : ℕ, jacobiSym (k : ℤ) N = -1 → L ≤ k) :
    min (W^2/D) (L*W) ≤ g*e := by
  have bounds : d ≤ W ∧ W ≤ e := by
    constructor
    · by_contra! h
      exact (Nat.ne_of_lt (Nat.mul_lt_mul_of_lt_of_le h (h.trans_le ordered).le (by omega)))
        (by simpa [sq] using de.symm)
    · by_contra! h
      exact (Nat.ne_of_lt (Nat.mul_lt_mul_of_lt_of_le (ordered.trans_lt h) h.le (by omega)))
        (by simpa [sq] using de)
  rcases jacobiSym.eq_one_or_neg_one unit with plus | minus
  · have leD := largest d (de ▸ dvd_mul_right d e) bounds.1 plus
    have bound : W^2/D ≤ e := Nat.div_le_of_le_mul (by rw [← de]; exact Nat.mul_le_mul_right e leD)
    exact (min_le_left ..).trans (bound.trans (Nat.le_mul_of_pos_left _ gp))
  · rw [Nat.cast_mul,jacobiSym.mul_left,minus,mul_neg_one] at squareClass
    have lower := least g (by omega)
    exact (min_le_right ..).trans (Nat.mul_le_mul lower bounds.2)

end PrimeFactors.MixedRatioHeight
