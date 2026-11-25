import PrimeFactors.WeightedCollision
import PrimeFactors.GapStride
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Factorization.Basic

namespace PrimeFactors

/-- Reducing the numerator and denominator of the approximating fraction
can only shrink its error in the cross product. -/
theorem exists_primitive_multiplier_band {p q K : ℕ} (hp : 0 < p)
    (ordered : p ≤ q) (balanced : q ≤ 2*p) (hK : 0 < K) :
    ∃ a b : ℕ, 0 < b ∧ b ≤ K ∧ b ≤ a ∧ a ≤ 2*b ∧ a.Coprime b ∧
      (K+1)*Nat.dist (a*p) (b*q) ≤ p := by
  obtain ⟨a,b,hb,hK',hba,hab,band⟩ := exists_balanced_multiplier_band hp ordered balanced hK
  let g := a.gcd b
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hb
  let A := a/g
  let B := b/g
  have ha' : A*g = a := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
  have hb' : B*g = b := Nat.div_mul_cancel (Nat.gcd_dvd_right a b)
  have hbpos : 0 < B := Nat.pos_of_ne_zero (fun h => by rw [h, zero_mul] at hb'; omega)
  have Ble : B ≤ b := Nat.div_le_self _ _
  refine ⟨A,B,hbpos,Ble.trans hK', Nat.le_of_mul_le_mul_right (ha' ▸ hb' ▸ hba) hg, ?_,
    Nat.coprime_div_gcd_div_gcd hg, ?_⟩
  · exact Nat.le_of_mul_le_mul_right (show A*g ≤ (2*B)*g by rw [ha',mul_assoc,hb']; exact hab) hg
  · have eq : Nat.dist (a*p) (b*q) = Nat.dist (A*p) (B*q) * g := by
      rw [← Nat.dist_mul_right, mul_right_comm A p, mul_right_comm B q, ha', hb']
    rw [eq] at band
    exact (Nat.mul_le_mul_left (K+1) (Nat.le_mul_of_pos_right _ hg)).trans band

/-- The maximal public modulus in which this weighted sum has a single
residue for every possible local unit, when the weights are primitive. -/
def weightedStride (n a b : ℕ) := Nat.gcd 24 (2*(a+b*n))

theorem weighted_sum_congruent {p : ℕ} (hp : p.Coprime 6) (a b q : ℕ) :
    a*p+b*q ≡ a+b*(p*q) [MOD weightedStride (p*q) a b] := by
  let n := p*q
  let C := a+b*n
  let s := weightedStride n a b
  have ds : s ∣ 24 := Nat.gcd_dvd_left _ _
  have dc : s ∣ 2*C := Nat.gcd_dvd_right _ _
  have sq : (p : ZMod s)^2 = 1 := by
    exact_mod_cast (ZMod.eq_iff_modEq_nat s).2 ((square_mod_twentyfour hp).of_dvd ds)
  have zeroC : (2:ZMod s)*C = 0 := by exact_mod_cast (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).2 dc
  have oddp : Odd p := by
    rw [← Nat.coprime_two_right]
    exact hp.of_dvd_right (by decide)
  obtain ⟨k,hk⟩ := oddp
  have pk : (p:ZMod s) = 2*k+1 := by rw [hk]; push_cast; rfl
  have same : (C : ZMod s)*p = C := by rw [pk]; linear_combination (k:ZMod s)*zeroC
  apply (ZMod.eq_iff_modEq_nat s).mp
  push_cast
  calc
    _ = (a + (b:ZMod s)*((p:ZMod s)*q))*p := by linear_combination -((b:ZMod s)*q)*sq
    _ = _ := by simpa [C,n] using same

/-- Raising each slope to a known power aligns every progression with
one table of powers of the same base. Equality need only hold modulo p. -/
theorem weighted_stride_collision {p : ℕ} (hp : p.Prime) (q a b s L start i : ℕ)
    (stride : s ∣ L) (hit : start+s*i = a*p+b*q) (v : (ZMod p)ˣ) :
    (v^L)^i = (v^(a+b*(p*q)) / v^start)^(L/s) := by
  have e : v^(s*i) = v^(a+b*(p*q)) / v^start := by
    apply (eq_div_iff_mul_eq').mpr
    rw [← pow_add, Nat.add_comm (s*i), hit]
    exact weighted_power_at_prime hp _ _ _ _
  rw [← e, ← pow_mul, ← pow_mul]
  congr 1
  calc
    L*i = (L/s*s)*i := by rw [Nat.div_mul_cancel stride]
    _ = s*i*(L/s) := by ring

end PrimeFactors
