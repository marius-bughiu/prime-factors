import PrimeFactors.BalancedPairPopulation

/-! Counting positive target norms with a bound on the convergent denominator.
The count covers all positive primitive and nonprimitive representations of the
specified size, irrespective of the starting multiplier or the method of search. -/
namespace PrimeFactors.SmallConvergentTargetPopulation

open Finset BalancedPairPopulation
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
attribute [local irreducible] BalancedPairPopulation.pairs

/-- The complete denominator for u = sqrt(R) is below 2u. Here old is
the preceding denominator and P is the new offset. The strict gap bound is
the remainder inequality for the floor quotient. -/
theorem remainder_bound {u P old Q : ℝ} (floorGap : u-P < old)
    (offset : P ≤ u) (positive : 0 < u+P) (oldpos : 0 < old)
    (recurrence : old*Q = u^2-P^2) : Q < 2*u := by
  have less : old*Q < old*(u+P) := by
    rw [recurrence]
    calc u^2-P^2 = (u-P)*(u+P) := by ring
         _ < old*(u+P) := mul_lt_mul_of_pos_right floorGap positive
  have := lt_of_mul_lt_mul_left less oldpos.le
  linarith

/-- A positive norm of the size of a complete denominator, for target 2 or 3. -/
def Hit (b N : ℕ) : Prop := ∃ D x t k y : ℕ, 2 ≤ D ∧ D ≤ 3 ∧
  0 < k ∧ k ≤ 320 ∧ 0 < y ∧ y ≤ 2^b ∧
  x^2 = k*N*y^2 + D*t^2 ∧ (D*t^2)^2 < 4*k*N

noncomputable def hits (b : ℕ) := by
  classical
  exact pairs.filter fun z => Hit b (z.1*z.2)

private theorem from_square {a b : ℕ} (small : a^2 < b^2) : a < b := by
  by_contra! bad
  exact (not_lt_of_ge (Nat.pow_le_pow_left bad 2)) small

private theorem heights {b N D x t k y : ℕ} (cap : b ≤ 500) (input : N < 2^2048)
    (pos : 2 ≤ D) (mulcap : k ≤ 320) (den : y ≤ 2^b)
    (norm : x^2 = k*N*y^2 + D*t^2) (small : (D*t^2)^2 < 4*k*N) :
    x < 2^1029*2^b ∧ t < 3*2^513 ∧ k*y^2 < 2^1023 := by
  have kn := Nat.mul_le_mul mulcap input.le
  have rem : D*t^2 < 2^1030 := from_square (small.trans_le (by
    calc 4*k*N = 4*(k*N) := by ring
         _ ≤ 4*(320*2^2048) := Nat.mul_le_mul_left 4 kn
         _ ≤ (2^1030)^2 := by decide +kernel))
  have den2 := Nat.pow_le_pow_left den 2
  have growth : 0 < (2^b)^2 := by positivity
  refine ⟨from_square ?_, ?_, ?_⟩
  · calc
      x^2 = k*N*y^2 + D*t^2 := norm
      _ ≤ (320*2^2048)*(2^b)^2 + 2^1030*(2^b)^2 :=
        Nat.add_le_add (Nat.mul_le_mul kn den2) (rem.le.trans (Nat.le_mul_of_pos_right _ growth))
      _ = (320*2^2048 + 2^1030)*(2^b)^2 := by ring
      _ < (2^1029)^2*(2^b)^2 := Nat.mul_lt_mul_of_pos_right (by decide +kernel) growth
      _ = (2^1029*2^b)^2 := (mul_pow ..).symm
  · apply lt_of_not_ge
    intro high
    have lower := Nat.mul_le_mul pos (Nat.pow_le_pow_left high 2)
    exact (not_lt_of_ge (le_trans (by decide +kernel : 2^1030 ≤ 2*(3*2^513)^2) lower)) rem
  · have dencap := den.trans (Nat.pow_le_pow_right (by decide : 0<2) cap)
    exact (Nat.mul_le_mul mulcap (Nat.pow_le_pow_left dencap 2)).trans_lt (by decide +kernel)

/-- The small cofactor cannot absorb even one of the unknown large primes. -/
private theorem recover {p q r s h j : ℕ}
    (pp : p.Prime) (qp : q.Prime) (rp : r.Prime) (sp : s.Prime) (pq : p<q) (rs : r<s)
    (small : j<p) (pos : 0<j) (same : (p*q)*h = (r*s)*j) : (p,q)=(r,s) := by
  have side (a : ℕ) (prime : a.Prime) (large : j<a) (dv : a ∣ p*q) : a=r ∨ a=s := by
    have all : a ∣ (r*s)*j := same ▸ dv.mul_right h
    rcases prime.dvd_mul.mp all with first | last
    · exact (prime.dvd_mul.mp first).imp (Nat.prime_dvd_prime_iff_eq prime rp).mp
                                         (Nat.prime_dvd_prime_iff_eq prime sp).mp
    · exact (not_lt_of_ge (Nat.le_of_dvd pos last) large).elim
  have hp := side p pp small (dvd_mul_right ..)
  have hq := side q qp (small.trans pq) (dvd_mul_left ..)
  exact Prod.ext (by omega) (by omega)

/-- Across every multiplier up to 320, a fixed target/numerator/scale triple
can belong to at most one balanced product. There is no multiplier or
denominator factor in the cardinality of the encoding. -/
theorem count (b : ℕ) (cap : b ≤ 500) : (hits b).card < 2^(1545+b) := by
  classical
  let A := {z // z ∈ hits b}
  let C := Fin 2 × Fin (2^1029*2^b) × Fin (3*2^513)
  have mem (z : A) := mem_filter.mp (show z.val ∈ pairs.filter (fun w => Hit b (w.1*w.2)) from z.property)
  have packet (z : A) : ∃ c : C, ∃ h : ℕ, 0<h ∧ h<2^1023 ∧
      (z.val.1*z.val.2)*h + (c.1.val+2)*c.2.2.val^2 = c.2.1.val^2 := by
    obtain ⟨D,x,t,k,y,lo,hi,kp,ks,yp,ys,norm,small⟩ := (mem z).2
    obtain ⟨_,_,_,_,_,width⟩ := mem_pairs.mp (mem z).1
    have bound := heights cap (Nat.size_le.mp width.le) lo ks ys norm small
    refine ⟨(⟨D-2,by omega⟩,⟨x,bound.1⟩,⟨t,bound.2.1⟩),k*y^2, by positivity,bound.2.2,?_⟩
    change (z.val.1*z.val.2)*(k*y^2) + (D-2+2)*t^2 = x^2
    rw [Nat.sub_add_cancel lo,norm]
    ring
  choose code h good using packet
  have injective : Function.Injective code := by
    intro z w eq
    obtain ⟨pp,qp,pq,ps,_,_⟩ := mem_pairs.mp (mem z).1
    obtain ⟨rp,sp,rs,_,_,_⟩ := mem_pairs.mp (mem w).1
    have gz := (good z).2.2
    rw [eq] at gz
    have same := Nat.add_right_cancel (gz.trans (good w).2.2.symm)
    apply Subtype.ext
    exact recover pp qp rp sp pq rs ((good w).2.1.trans_le (Nat.lt_size.mp (by omega)))
      (good w).1 same
  have n := Fintype.card_le_of_injective code injective
  change Fintype.card {z // z ∈ hits b} ≤ Fintype.card C at n
  rw [Fintype.card_coe] at n
  apply n.trans_lt
  simp only [C,Fintype.card_prod,Fintype.card_fin]
  rw [pow_add]
  calc
    2 * (2^1029 * 2^b * (3*2^513)) = (2*2^1029*(3*2^513))*2^b := by ring
    _ < 2^1545*2^b := Nat.mul_lt_mul_of_pos_right (by decide +kernel) (by positivity)

/-- Relative to the published population bound, e.g. b=384 gives 2^-96. -/
theorem fraction (dusart : WeightedCrowdingEstimates.Dusart) {b h : ℕ}
    (exponents : b+h ≤ 480) : 2^h * (hits b).card < pairs.card := by
  calc
    _ < 2^h * 2^(1545+b) := Nat.mul_lt_mul_of_pos_left (count b (by omega)) (by positivity)
    _ = 2^(h+(1545+b)) := (pow_add ..).symm
    _ ≤ 2^2025 := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ pairs.card := population dusart

end PrimeFactors.SmallConvergentTargetPopulation
