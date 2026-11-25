import PrimeFactors.BoundaryWindowSelection

/-! Conditional exact recovery. One sample scale per factor bit suffices
to dispense with the local polynomial search entirely. -/

namespace PrimeFactors.ExactBoundaryFactors

open BoundaryWindowSelection AnalyticDivisorWindow

/-- Round a lower estimate, shifted by half a unit, to the odd integer in its cell. -/
noncomputable def decode (A : ℝ) : ℕ := 2*⌊(A+1/2)/2⌋₊+1

private theorem rounding {q : ℕ} (odd : Odd q) {X A : ℝ} (low : X≤q)
    (dist : (q:ℝ)-X≤Real.pi/3) (approximation : |A-X|≤1/4) : decode A=q := by
  obtain ⟨j,hj⟩ := odd
  have eq : (q:ℝ)=2*(j:ℝ)+1 := by exact_mod_cast hj
  have π := Real.pi_lt_d2
  obtain ⟨left,right⟩ := abs_le.mp approximation
  have lo : (j:ℝ)≤(A+1/2)/2 := by linarith
  have hi : (A+1/2)/2<(j:ℝ)+1 := by linarith
  have floor := (Nat.floor_eq_iff ((Nat.cast_nonneg j).trans lo)).mpr ⟨lo,hi⟩
  rw [decode,floor]
  exact hj.symm

/-- For bit cap b the exact larger factor, and hence its partner, can be decoded
from two batches of at most 2(b+1) readings. The reading oracle is a hypothesis. -/
theorem recover {n bits : ℕ} [NeZero n] (read : ℕ → ℝ)
    (accurate : ∀ t∈queries bits (wave n read), |read t-boundaryProbe n t|≤1/8) :
    let T := queries bits (wave n read)
    let X := lowerValue n (left bits (wave n read))
    T.card≤2*(bits+1) ∧ (∀ t∈T, 0<t ∧ t≤2^(bits+1)) ∧
      ∀ A : ℝ, |A-X|≤1/4 → ∀ p q : ℕ, p*q=n → p.Prime → q.Prime → p<q →
        q≤2*p → q≤2^bits → decode A=q ∧ n/decode A=p := by
  refine ⟨query_count ..,fun _ ht => query_heights ht,?_⟩
  intro A approx p q pair hp hq ord bal cap
  subst n
  obtain ⟨lo,hi⟩ := enclosure (fits_readings hp hq ord bal read accurate)
  have phase : Real.log q-Real.log (p*q:ℕ)/2=(Real.log q-Real.log p)/2 := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
    ring
  rw [←phase] at lo hi
  obtain ⟨low,dist⟩ := lowerValue_bounds (by exact_mod_cast hq.pos) (by exact_mod_cast cap : (q:ℝ)≤(2:ℝ)^bits) lo hi
  have scale : (2:ℝ)^bits*(Real.pi/(3*2^bits))=Real.pi/3 := by field_simp; ring
  rw [scale] at dist
  have odd : Odd q := hq.odd_of_ne_two (by have := hp.two_le; omega)
  have hit := rounding odd low dist approx
  exact ⟨hit,by rw [hit,Nat.mul_div_cancel _ hq.pos]⟩

end PrimeFactors.ExactBoundaryFactors
