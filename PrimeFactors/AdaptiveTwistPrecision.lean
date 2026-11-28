import PrimeFactors.AdaptiveThreeSquareTwist

/-! Precision needed for a supplied mixed-sign three-square count. -/

namespace PrimeFactors.AdaptiveTwistPrecision

open FiniteThreeSquareTwists

theorem count_mod (b N : ℤ) {r : ℤ} (odd : Odd r) :
    b*(N+2*r) ≡ b*(N+2) [ZMOD 4*b] := by
  obtain ⟨k,rfl⟩ := odd
  exact Int.modEq_iff_dvd.mpr ⟨-k,by ring⟩

/-- Round the supplied integer count to the nearest odd candidate.
At an exact midpoint the quotient selects the larger candidate. -/
def roundOdd (b N v : ℤ) : ℤ := 2*((v-b*N)/(4*b))+1

theorem rounded {b N r v : ℤ} (pos : 0<b) (odd : Odd r)
    (error : |v-b*(N+2*r)|<2*b) : roundOdd b N v=r := by
  obtain ⟨k,rfl⟩ := odd
  have bounds := abs_lt.mp error
  have quot : (v-b*N)/(4*b)=k := by
    apply (Int.ediv_eq_iff_of_pos (show 0<4*b by positivity)).mpr
    constructor <;> nlinarith only [bounds.1,bounds.2]
  simp only [roundOdd,quot]

/-- Two candidates consistent with the same estimate have distance at most
ε/b. This bound also holds with real-valued estimates and candidates. -/
theorem candidate_gap {b N r s v ε : ℝ} (pos : 0<b)
    (first : |v-b*(N+2*r)|≤ε) (second : |v-b*(N+2*s)|≤ε) :
    |r-s|≤ε/b := by
  have size : 2*b*|r-s| ≤ ε+ε := calc
    2*b*|r-s| = |2*b*(r-s)| := by rw [abs_mul,abs_of_pos (by positivity : 0<2*b)]
    _ = |b*(N+2*r)-b*(N+2*s)| := by congr 1; ring
    _ ≤ |b*(N+2*r)-v|+|v-b*(N+2*s)| := abs_sub_le _ _ _
    _ ≤ ε+ε := add_le_add (abs_sub_comm v _ ▸ first) second
  apply (le_div_iff₀ pos).mpr
  linarith only [size]

attribute [local irreducible] r₃

/-- On a mixed-sign twist the estimate determines both the split prime
and its exact count, assuming the classical three-square recurrence. -/
theorem mixed_rounds (formula : HirschhornSellers) {p q d : ℕ}
    (pp : p.Prime) (qp : q.Prime) (op : Odd p) (oq : Odd q) (ne : p≠q)
    (negative : jacobiSym (-(d:ℤ)) (p*q)= -1) (represented : 0<r₃ d) (v : ℤ)
    (error : |v-(r₃ (d*(p*q)^2) : ℤ)|<2*(r₃ d : ℤ)) :
    ∃ r : ℕ, (r=p ∨ r=q) ∧ jacobiSym (-(d:ℤ)) r=1 ∧
      roundOdd (r₃ d) (p*q) v=r ∧
      (r₃ (d*(p*q)^2) : ℤ)=(r₃ d : ℤ)*(p*q+2*roundOdd (r₃ d) (p*q) v) := by
  have branch (r : ℕ) (odd : Odd r) (count : r₃ (d*(p*q)^2)=r₃ d*(p*q+2*r)) :
      roundOdd (r₃ d) (p*q) v=r ∧
      (r₃ (d*(p*q)^2) : ℤ)=(r₃ d : ℤ)*(p*q+2*roundOdd (r₃ d) (p*q) v) := by
    have value : (r₃ (d*(p*q)^2) : ℤ)=(r₃ d : ℤ)*(p*q+2*(r:ℤ)) := by exact_mod_cast count
    have correct := rounded (by exact_mod_cast represented : 0<(r₃ d : ℤ))
      (by exact_mod_cast odd : Odd (r:ℤ)) (value ▸ error)
    exact ⟨correct,correct ▸ value⟩
  rcases AdaptiveThreeSquareTwist.mixed formula pp qp op oq ne negative with
    ⟨ps,_,c⟩|⟨_,qs,c⟩
  · exact ⟨p,Or.inl rfl,ps,branch p op c⟩
  · exact ⟨q,Or.inr rfl,qs,branch q oq c⟩

/-- The radius 2b is sharp on the lattice of odd integer candidates.
Here only 5 divides 15, so the tie concerns two possible lattice readings. -/
theorem boundary : |(162:ℤ)-6*(15+2*5)|=2*6 ∧ |(162:ℤ)-6*(15+2*7)|=2*6 ∧
    roundOdd 6 15 162=7 ∧ (5:ℕ)∣15 ∧ ¬(7:ℕ)∣15 := by decide +kernel

end PrimeFactors.AdaptiveTwistPrecision
