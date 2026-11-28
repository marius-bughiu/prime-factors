import PrimeFactors.CircleMarkChangedResidue
import PrimeFactors.Fermat

/-! Predicting the unsigned-change residue by substituting a proposed prime
sum. The slope gives an exact comparison with ordinary Fermat search. -/

namespace PrimeFactors.CircleMarkResiduePrediction

open CircleMarkChangedResidue

/-- The residue corresponding to a proposed real value of the prime sum. -/
noncomputable def predict (n d : ℕ) (s : ℝ) : ℝ := d*(s-2-d)/n

theorem correct {p q d : ℕ} [hp : Fact p.Prime] [Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) (cap : d ≤ (p-1)/2) :
    (value (p*q) d : ℝ) = predict (p*q) d ((p:ℝ)+q) := by
  have pp := hp.out.two_le
  have room : 2+d ≤ p+q := by omega
  rw [prefix_value order op oq cap, show p+q-2-d=p+q-(2+d) by omega]
  push_cast [Nat.cast_sub room]
  simp only [predict, Nat.cast_mul]
  ring

/-- The discrepancy in the predicted prime sum is multiplied by exactly d/N. -/
theorem error {p q d : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) (cap : d ≤ (p-1)/2) (s : ℝ) :
    |predict (p*q) d s - (value (p*q) d : ℝ)| =
      ((d:ℝ)/(p*q : ℕ))*|s-((p:ℝ)+q)| := by
  rw [correct order op oq cap]
  have eqn : predict (p*q) d s - predict (p*q) d ((p:ℝ)+q) =
      ((d:ℝ)/(p*q : ℕ))*(s-((p:ℝ)+q)) := by unfold predict; ring
  rw [eqn, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (d:ℝ)/(p*q : ℕ))]

/-- Measuring the error in units of the required d/N precision removes the
prefix length entirely. -/
theorem normalized_error {p q d : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) (pos : 0 < d) (cap : d ≤ (p-1)/2) (s : ℝ) :
    |predict (p*q) d s - (value (p*q) d : ℝ)| / ((d:ℝ)/(p*q : ℕ)) = |s-((p:ℝ)+q)| := by
  rw [error order op oq cap]
  have n : 0 < (p*q : ℕ) := Nat.mul_pos hp.out.pos hq.out.pos
  exact mul_div_cancel_left₀ _ (by positivity)

/-- Substituting twice any integer midpoint meets the strict residue precision
requirement exactly when that midpoint gives the prime sum. -/
theorem integer_midpoint {p q d : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) (pos : 0 < d) (cap : d ≤ (p-1)/2) (m : ℤ) :
    |predict (p*q) d (2*m) - (value (p*q) d : ℝ)| < (d:ℝ)/(p*q : ℕ) ↔ 2*m = (p:ℤ)+q := by
  have n : 0 < (p*q : ℕ) := Nat.mul_pos hp.out.pos hq.out.pos
  have scale : 0 < (d:ℝ)/(p*q : ℕ) := by positivity
  rw [← div_lt_one scale, normalized_error order op oq pos cap]
  constructor
  · intro lt
    obtain ⟨l,u⟩ := abs_lt.mp lt
    have low : -1 < 2*m-((p:ℤ)+q) := by exact_mod_cast l
    have high : 2*m-((p:ℤ)+q) < 1 := by exact_mod_cast u
    omega
  · intro exactSum
    have sum : 2*(m:ℝ)=(p:ℝ)+q := by exact_mod_cast exactSum
    simp [sum]

private theorem geometric_gap (p q : ℕ) :
    (p:ℝ)+q-2*Real.sqrt ((p*q : ℕ) : ℝ) = (Real.sqrt q-Real.sqrt p)^2 := by
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p)]
  nlinarith only [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) p), Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) q)]

/-- The normalized error of twice the public geometric mean is the squared
difference of the prime square roots. -/
theorem geometric_error {p q d : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) (pos : 0 < d) (cap : d ≤ (p-1)/2) :
    |predict (p*q) d (2*Real.sqrt ((p*q : ℕ) : ℝ)) - (value (p*q) d : ℝ)| /
      ((d:ℝ)/(p*q : ℕ)) = (Real.sqrt q-Real.sqrt p)^2 := by
  rw [normalized_error order op oq pos cap, abs_sub_comm, geometric_gap, abs_of_nonneg (sq_nonneg _)]

/-- Whenever the unrounded geometric mean achieves the residue margin, the
very first integer Fermat midpoint already splits the number. -/
theorem geometric_fermat {p q d : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) (pos : 0 < d) (cap : d ≤ (p-1)/2)
    (accurate : |predict (p*q) d (2*Real.sqrt ((p*q : ℕ) : ℝ)) - (value (p*q) d : ℝ)| <
      (d:ℝ)/(p*q : ℕ)) :
    let a := ceilSqrt (p*q)
    let b := (a^2-p*q).sqrt
    (a-b,a+b) = (p,q) := by
  have n : 0 < (p*q : ℕ) := Nat.mul_pos hp.out.pos hq.out.pos
  have scale : 0 < (d:ℝ)/(p*q : ℕ) := by positivity
  rw [← div_lt_one scale, geometric_error order op oq pos cap, ← geometric_gap] at accurate
  obtain ⟨u, hu⟩ := hp.out.odd_of_ne_two op
  obtain ⟨v, hv⟩ := hq.out.odd_of_ne_two oq
  let h := (q-p)/2
  have shape : q=p+2*h := by dsimp [h]; omega
  have hit : (p+h)^2 = p*q+h^2 := by rw [shape]; ring
  have upper : ceilSqrt (p*q) ≤ p+h := ceilSqrt_le_iff.mpr (by omega)
  have atStart := ceilSqrt_le_iff.mp (le_refl (ceilSqrt (p*q)))
  have realStart : Real.sqrt ((p*q : ℕ) : ℝ) ≤ (ceilSqrt (p*q):ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by exact_mod_cast atStart⟩
  have sum : (p:ℝ)+q=2*((p+h : ℕ):ℝ) := by exact_mod_cast (by omega : p+q=2*(p+h))
  have gap : ((p+h : ℕ):ℝ) < (ceilSqrt (p*q):ℝ)+1 := by linarith only [accurate, sum, realStart]
  have start : ceilSqrt (p*q) = p+h := by
    have lt : p+h < ceilSqrt (p*q)+1 := by exact_mod_cast gap
    omega
  dsimp only
  rw [start, hit, Nat.add_sub_cancel_left, Nat.sqrt_eq']
  congr 1 <;> omega

/-- The public first midpoint predicts a sum two below the truth at 2183.
The 0.57 residue reading checked separately was supplied. -/
theorem example_2183 :
    ceilSqrt 2183 = 47 ∧ |predict 2183 16 (2*47) - (value 2183 16 : ℝ)| = 32/2183 ∧
      (47^2-2183 : ℕ) = 26 ∧ (48^2-2183 : ℕ) = 11^2 := by
  rw [CircleMarkChangedResidue.example_2183.2.2.1]
  norm_num [ceilSqrt, predict, abs_of_nonpos]

/-- The geometric accuracy criterion is sufficient for a first Fermat hit.
At 55 the first test succeeds even though the geometric estimate misses the
singleton residue margin. -/
theorem converse_55 :
    ceilSqrt 55 = 8 ∧ (8^2-55 : ℕ) = 3^2 ∧
      1/55 < |predict 55 1 (2*Real.sqrt 55) - (value 55 1 : ℝ)| := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have e := error (p:=5) (q:=11) (d:=1) (by decide) (by decide) (by decide)
    (by decide) (2*Real.sqrt 55)
  norm_num at e
  have root : Real.sqrt 55 < 15/2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  refine ⟨by norm_num [ceilSqrt], by decide, ?_⟩
  rw [e, abs_of_nonpos (by linarith)]
  linarith

end PrimeFactors.CircleMarkResiduePrediction
