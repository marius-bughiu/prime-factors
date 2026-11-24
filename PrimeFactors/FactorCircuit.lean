import PrimeFactors.BitMarginals
import PrimeFactors.ReverseSweep

namespace PrimeFactors

open ReverseSweep

/-- One vector of reverse weights from a scalar-output circuit at unit tags. -/
noncomputable def factorGradient {b n : ℕ} (t : Circuit (ZMod 3) b n) (o : Fin n) : Fin b → ZMod 3 :=
  (trace t (fun _ => 1)).pullback (bump (fun _ => 0) o 1)

/-- A circuit must represent the tagged multiplication polynomial, at least on
each coordinate line. A known nonzero scalar multiplier is allowed. Equality
only at the all-ones point would not imply this property. -/
def RepresentsBitTags {b n : ℕ} (t : Circuit (ZMod 3) b n) (o : Fin n)
    (N B : ℕ) (scale : ZMod 3) : Prop :=
  ∀ i : Fin b, polynomialValues t (fun j => if j = i then Polynomial.X else 1) o =
    Polynomial.C scale * bitTagPartition N B b
      (fun j => if j = i.val then Polynomial.X else 1)

theorem gradient_eq_scaled_marginal {b n N B : ℕ} (t : Circuit (ZMod 3) b n)
    (o : Fin n) {scale : ZMod 3} (rep : RepresentsBitTags t o N B scale) (i : Fin b) :
    factorGradient t o i = scale * bitMarginal N B i := by
  let z := fun j : Fin b => if j = i then (Polynomial.X : Polynomial (ZMod 3)) else 1
  have x : (fun j => (z j).eval 1) = fun _ => 1 := by
    funext j
    by_cases h : j = i <;> simp [z, h]
  have v : (fun j => (z j).derivative.eval 1) = fun j => if j = i then 1 else 0 := by
    funext j
    by_cases h : j = i <;> simp [z, h]
  have h := output_derivative t z 1 o
  rw [x, v, show polynomialValues t z o = _ from rep i] at h
  simp only [Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
    derivative_bitTagPartition N B b i i.isLt] at h
  simpa [factorGradient, pairing, mul_ite] using h

/-- The sum of the ordinary place values read from a single reverse sweep. -/
theorem factorGradient_sum {b n p q B : ℕ} (t : Circuit (ZMod 3) b n) (o : Fin n)
    {scale : ZMod 3} (nonzero : scale ≠ 0) (rep : RepresentsBitTags t o (p*q) B scale)
    (hp : p.Prime) (hq : q.Prime) (ordered : p < q) (inside : q < B)
    (upper : B ≤ p*q) (width : q < 2^b) :
    ∑ i : Fin b, 2^i.val * ((factorGradient t o i) / scale).val = p + q := by
  simp_rw [gradient_eq_scaled_marginal t o rep, mul_div_cancel_left₀ _ nonzero]
  rw [Fin.sum_univ_eq_sum_range (fun i => 2^i * (bitMarginal (p*q) B i).val)]
  exact sumFromBitMarginals_semiprime hp hq ordered inside upper width

end PrimeFactors
