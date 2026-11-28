import PrimeFactors.WeightedStride

/-!
# The exact modulo-24 filter for weighted factor sums

When the product is coprime to six, every candidate first coordinate is a unit
modulo 24. Each unit is its own inverse. The possible weighted sums therefore
form one orbit under multiplication by the units. A gcd identifies that orbit.
-/

namespace PrimeFactors.QuotientStripLevelMod24

private theorem unit_square (x : ZMod 24) (h : x.val.Coprime 24) : x*x=1 := by
  exact (by decide +kernel : ∀ t : ZMod 24, t.val.Coprime 24 → t*t=1) x h

/-- The eight units modulo 24 act transitively on each gcd class. -/
theorem orbit (c z : ZMod 24) :
    (∃ x : ZMod 24, x.val.Coprime 24 ∧ c*x=z) ↔ z.val.gcd 24=c.val.gcd 24 := by
  exact (by decide +kernel : ∀ c z : ZMod 24,
    (∃ x : ZMod 24, x.val.Coprime 24 ∧ c*x=z) ↔ z.val.gcd 24=c.val.gcd 24) c z

/-- A label survives exactly when its residue can occur in a local factor pair.
This criterion concerns multiplication modulo 24. -/
theorem exact_labels (N u v z : ZMod 24) (unitN : N.val.Coprime 24) :
    (∃ x y : ZMod 24, x*y=N ∧ u*x+v*y=z) ↔ z.val.gcd 24=(u+v*N).val.gcd 24 := by
  rw [← orbit]
  constructor
  · rintro ⟨x,y,prod,label⟩
    have xu : x.val.Coprime 24 := by
      have prop : ∀ a b : ZMod 24, (a*b).val.Coprime 24 → a.val.Coprime 24 := by decide +kernel
      exact prop x y (prod ▸ unitN)
    refine ⟨x,xu,?_⟩
    calc
      (u+v*N)*x = u*x+v*y*(x*x) := by rw [← prod]; ring
      _ = z := by rw [unit_square x xu, mul_one, label]
  · rintro ⟨x,xu,h⟩
    refine ⟨x,x*N,?_,?_⟩
    · rw [← mul_assoc,unit_square x xu,one_mul]
    · rw [← h]
      ring

/-- At product 35 with direction (4,3), the public maximal single
progression also admits multiples of 3. The full local image excludes them. -/
theorem strictly_finer :
    3 % weightedStride 35 4 3 = (4+3*35) % weightedStride 35 4 3 ∧
      ¬ (∃ x y : ZMod 24, x*y=35 ∧ 4*x+3*y=3) := by
  decide +kernel

end PrimeFactors.QuotientStripLevelMod24
