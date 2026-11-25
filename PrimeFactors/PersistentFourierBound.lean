import PrimeFactors.PersistentLocalSurvivors

namespace PrimeFactors.PersistentFourierBound

open PersistentLocalSurvivors

/-- The affine hyperbola that counts square roots above each midpoint is
parametrized once by the nonzero field elements. This change of variables
converts every nonzero Fourier coefficient to a Kloosterman sum and a
correction from the ramified points. -/
noncomputable def hyperbolaEquiv {F : Type*} [Field F] {n : F} (unit : n≠0) (two : (2:F)≠0) :
    {z : F × F // z.2^2 = z.1^2-n} ≃ {x : F // x≠0} where
  toFun z := ⟨z.val.1+z.val.2,by
    have pair : (z.val.1+z.val.2)*(z.val.1-z.val.2)=n := by linear_combination -z.property
    intro zero; exact unit (by simpa [zero] using pair.symm)⟩
  invFun x := ⟨((x.val+n/x.val)/2,(x.val-n/x.val)/2),by
    dsimp; field_simp [two,x.property]; ring⟩
  left_inv z := by
    have pair : (z.val.1+z.val.2)*(z.val.1-z.val.2)=n := by linear_combination -z.property
    have nz : z.val.1+z.val.2≠0 := by intro zero; exact unit (by simpa [zero] using pair.symm)
    have partner : n/(z.val.1+z.val.2)=z.val.1-z.val.2 := (div_eq_iff nz).mpr (by rw [mul_comm,pair])
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> rw [partner] <;> field_simp <;> ring
  right_inv x := by
    apply Subtype.ext; dsimp; field_simp; ring

theorem weighted_hyperbola {F R : Type*} [Field F] [Fintype F] [DecidableEq F]
    [AddCommMonoid R] {n : F} (unit : n≠0) (two : (2:F)≠0) (weight : F → R) :
    ∑ z : {z : F × F // z.2^2 = z.1^2-n}, weight z.val.1 =
      ∑ x : {x : F // x≠0}, weight ((x.val+n/x.val)/2) :=
  ((hyperbolaEquiv unit two).symm.sum_comp (fun z => weight z.val.1)).symm



/-- Odd primes with regular discriminant classes used in the completion.
The dyadic and triadic periods are handled separately. -/
noncomputable def oddModuli : Finset ℕ := (smallPrimes 1109).filter (5≤·)

noncomputable def modulus : ℕ := ∏ p ∈ oddModuli, p

noncomputable def densityNum : ℕ := ∏ p ∈ oddModuli, (p-3)

noncomputable def densityDen : ℕ := ∏ p ∈ oddModuli, (2*p)

/-- A fourteen-bit upper bound for 256 times the square root. Taking the
bits from largest to smallest makes the numerical certificate kernel-reducible. -/
def rootUpper (p : ℕ) : ℕ :=
  let lower := (List.range 14).reverse.foldl (fun r bit =>
    let trial := r+2^bit
    if trial^2 ≤ 65536*p then trial else r) 0
  lower+1

noncomputable def relativeErrorNum : ℕ := ∏ p ∈ oddModuli,
  (256*(p-3)+2*p*(256+rootUpper p))

noncomputable def relativeErrorDen : ℕ := ∏ p ∈ oddModuli, (256*(p-3))

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 4096 in
/-- The numerical portion of the Fourier completion bound. The first strict
comparison keeps 90% of the main term for the actual input density; the
second gives a lower bound on that main term at the minimum possible density. -/
theorem completion_arithmetic :
    (∀ p ∈ oddModuli, 65536*p < (rootUpper p)^2) ∧
    oddModuli.card = 184 ∧
    2^1557 ≤ modulus ∧ modulus < 2^1558 ∧
    10*1559*relativeErrorNum < (2^1019/3456)*relativeErrorDen ∧
    5*(2^819+1)*densityDen < 32*(2^1019/3456)*densityNum := by decide +kernel

private noncomputable def accepted (p h : ℕ) : Bool :=
  let d := (h%p)^2+p-(713%p)
  ((List.range p).any (fun a => a^2%p == d%p)) && d%p != 0

private noncomputable def center (active : Bool) (p m h : ℕ) : ℤ :=
  if active then (if accepted p h then (p:ℤ) else 0)-m else m

/-- This integer is 385 times one exact-conductor contribution.
Centering a local indicator suppresses its zero Fourier frequency. -/
private noncomputable def contribution (d : ℕ) : ℤ :=
  ((List.range 137).map (fun t =>
    let h := 27+3456*t
    center (d%5==0) 5 2 h * center (d%7==0) 7 3 h * center (d%11==0) 11 4 h)).sum

set_option maxRecDepth 8192 in
/-- Independent enumeration of the surviving midpoints and the centered
expansion. The last identity uses the prime product 385 as denominator. -/
theorem short_completion :
    ([1,5,7,11,35,55,77,385].map contribution) =
      [3288,72,16,-54,-16,-6,138,-358] ∧
    ((List.range 137).filter (fun t =>
      let h := 27+3456*t
      accepted 5 h && accepted 7 h && accepted 11 h)).length = 8 ∧
    (3288+72+16-54-16-6+138-358:ℤ) = 8*385 := by decide +kernel

end PrimeFactors.PersistentFourierBound
