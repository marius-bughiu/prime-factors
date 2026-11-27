import PrimeFactors.ReciprocalTraceHalving
import PrimeFactors.SaturatedTraceSplit

/-! The two offsets of a factor sum need not be units modulo the full period.
Over a suitable split of the modulus, taking opposite offsets on the two
parts recovers the Jacobi character of the factor. -/

namespace PrimeFactors.ReciprocalAdaptiveCharacter

open ReciprocalSumCharacter TraceFoldedRight

/-- The character determined by integer representatives of the two offsets. -/
def splitTag (u v : ℕ) (minus plus : ℤ) : ℤ := jacobiSym minus u * jacobiSym plus v

private theorem sign_of_unit_offset {r : ℕ} [NeZero r] (x : (ZMod r)ˣ)
    {b t : ZMod r} (hb : IsUnit b) (h : (x : ZMod r) * b = t^2) :
    sign (x : ZMod r) = sign b := by
  obtain ⟨y,rfl⟩ := hb
  have hsign := congrArg sign h
  rw [pow_two, sign_mul, sign_mul] at hsign
  rcases ReciprocalDivisorClasses.unit_sign x with hx | hx <;>
    rcases ReciprocalDivisorClasses.unit_sign y with hy | hy <;>
    rw [hx, hy] at hsign ⊢ <;> first | rfl | nlinarith [sq_nonneg (sign t)]

private theorem reduction {d r : ℕ} (dv : r ∣ d) (a : ℤ) (x : ZMod d)
    (h : (a : ZMod d) = x) :
    jacobiSym a r = sign (ZMod.castHom dv (ZMod r) x) := by
  rw [← sign_cast, ← h, map_intCast]

/-- Any integer representatives work. The selected offset must be a unit on
its own component. Even coprimality of the components is optional here. -/
theorem splitTag_trace {d u v : ℕ} [NeZero d] (n x : (ZMod d)ˣ) (e : ZMod d)
    (square : e^2 = (n : ZMod d)) (product : u*v = d)
    (minus plus : ℤ) (hm : (minus : ZMod d) = trace n x - 2*e)
    (hp : (plus : ZMod d) = trace n x + 2*e)
    (mu : IsUnit (minus : ZMod u)) (pu : IsUnit (plus : ZMod v)) :
    splitTag u v minus plus = sign (x : ZMod d) := by
  have nz := NeZero.ne d
  letI : NeZero u := ⟨fun h => nz (by rw [← product, h, zero_mul])⟩
  letI : NeZero v := ⟨fun h => nz (by rw [← product, h, mul_zero])⟩
  have du : u ∣ d := ⟨v, product.symm⟩
  have dv : v ∣ d := ⟨u, by rw [mul_comm,product]⟩
  have cleared : (x : ZMod d) * trace n x = (x : ZMod d)^2 + e^2 := by
    rw [trace,square]
    linear_combination (n : ZMod d) * (Units.mul_inv x)
  have loc {r : ℕ} [NeZero r] (dr : r ∣ d) (b : ℤ) (ok : IsUnit (b : ZMod r))
      (t : ZMod d) (ht : (x : ZMod d)*(b : ZMod d) = t^2) :
      jacobiSym b r = jacobiSym (x : ZMod d).valMinAbs r := by
    let π := ZMod.castHom dr (ZMod r)
    have h := congrArg π ht
    rw [map_mul, map_intCast, map_pow] at h
    rw [← sign_cast b, reduction dr _ _ (ZMod.coe_valMinAbs (x : ZMod d))]
    exact (sign_of_unit_offset (Units.map π.toMonoidHom x) ok h).symm
  have m : (x : ZMod d)*(minus : ZMod d) = ((x : ZMod d)-e)^2 := by
    rw [hm]; linear_combination cleared
  have p : (x : ZMod d)*(plus : ZMod d) = ((x : ZMod d)+e)^2 := by
    rw [hp]; linear_combination cleared
  rw [splitTag, loc du minus mu _ m, loc dv plus pu _ p, ← jacobiSym.mul_right]
  change jacobiSym _ (u*v) = jacobiSym _ d
  rw [product]

/-- Compute the complete character directly from the two residues. The seed
is the nonnegative representative of the minus offset, and the plus offset
is represented by adding four times the public root to that same seed. -/
def tag {d : ℕ} (e s : ZMod d) : ℤ :=
  let z := (s-(e+e)).val
  let part := SaturatedTraceSplit.v d z
  splitTag (d / part) part z (z+4*e.val : ℕ)

/-- The canonical, computable character agrees with the hidden factor sign
on every attainable sum. There is no assumption of squarefreeness on d. -/
theorem tag_trace {d : ℕ} [NeZero d] (odd : Odd d) (n : (ZMod d)ˣ)
    (e : ZMod d) (square : e^2 = (n : ZMod d)) (x : (ZMod d)ˣ) :
    tag e (trace n x) = sign (x : ZMod d) := by
  simp only [tag, ← two_mul]
  let z := (trace n x - 2*e).val
  have isUnitE : IsUnit e := (IsUnit.mul_iff.mp
    (show IsUnit (e*e) by rw [← pow_two, square]; exact n.isUnit)).1
  have copE : e.val.Coprime d := (ZMod.isUnit_iff_coprime _ _).mp (by simpa using isUnitE)
  obtain ⟨product, _, hm, hp⟩ := SaturatedTraceSplit.split_spec (z := z)
    (NeZero.pos d) (Nat.coprime_mul_iff_left.mpr ⟨odd.coprime_two_left, copE⟩)
  apply splitTag_trace n x e square product (z : ℤ) (z+4*e.val : ℕ)
  · simp [z]
  · push_cast
    simp only [z, ZMod.natCast_zmod_val]
    ring
  · simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime _ _).mpr hm
  · simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime _ _).mpr hp

end PrimeFactors.ReciprocalAdaptiveCharacter
