import PrimeFactors.ReciprocalDivisorSums
import PrimeFactors.PrimePower

/-! If the product is a unit square modulo an odd modulus, all local factor
pairs with the same sum have the same Jacobi sign on their factors. For a
modulus congruent to three modulo four, requiring positive sign therefore
halves the ordinary modular discriminant sieve over a complete period. -/

namespace PrimeFactors.ReciprocalTraceHalving

open ReciprocalSumCharacter ReciprocalDivisorSums TraceFoldedRight Finset

variable {d : ℕ} [NeZero d]

private theorem glue {a b : ℤ} (same : ∀ r, r.Prime → r ∣ d →
    jacobiSym a r = jacobiSym b r) : jacobiSym a d = jacobiSym b d := by
  have nz (r : ℕ) (hr : r ∈ d.primeFactorsList) : r ≠ 0 :=
    (Nat.prime_of_mem_primeFactorsList hr).ne_zero
  rw [← Nat.prod_primeFactorsList (NeZero.ne d), jacobiSym.list_prod_right nz,
    jacobiSym.list_prod_right nz]
  exact congrArg List.prod (List.map_congr_left fun r hr =>
    same r (Nat.prime_of_mem_primeFactorsList hr) (Nat.dvd_of_mem_primeFactorsList hr))

/-- Even at a repeated prime of the modulus, all roots of the trace equation
have the same Jacobi character when the product is a square unit. -/
theorem same_sign (n x y : (ZMod d)ˣ) (square : IsSquare (n : ZMod d))
    (equal : trace n x = trace n y) : sign (x : ZMod d) = sign (y : ZMod d) := by
  apply glue
  intro r prime dv
  letI : Fact r.Prime := ⟨prime⟩
  let π := ZMod.castHom dv (ZMod r)
  have reduce (u : (ZMod d)ˣ) :
      jacobiSym (u : ZMod d).valMinAbs r = sign (π (u : ZMod d)) := by
    rw [← sign_cast]
    congr 1
    have h := congrArg π (ZMod.coe_valMinAbs (u : ZMod d))
    rwa [map_intCast] at h
  rw [reduce, reduce]
  have z := congrArg π ((trace_iff n x y).mp equal)
  simp only [map_mul, map_sub, map_zero] at z
  rcases mul_eq_zero.mp z with h | h
  · rw [sub_eq_zero.mp h]
  · have first := sub_eq_zero.mp h
    have pair : π (x : ZMod d) * π (y : ZMod d) = π (n : ZMod d) := by
      rw [first, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]
    obtain ⟨e, he⟩ := square
    have hsign := congrArg sign pair
    rw [he, map_mul, sign_mul, sign_mul] at hsign
    have sx := ReciprocalDivisorClasses.unit_sign (Units.map π.toMonoidHom x)
    have sy := ReciprocalDivisorClasses.unit_sign (Units.map π.toMonoidHom y)
    change sign (π (x : ZMod d)) = 1 ∨ sign (π (x : ZMod d)) = -1 at sx
    change sign (π (y : ZMod d)) = 1 ∨ sign (π (y : ZMod d)) = -1 at sy
    rcases sx with hx | hx <;> rcases sy with hy | hy <;> rw [hx,hy] at hsign ⊢ <;>
      first | rfl | nlinarith [sq_nonneg (sign (π e))]

/-- The ordinary sieve on factor sums checks the discriminant against all
squares modulo the same modulus, including zero and nonunit squares. -/
noncomputable def ordinary (n : (ZMod d)ˣ) : Finset (ZMod d) := by
  classical
  exact univ.filter fun s => IsSquare (s^2 - 4*(n : ZMod d))

theorem mem_ordinary {n : (ZMod d)ˣ} {s : ZMod d} (odd : Odd d) :
    s ∈ ordinary n ↔ ∃ x : (ZMod d)ˣ, trace n x = s := by
  classical
  have two : IsUnit (2 : ZMod d) := (ZMod.isUnit_iff_coprime 2 d).mpr odd.coprime_two_left
  simp only [ordinary, mem_filter, mem_univ, true_and, ← admissibleSum_iff_isSquare_of_two_unit two]
  constructor
  · rintro ⟨a,b,prod,sum⟩
    have good : IsUnit (a*b) := prod ▸ n.isUnit
    obtain ⟨x,rfl⟩ := (IsUnit.mul_iff.mp good).1
    refine ⟨x, ?_⟩
    rw [trace, ← prod, mul_right_comm, Units.mul_inv, one_mul, sum]
  · rintro ⟨x,rfl⟩
    exact ⟨x,(n : ZMod d)*(↑(x⁻¹) : ZMod d),
      by rw [mul_left_comm, Units.mul_inv, mul_one], rfl⟩

private theorem positive_of {n x : (ZMod d)ˣ} (hx : sign (x : ZMod d) = 1) :
    trace n x ∈ sums n :=
  mem_image.mpr ⟨x, mem_filter.mpr ⟨mem_univ _,hx⟩,rfl⟩

/-- Under the two public square certificates, the possible factor sums belong to
`sums` by `ReciprocalDivisorSums.covers`. Its cardinality is exactly half of
the ordinary square-discriminant image over this entire modulus. -/
theorem exact_half (hd : d % 4 = 3) (n : (ZMod d)ˣ) (square : IsSquare (n : ZMod d)) :
    2 * (sums n).card = (ordinary n).card := by
  classical
  have odd : Odd d := Nat.odd_iff.mpr (by omega)
  let A := sums n
  let B := A.image (fun x : ZMod d => -x)
  have partition : ordinary n = A ∪ B := by
    ext s
    rw [mem_ordinary odd, mem_union]
    constructor
    · rintro ⟨x,rfl⟩
      rcases ReciprocalDivisorClasses.unit_sign x with h | h
      · exact Or.inl (positive_of h)
      · right
        have hp : sign ((-x : (ZMod d)ˣ) : ZMod d) = 1 := by
          change sign (-(x : ZMod d)) = 1
          rw [sign_neg hd,h,neg_neg]
        exact mem_image.mpr ⟨_, positive_of hp, by rw [neg_local_sum, neg_neg]⟩
    · rintro (h | h)
      · obtain ⟨x,_,eq⟩ := mem_image.mp h
        exact ⟨x,eq⟩
      · obtain ⟨t,ht,rfl⟩ := mem_image.mp h
        obtain ⟨x,_,rfl⟩ := mem_image.mp ht
        exact ⟨-x,neg_local_sum ..⟩
  have disj : Disjoint A B := by
    rw [disjoint_left]
    intro s hs hneg
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hneg
    obtain ⟨x,hx,eq⟩ := mem_image.mp hs
    obtain ⟨y,hy,rfl⟩ := mem_image.mp ht
    have hx' : sign (x : ZMod d) = 1 := (mem_filter.mp hx).2
    have hy' : sign (y : ZMod d) = 1 := (mem_filter.mp hy).2
    have impossible := same_sign n x (-y) square (eq.trans (neg_local_sum n y).symm)
    change sign (x : ZMod d) = sign (-(y : ZMod d)) at impossible
    rw [sign_neg hd, hx', hy'] at impossible
    contradiction
  have negCount : B.card = A.card := card_image_of_injective _ neg_injective
  rw [partition,card_union_of_disjoint disj,negCount,two_mul]

end PrimeFactors.ReciprocalTraceHalving
