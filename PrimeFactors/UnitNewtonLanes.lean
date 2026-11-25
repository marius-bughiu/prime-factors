import PrimeFactors.DifferenceLane
import Mathlib.Data.Int.GCD

namespace PrimeFactors.UnitNewtonLanes
open Finset

/-- The jth monic Newton polynomial on any prescribed integral nodes. -/
noncomputable def basis (nodes : ℕ → ℤ) (j : ℕ) (x : ℤ) : ℤ :=
  ∏ i ∈ range j, (x-nodes i)

private theorem at_earlier (nodes : ℕ → ℤ) {i j : ℕ} (h : i < j) :
    basis nodes j (nodes i) = 0 :=
  prod_eq_zero (mem_range.mpr h) (sub_self _)

private theorem transfer {M c v w : ℤ} (minimum : (M.gcd v : ℤ) ∣ w)
    (atNode : M ∣ c*v) : M ∣ c*w := by
  obtain ⟨t, ht⟩ := minimum
  rw [ht, Int.gcd_eq_gcd_ab]
  have fromM : M ∣ M*(c*Int.gcdA M v*t) := dvd_mul_right _ _
  have fromV : M ∣ (c*v)*(Int.gcdB M v*t) := dvd_mul_of_dvd_left atNode _
  convert dvd_add fromM fromV using 1
  ring

/-- If each diagonal attains minimal divisibility on a set, the d+1 node
evaluations certify a degree-d Newton expansion everywhere on that set. -/
theorem grid_iff {M : ℤ} {d : ℕ} (nodes c : ℕ → ℤ) (S : Set ℤ)
    (inside : ∀ j ≤ d, nodes j ∈ S)
    (minimum : ∀ j ≤ d, ∀ x ∈ S, (M.gcd (basis nodes j (nodes j)) : ℤ) ∣ basis nodes j x) :
    (∀ i ≤ d, M ∣ ∑ j ∈ range (d+1), c j * basis nodes j (nodes i)) ↔
      ∀ x ∈ S, M ∣ ∑ j ∈ range (d+1), c j * basis nodes j x := by
  constructor
  · intro grid
    have terms (i : ℕ) (hi : i ≤ d) : ∀ x ∈ S, M ∣ c i * basis nodes i x := by
      induction i using Nat.strong_induction_on with
      | h i ih =>
        have first : (∑ j ∈ range (i+1), c j * basis nodes j (nodes i)) =
            ∑ j ∈ range (d+1), c j * basis nodes j (nodes i) := by
          apply sum_subset (range_mono (by omega))
          intro j _ outside
          rw [at_earlier nodes (show i < j by simpa using outside), mul_zero]
        have sumAt := grid i hi
        rw [← first, sum_range_succ] at sumAt
        have before : M ∣ ∑ j ∈ range i, c j * basis nodes j (nodes i) := by
          apply dvd_sum
          intro j hj
          have smaller := mem_range.mp hj
          exact ih j smaller (by omega) (nodes i) (inside i hi)
        exact fun x hx => transfer (minimum i hi x hx) ((dvd_add_right before).mp sumAt)
    exact fun x hx => dvd_sum fun j hj => terms j (Nat.le_of_lt_succ (mem_range.mp hj)) x hx
  · exact fun all i hi => all (nodes i) (inside i hi)

/-- Four simultaneous nodes match the ordered 3-adic and 5-adic units. -/
private noncomputable def exampleValue (x : ℤ) := (x-1)*(x-2)*(x-13)*(x-14)

theorem example_modulus :
    (∀ x : Fin 45, x.val.Coprime 15 → 45 ∣ exampleValue x.val) ∧
    ¬(45 ∣ exampleValue 3) ∧ exampleValue 16 = 45*28 := by decide +kernel

/-- Extra exponent in the determinant margin from omitting zero modulo p.
The terms beyond a=j vanish for p≥2. -/
noncomputable def extra (p d : ℕ) : ℕ :=
  ∑ j ∈ range (d+1), ∑ a ∈ range (j+1),
    (j/((p-1)*p^a) - j/p^(a+1))

theorem small_margins :
    (3:ℕ)^(extra 3 4) * 5^(extra 5 4) = 45 ∧
    (3:ℕ)^(extra 3 6) * 5^(extra 5 6) * 7^(extra 7 6) = 8505 ∧
    (3:ℕ)^(extra 3 8) * 5^(extra 5 8) * 7^(extra 7 8) = 10333575 := by
  decide +kernel

/-- At degree four the Dickson weights yield a squared product bounded by
2^(6+2049*2+2045*4). Combining it with the quartic margin saves one radix bit. -/
theorem quartic_dickson_scale :
    let right := 5^5 * 2^(10+6+2049*2+2045*4)
    let factorialAndUnits := 1*1*2*6*24*45
    right < (2:ℕ)^(2*614*10)*factorialAndUnits^2 ∧
      (2:ℕ)^(2*613*10)*factorialAndUnits^2 ≤ right := by decide +kernel

end PrimeFactors.UnitNewtonLanes
