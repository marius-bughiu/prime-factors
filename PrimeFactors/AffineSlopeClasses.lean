import PrimeFactors.ModularHyperbola
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PrimeFactors.AffineSlopeClasses

open Finset

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- Low digits traverse all units, so their inverses do too. With `c = -N`
this is precisely the collection of slopes of the high-digit graphs. -/
noncomputable def slopes (c : G) : Finset G := univ.image fun u => c * u ^ 2

/-- Every slope is repeated once per square root of unity. -/
theorem slope_count (c : G) :
    Fintype.card G = (slopes c).card * (univ.filter fun t : G => t ^ 2 = 1).card := by
  classical
  let f (u : G) := c*u^2
  have fiber (s : G) (hs : s ∈ slopes c) :
      (univ.filter fun u : G => f u = s).card = (univ.filter fun t : G => t ^ 2 = 1).card := by
    obtain ⟨v, _, rfl⟩ := mem_image.mp hs
    apply card_nbij' (fun u => u/v) (fun t => t*v)
    · intro u hu
      have e : u^2 = v^2 := mul_left_cancel (mem_filter.mp hu).2
      simp [div_pow,e]
    · intro t ht
      simp [f, mul_pow,(mem_filter.mp ht).2]
    · intro u _
      simp
    · intro t _
      simp
  calc
    Fintype.card G = ∑ s ∈ slopes c, (univ.filter fun u : G => f u = s).card := by
      simpa only [card_univ] using (card_eq_sum_card_fiberwise (s:=univ) (t:=slopes c)
        (f:=f) (fun _ hu => mem_image_of_mem _ hu))
    _ = _ := by simp [sum_congr rfl fiber]

/-- Reflection of one coordinate multiplies a slope by `e = -1`, and
exchanging the coordinates inverts a unit slope. Translations are free. -/
noncomputable def orientations (e a : G) : Finset G := {a, e*a, a⁻¹, e*a⁻¹}

omit [Fintype G] in
theorem orientation_count_le (e a : G) : (orientations e a).card ≤ 4 := by
  exact card_insert_le .. |>.trans <| Nat.succ_le_succ <| (card_insert_le ..).trans <|
    Nat.succ_le_succ <| (card_insert_le ..).trans <| by simp

/-- A collection of graph types covering every low digit incurs this count
before any cost for arithmetic on the graphs or locating their rectangles. -/
theorem graph_cover (c e : G) (types : Finset G)
    (cover : slopes c ⊆ types.biUnion (orientations e)) :
    Fintype.card G ≤ types.card * 4 * (univ.filter fun t : G => t ^ 2 = 1).card := by
  rw [slope_count c]
  apply Nat.mul_le_mul_right
  exact (card_le_card cover).trans (card_biUnion_le_card_mul _ _ _ fun a _ => orientation_count_le e a)

/-- On the product graph, recording the first coordinate modulo A and the
second modulo B distinguishes exactly the first-coordinate classes modulo
their least common multiple. This also permits shared prime factors in A,B. -/
theorem asymmetric_low_digits {A B x y x' y' : ℕ}
    (same : x*y ≡ x'*y' [MOD B]) (unitX : B.Coprime x') (unitY : B.Coprime y) :
    (x ≡ x' [MOD A] ∧ y ≡ y' [MOD B]) ↔ x ≡ x' [MOD A.lcm B] := by
  constructor
  · rintro ⟨hx,hy⟩
    exact Nat.mod_lcm hx (Nat.ModEq.cancel_right_of_coprime unitY
      (same.trans (hy.symm.mul_left x')))
  · intro hx
    exact ⟨hx.of_dvd (Nat.dvd_lcm_left ..), Nat.ModEq.cancel_left_of_coprime unitX
      (((hx.of_dvd (Nat.dvd_lcm_right ..)).symm.mul_right y).trans same)⟩

/-- The symmetric square of the joint radix checks at least the product
precision of the two asymmetric radices. -/
theorem square_refines {A B s n : ℕ} (h : s ≡ n [MOD (A.lcm B)^2]) :
    s ≡ n [MOD A*B] := by
  exact h.of_dvd (by simpa [sq] using
    (Nat.mul_dvd_mul (Nat.dvd_lcm_left A B) (Nat.dvd_lcm_right A B)))

-- The products below run over the first 95 or 96 primes, respectively.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem primorial_cutoffs :
    let P := (range 504).filter Nat.Prime
    let Q := (range 503).filter Nat.Prime
    P.card = 96 ∧ Q.card = 95 ∧ 2^685 < ∏ p ∈ P, p ∧
      (∏ p ∈ Q, p) < 12 * ∏ p ∈ Q, (p-1) := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- For the actual 2048-bit policy the radix is 320 times the first 94
primes. Dividing its totient by 2^95 counts its slopes. -/
theorem chosen_radix_cutoffs :
    let P := (range 492).filter Nat.Prime
    let W := ∏ p ∈ P, p
    let S := 320 * (∏ p ∈ P, (p-1)) / 2^95
    P.card = 94 ∧ W ≤ 2^680 ∧ 2^680 < 499*W ∧ 2^684/W = 320 ∧
      2^585 < S ∧ S + 2^95 < 2^586 := by decide +kernel

theorem finite_type_lower_bound {R units torsion types : ℕ}
    (large : 2^683 ≤ R) (density : R < 12*units)
    (roots : torsion ≤ 2^96) (cover : units ≤ types*4*torsion) : 2^581 < types := by
  have h := Nat.mul_le_mul_left (types*4) roots
  omega

end PrimeFactors.AffineSlopeClasses
