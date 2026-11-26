import PrimeFactors.FoldedFactorial
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-! Certify an entire rectangle of unit candidates by a polynomial identity.
All arithmetic takes place in the coefficient ring, including when the
coefficient ring is the integers modulo a composite. -/

namespace PrimeFactors.FactorialBlockExclusion

open Polynomial Finset
open scoped Polynomial

variable {R ι κ : Type*} [CommRing R]

noncomputable def offsetPolynomial (offsets : Finset ι) (offset : ι → R) : R[X] :=
  ∏ i ∈ offsets, (X + C (offset i))

noncomputable def nodePolynomial (nodes : Finset κ) (point : κ → R) : R[X] :=
  ∏ j ∈ nodes, (X - C (point j))

theorem at_node (nodes : Finset κ) (point : κ → R) {j : κ} (hj : j ∈ nodes) :
    (nodePolynomial nodes point).eval (point j) = 0 := by
  rw [nodePolynomial, eval_prod]
  exact Finset.prod_eq_zero hj (by simp)

theorem node_monic (nodes : Finset κ) (point : κ → R) :
    (nodePolynomial nodes point).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- Evaluation at a root of B gives an explicit inverse at that point. -/
theorem unit_at_root {A B U V : R[X]} (identity : U * A + V * B = 1)
    {x : R} (root : B.eval x = 0) : IsUnit (A.eval x) := by
  apply isUnit_of_mul_eq_one_right (U.eval x)
  simpa only [eval_add, eval_mul, root, mul_zero, add_zero, eval_one] using
    congrArg (fun F : R[X] => F.eval x) identity

/-- Extend a certificate by one node using a scalar inverse of A(b).
The new quotient is exact, including when a previous node equals b. -/
theorem append_node {A B U V : R[X]} {b c : R}
    (identity : U*A + V*B = 1) (value : V.eval b = c * A.eval b) :
    (U + C c*B)*A + ((V - C c*A) /ₘ (X-C b)) * (B*(X-C b)) = 1 := by
  have root : IsRoot (V - C c*A) b := by
    simp only [IsRoot.def, eval_sub, eval_mul, eval_C, value, sub_self]
  have exactDiv := mul_divByMonic_eq_iff_isRoot.mpr root
  calc
    _ = U*A + (C c*A + (X-C b)*((V - C c*A) /ₘ (X-C b)))*B := by ring
    _ = 1 := by rw [exactDiv]; simpa using identity

/-- For a monic B, one can verify U alone by taking a polynomial remainder. -/
theorem identity_of_remainder {A B U : R[X]} (monic : B.Monic)
    (check : (U * A) %ₘ B = 1) : ∃ V : R[X], U * A + V * B = 1 := by
  refine ⟨-((U*A) /ₘ B), ?_⟩
  have decomp := modByMonic_add_div (U*A) monic
  rw [check] at decomp
  linear_combination -decomp

/-- A monic nonconstant node polynomial requires only the coefficients of
one inverse of degree strictly below its own degree. This uses monic
division over the original ring and needs no divisions between its nodes. -/
theorem exists_short_inverse [Nontrivial R] {A B : R[X]} (monic : B.Monic)
    (nonconstant : B ≠ 1) (cop : IsCoprime A B) :
    ∃ U : R[X], U.natDegree < B.natDegree ∧ (U*A) %ₘ B = 1 := by
  obtain ⟨U,V,identity⟩ := cop
  refine ⟨U %ₘ B, natDegree_modByMonic_lt U monic nonconstant, ?_⟩
  apply (div_modByMonic_unique (-(V+(U /ₘ B)*A)) 1 monic ?_).2
  constructor
  · linear_combination -identity - A * (modByMonic_add_div U monic)
  · simpa using monic.degree_pos.mpr nonconstant

theorem rectangle_units {offsets : Finset ι} {nodes : Finset κ}
    {offset : ι → R} {point : κ → R} {U V : R[X]}
    (identity : U * offsetPolynomial offsets offset + V * nodePolynomial nodes point = 1)
    {i : ι} (hi : i ∈ offsets) {j : κ} (hj : j ∈ nodes) :
    IsUnit (point j + offset i) := by
  have unit := unit_at_root identity (at_node nodes point hj)
  rw [offsetPolynomial, eval_prod] at unit
  have single := isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ hi) unit
  simpa using single

/-- Existence is exact, even when distinct indices have the same value or
the difference between two evaluation points is a zero divisor. -/
theorem rectangle_iff (offsets : Finset ι) (nodes : Finset κ) (offset : ι → R)
    (point : κ → R) :
    IsCoprime (offsetPolynomial offsets offset) (nodePolynomial nodes point) ↔
      ∀ i ∈ offsets, ∀ j ∈ nodes, IsUnit (point j + offset i) := by
  constructor
  · rintro ⟨U,V,h⟩ i hi j hj
    exact rectangle_units h hi hj
  · intro h
    apply IsCoprime.prod_left
    intro i hi
    apply IsCoprime.prod_right
    intro j hj
    have unit : IsUnit (point j - (-offset i)) := by simpa using h i hi j hj
    simpa using (isCoprime_X_sub_C_of_isUnit_sub unit).symm

/-- For a nonempty rectangle of unit candidates, a witness with at most
`nodes.card` coefficients suffices; offsets and nodes determine both moduli. -/
theorem compact_rectangle [Nontrivial R] (offsets : Finset ι) (nodes : Finset κ)
    (offset : ι → R) (point : κ → R) (nonempty : nodes.Nonempty)
    (units : ∀ i ∈ offsets, ∀ j ∈ nodes, IsUnit (point j + offset i)) :
    ∃ U : R[X], U.natDegree < nodes.card ∧
      (U * offsetPolynomial offsets offset) %ₘ nodePolynomial nodes point = 1 := by
  have degree : (nodePolynomial nodes point).natDegree = nodes.card := by
    rw [nodePolynomial, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (point i))]
    simp
  have pos : 0 < (nodePolynomial nodes point).natDegree := by
    rw [degree]
    exact nonempty.card_pos
  have monic := node_monic nodes point
  simpa [degree] using exists_short_inverse monic (monic.natDegree_pos.mp pos)
    ((rectangle_iff offsets nodes offset point).mpr units)

/-- A public identity excludes every integer in the rectangle for modulus n. -/
theorem rectangle_coprime {n : ℕ} {offsets : Finset ι} {nodes : Finset κ}
    {offset : ι → ℕ} {point : κ → ℕ} {U V : (ZMod n)[X]}
    (identity : U * offsetPolynomial offsets (fun i => (offset i : ZMod n)) +
      V * nodePolynomial nodes (fun j => (point j : ZMod n)) = 1)
    {i : ι} (hi : i ∈ offsets) {j : κ} (hj : j ∈ nodes) :
    (point j + offset i).Coprime n := by
  apply (ZMod.isUnit_iff_coprime _ _).mp
  simpa only [Nat.cast_add] using rectangle_units identity hi hj

/-- The list form allows a coefficient-arithmetic verifier to supply the two
monic products in their construction order, including repeated entries. -/
theorem list_rectangle {n : ℕ} {offsets nodes : List ℕ} {U V : (ZMod n)[X]}
    (identity : U * (offsets.map (fun a : ℕ => X + C (a : ZMod n))).prod +
      V * (nodes.map (fun b : ℕ => X - C (b : ZMod n))).prod = 1)
    {a b : ℕ} (ha : a ∈ offsets) (hb : b ∈ nodes) : (b+a).Coprime n := by
  have root : ((nodes.map (fun v : ℕ => X - C (v : ZMod n))).prod).eval (b : ZMod n) = 0 := by
    rw [eval_list_prod]
    apply List.prod_eq_zero
    apply List.mem_map.mpr
    exact ⟨_, List.mem_map_of_mem hb, by simp⟩
  have unit := unit_at_root identity root
  rw [eval_list_prod] at unit
  apply (ZMod.isUnit_iff_coprime _ _).mp
  apply isUnit_of_dvd_unit _ unit
  apply List.dvd_prod
  apply List.mem_map.mpr
  exact ⟨_, List.mem_map_of_mem ha, by simp⟩

/-- One block contains `height` wheel cycles. Each pair in the offset
set is a cycle number within that block and a retained wheel residue. -/
theorem wheel_rectangle {n base wheel height : ℕ} {residues blocks : Finset ℕ}
    {U V : (ZMod n)[X]}
    (identity : U * offsetPolynomial ((range height) ×ˢ residues)
      (fun t => (↑(wheel*t.1+t.2) : ZMod n)) +
      V * nodePolynomial blocks (fun j => (↑(base+wheel*(height*j)) : ZMod n)) = 1)
    {j k r : ℕ} (hj : j ∈ blocks) (hk : k < height) (hr : r ∈ residues) :
    (base + wheel*(height*j+k) + r).Coprime n := by
  have hit := rectangle_coprime identity (i := (k,r))
    (Finset.mem_product.mpr ⟨mem_range.mpr hk, hr⟩) hj
  convert hit using 1
  ring

/-- One quadratic address j(j+1) covers both reflected wheel blocks. -/
theorem reflected_units {a b : R} {offsets : Finset ι} {nodes : Finset κ}
    {offset : ι → R} {index : κ → R} {U V : R[X]}
    (identity : U * FoldedFactorial.folded a b offsets offset +
      V * nodePolynomial nodes (fun j => index j * (index j + 1)) = 1)
    {i : ι} (hi : i ∈ offsets) {j : κ} (hj : j ∈ nodes) :
    IsUnit (a + offset i + b * index j) ∧
    IsUnit (a + offset i - b * (index j + 1)) := by
  have unit := unit_at_root identity (at_node _ _ hj)
  rw [FoldedFactorial.folded_eval] at unit
  exact ⟨isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun t => a+offset t+b*index j) hi)
      (isUnit_of_mul_isUnit_left unit),
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun t => a+offset t-b*(index j+1)) hi)
      (isUnit_of_mul_isUnit_right unit)⟩

/-- Twelve integers in three consecutive two-cycle blocks of the 6-wheel.
The polynomial Euclidean algorithm modulo the public input 16003 supplied
these six-degree identity coefficients, using no prime factors. -/
theorem checked_twelve {a b : ℕ} (ha : a ∈ [1,5,7,11]) (hb : b ∈ [24,36,48]) :
    (b+a).Coprime 16003 := by
  let x : (ZMod 16003)[X] := X
  apply list_rectangle (U := 8172+14696*x+12609*x^2)
    (V := 9710+100*x+1231*x^2+3394*x^3) _ ha hb
  have char : (16003 : (ZMod 16003)[X]) = 0 := by
    calc
      _ = C (↑(16003:ℕ) : ZMod 16003) := (map_natCast C 16003).symm
      _ = C 0 := congrArg C (ZMod.natCast_self 16003)
      _ = 0 := map_zero _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    map_natCast, x]
  linear_combination (-24967+2648*X-2325*X^2-7886*X^3+958*X^4-3*X^5+X^6) * char

end PrimeFactors.FactorialBlockExclusion
