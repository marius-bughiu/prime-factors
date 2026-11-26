import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Sqrt
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum

/-! A single polynomial address for several affine blocks, valid at every offset.
The first two power sums detect the linear strides even over a composite modulus. -/
namespace PrimeFactors.AffineFactorialAddress

open Polynomial
variable {R : Type*} [CommRing R]

private noncomputable def line (r : R × R) : R[X] := C r.1 + C r.2 * X

/-- The outer variable is the common offset. The inner variable is the block index. -/
noncomputable def blocks (rows : List (R × R)) : (R[X])[X] :=
  (rows.map fun r => X + C (line r)).prod

/-- Each coefficient in the offset has a polynomial expression in the same address. -/
def Shared (rows : List (R × R)) (u : R[X]) : Prop :=
  ∀ j, ∃ f : R[X], (blocks rows).coeff j = f.comp u

private noncomputable def revBlocks (rows : List (R × R)) : (R[X])[X] :=
  (rows.map fun r => 1 + C (line r) * X).prod

private theorem deg_blocks (rows : List (R × R)) : (blocks rows).natDegree ≤ rows.length := by
  induction rows with
  | nil => simp [blocks]
  | cons r rows ih =>
    change ((X+C (line r))*blocks rows).natDegree ≤ rows.length+1
    exact natDegree_mul_le.trans (by
      have h : (X+C (line r)).natDegree≤1 := by compute_degree
      omega)

private theorem reverse (rows : List (R × R)) :
    reflect rows.length (blocks rows) = revBlocks rows := by
  induction rows with
  | nil => simp [blocks,revBlocks]
  | cons r rows ih =>
    change reflect (rows.length+1) ((X+C (line r))*blocks rows) =
      (1+C (line r)*X)*revBlocks rows
    have d : (X+C (line r)).natDegree≤1 := by compute_degree
    rw [Nat.add_comm rows.length 1, reflect_mul _ _ d (deg_blocks rows), ih, reflect_add]
    simp

private theorem reverse_shared {rows : List (R × R)} {u : R[X]} (h : Shared rows u) (j : ℕ) :
    ∃ f : R[X], (revBlocks rows).coeff j = f.comp u := by
  rw [←reverse, coeff_reflect]
  exact h _

private theorem power_sums (rows : List (R × R)) :
    (revBlocks rows).coeff 0 = 1 ∧
    (revBlocks rows).coeff 1 = (rows.map line).sum ∧
    ((revBlocks rows).coeff 1)^2 - 2*(revBlocks rows).coeff 2 =
      (rows.map fun r => (line r)^2).sum := by
  induction rows with
  | nil => simp [revBlocks, coeff_one]
  | cons r rows ih =>
    have step : revBlocks (r::rows) = revBlocks rows + (C (line r)*revBlocks rows)*X := by
      change (1+C (line r)*X)*revBlocks rows=_; ring
    simp only [step, coeff_add, coeff_mul_X_zero, add_zero, coeff_mul_X, coeff_C_mul,
      ih.1, mul_one, List.map_cons, List.sum_cons]
    refine ⟨trivial, by rw [ih.2.1,add_comm], ?_⟩
    rw [←ih.2.2]
    ring

private theorem low_comp {f u : R[X]} (unit : IsUnit u.leadingCoeff) {d : ℕ}
    (big : d < u.natDegree) (small : (f.comp u).natDegree≤d) :
    f.comp u = C (f.coeff 0) := by
  by_cases hf : f.natDegree=0
  · rw [eq_C_of_natDegree_eq_zero hf, C_comp]
    simp
  have nz : f.leadingCoeff * u.leadingCoeff ^ f.natDegree ≠ 0 := by
    intro h
    have h' : f.leadingCoeff=0 := (unit.pow _).mul_left_eq_zero.mp h
    exact hf (by simp [leadingCoeff_eq_zero.mp h'])
  rw [natDegree_comp_eq_of_mul_ne_zero nz] at small
  have bound : u.natDegree ≤ f.natDegree*u.natDegree := by
    simpa using Nat.mul_le_mul_right u.natDegree (show 1≤f.natDegree by omega)
  omega

private theorem line_sq (r : R × R) : (line r)^2 =
    C (r.1^2) + C (2*r.1*r.2)*X + C (r.2^2)*X^2 := by
  simp only [line,map_mul,map_ofNat,map_pow]
  ring

private theorem slope_coeffs (rows : List (R × R)) :
    ((rows.map line).sum).coeff 1 = (rows.map Prod.snd).sum ∧
    ((rows.map fun r => (line r)^2).sum).coeff 2 = (rows.map fun r => r.2^2).sum := by
  induction rows with
  | nil => simp
  | cons r rows ih =>
    simp only [List.map_cons,List.sum_cons,coeff_add,ih.1,ih.2]
    rw [line_sq]
    simp only [line, coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
    norm_num

private theorem power_degrees (rows : List (R × R)) :
    (rows.map line).sum.natDegree ≤ 1 ∧ (rows.map fun r => (line r)^2).sum.natDegree ≤ 2 := by
  induction rows with
  | nil => simp
  | cons r rows ih =>
    simp only [List.map_cons,List.sum_cons]
    have ld : (line r).natDegree ≤ 1 := by unfold line; compute_degree
    exact ⟨(natDegree_add_le _ _).trans (max_le ld ih.1),
      (natDegree_add_le _ _).trans (max_le (natDegree_pow_le.trans (by omega)) ih.2)⟩

/-- A shared address of degree at least two requires the signed strides to sum to zero. -/
theorem sum_zero {rows : List (R × R)} {u : R[X]} (unit : IsUnit u.leadingCoeff)
    (shared : Shared rows u) (large : 1<u.natDegree) : (rows.map Prod.snd).sum = 0 := by
  obtain ⟨f,h⟩ := reverse_shared shared 1
  have eq := (power_sums rows).2.1.symm.trans h
  have val := low_comp unit large (eq ▸ (power_degrees rows).1)
  rw [←(slope_coeffs rows).1, eq, val]
  simp

/-- A shared address of degree at least three requires the sum of squared strides to vanish. -/
theorem squares_zero {rows : List (R × R)} {u : R[X]} (unit : IsUnit u.leadingCoeff)
    (shared : Shared rows u) (large : 2<u.natDegree) : (rows.map fun r => r.2^2).sum = 0 := by
  obtain ⟨f,hf⟩ := reverse_shared shared 1
  obtain ⟨g,hg⟩ := reverse_shared shared 2
  have eq : (rows.map fun r => (line r)^2).sum = (f^2 - C 2*g).comp u := by
    rw [←(power_sums rows).2.2, hf,hg,sub_comp,pow_comp,mul_comp,C_comp]
    simp only [map_ofNat]
  have val := low_comp unit large (eq ▸ (power_degrees rows).2)
  rw [←(slope_coeffs rows).2, eq,val]
  simp

/-- Interpolation in the common offset: a separate reading polynomial at each
of at least m+1 distinct offsets already gives the common coefficient representation. -/
theorem shared_of_offsets {K : Type*} [Field K] (rows : List (K × K)) (u : K[X])
    (offsets : Finset K) (enough : rows.length<offsets.card) (read : K→K[X])
    (cert : ∀ x ∈ offsets, (blocks rows).eval (C x) = (read x).comp u) :
    Shared rows u := by
  classical
  let basis (x : K) := Lagrange.basis offsets id x
  let fit : (K[X])[X] := ∑ x ∈ offsets, C ((read x).comp u) * (basis x).map C
  have inj : Set.InjOn (id : K→K) offsets := Function.injective_id.injOn
  have size : 0<offsets.card := by omega
  have fitdeg : fit.natDegree ≤ offsets.card-1 := by
    apply natDegree_sum_le_of_forall_le
    intro x hx
    apply (natDegree_C_mul_le _ _).trans
    apply natDegree_map_le.trans
    exact (natDegree_eq_of_degree_eq_some (Lagrange.degree_basis inj hx)).le
  have interp : blocks rows = fit := by
    apply eq_of_degrees_lt_of_eval_index_eq offsets
      (v := (C : K→K[X])) (C_injective.injOn)
    · exact (degree_le_natDegree.trans_lt (Nat.cast_lt.mpr ((deg_blocks rows).trans_lt enough)))
    · exact degree_le_natDegree.trans_lt (Nat.cast_lt.mpr (by omega))
    · intro x hx
      rw [cert x hx]
      dsimp [fit]
      simp only [eval_finset_sum,eval_mul,eval_C,eval_map,eval₂_at_apply]
      rw [Finset.sum_eq_single_of_mem x hx]
      · have e : (basis x).eval x=1 := Lagrange.eval_basis_self inj hx
        rw [e,map_one,mul_one]
      · intro y _ hy
        have e : (basis y).eval x=0 := Lagrange.eval_basis_of_ne (v:=id) hy hx
        rw [e,map_zero,mul_zero]
  intro j
  refine ⟨∑ x ∈ offsets, read x * C ((basis x).coeff j), ?_⟩
  rw [interp]
  simp only [fit,finset_sum_coeff,coeff_C_mul,coeff_map,sum_comp,mul_comp,C_comp]

/-- Modulo N the integer sum of the squared strides must then be a multiple
of the whole modulus, including when N has several distinct prime factors. -/
theorem integer_bound (n : ℕ) (rows : List (ℤ × ℤ)) (u : (ZMod n)[X])
    (unit : IsUnit u.leadingCoeff)
    (shared : Shared (rows.map fun r => ((r.1 : ZMod n), (r.2 : ZMod n))) u)
    (positive : 0 < (rows.map fun r => r.2^2).sum)
    (small : (rows.map fun r => r.2^2).sum < (n:ℤ)) : u.natDegree ≤ 2 := by
  by_contra! large
  have reduce : (((rows.map fun r => r.2^2).sum : ℤ) : ZMod n) =
      ((rows.map fun r => ((r.1 : ZMod n), (r.2 : ZMod n))).map fun r => r.2^2).sum := by
    clear shared positive small
    induction rows with
    | nil => simp
    | cons r rows ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_pow]
      rw [ih]
  have dvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp
    (reduce.trans (squares_zero unit shared large))
  exact (not_le_of_gt small) (Int.le_of_dvd positive dvd)

/-- Nonzero common stride up to sign rules out all higher-degree shared addresses
whenever the row count is nonzero in the ring and the stride is a unit. -/
theorem common_stride {rows : List (R × R)} {b : R} {u : R[X]}
    (signed : ∀ r ∈ rows, r.2=b ∨ r.2= -b)
    (stride : IsUnit b) (count : (rows.length:R)≠0) (unit : IsUnit u.leadingCoeff)
    (shared : Shared rows u) : u.natDegree ≤ 2 := by
  have squares (l : List (R × R)) (h : ∀ r ∈ l, r.2=b ∨ r.2= -b) :
      (l.map fun r => r.2^2).sum = (l.length:R)*b^2 := by
    induction l with
    | nil => simp
    | cons r l ih =>
      have v : r.2^2=b^2 := by
        rcases h r (by simp) with h|h <;> simp [h]
      simp only [List.map_cons,List.sum_cons,v,List.length_cons,Nat.cast_add,Nat.cast_one]
      rw [ih (fun x hx => h x (by simp [hx]))]
      ring
  by_contra! long
  have z := squares_zero unit shared long
  rw [squares rows signed] at z
  exact count ((stride.pow 2).mul_left_eq_zero.mp z)

/-- Node at which the folded block factor for offset r vanishes. -/
def node {K : Type*} [Field K] (a b r : K) : K := (a+r)*(a+r-b)/b^2

theorem node_difference {K : Type*} [Field K] (a b r s : K) :
    node a b r - node a b s = (r-s)*(2*a-b+r+s)/b^2 := by
  unfold node
  ring

theorem node_reachable {K : Type*} [Field K] (a b r : K) (hb : b≠0) :
    let j := (a+r)/b-1; node a b r = j*(j+1) := by
  dsimp [node]
  field_simp
  ring

/-- After checking a short public interval, even a polynomial required only
to vanish at the relevant folded nodes needs one degree per retained offset. -/
theorem folded_root_bound (p a b : ℕ) [Fact p.Prime] (sb : 0<b) (bp : b<p)
    (mid : b≤2*a) (off : Finset ℕ) (within : ∀ r ∈ off, r<b)
    (precheck : ∀ z ∈ Finset.Icc (2*a-b) (2*a+b-2), ¬p∣z)
    (F : (ZMod p)[X]) (nz : F≠0)
    (accept : ∀ r ∈ off, F.eval (node (a:ZMod p) b r)=0) : off.card≤F.natDegree := by
  classical
  let address (r : ℕ) := node (a:ZMod p) b r
  have units : (b:ZMod p)≠0 := fun h =>
    Nat.not_dvd_of_pos_of_lt sb bp ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h)
  have inj : Set.InjOn address off := by
    intro r hr s hs eq
    have rb := within r hr
    have sb' := within s hs
    have diff := node_difference (a:ZMod p) b r s
    have z : ((r:ZMod p)-s) * (2*(a:ZMod p)-b+r+s)=0 := by
      rw [show node (a:ZMod p) b r = node (a:ZMod p) b s from eq,sub_self] at diff
      exact (div_eq_zero_iff.mp diff.symm).resolve_right (pow_ne_zero _ units)
    rcases mul_eq_zero.mp z with same | bad
    · have h := (ZMod.natCast_eq_natCast_iff' r s p).mp (sub_eq_zero.mp same)
      simpa [Nat.mod_eq_of_lt (rb.trans bp), Nat.mod_eq_of_lt (sb'.trans bp)] using h
    · have nmem : 2*a-b+r+s ∈ Finset.Icc (2*a-b) (2*a+b-2) := by
        rw [Finset.mem_Icc]; omega
      apply False.elim (precheck _ nmem _)
      apply (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp
      simpa only [Nat.cast_add,Nat.cast_sub mid,Nat.cast_mul,Nat.cast_ofNat] using bad
  have subset : off.image address ⊆ F.roots.toFinset := by
    intro x hx
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hx
    exact Multiset.mem_toFinset.mpr ((mem_roots nz).mpr (accept r hr))
  rw [←Finset.card_image_of_injOn inj]
  exact (Finset.card_le_card subset).trans ((Multiset.toFinset_card_le _).trans F.card_roots')

/-- Concrete units permit a cubic fold outside the small-stride bound.
At index 3 and offset 1 it yields a proper factor, although the first linear term is a unit. -/
theorem cubic_example (x t : ZMod 91) :
    (x+t)*(x+9*t)*(x-10*t)=x^3+t^3 := by
  have e : (91 : ZMod 91)=0 := by decide
  linear_combination -(t^2*x + t^3)*e

theorem cubic_example_gcd : Nat.gcd (1+3) 91 = 1 ∧ Nat.gcd (1^3+3^3) 91 = 7 ∧
    91 = 7*13 ∧ Nat.Prime 7 ∧ Nat.Prime 13 := by decide

/-- A collision in a folded block really can supply a factor. The equal-width
smaller-factor interval for this product is [90,106], with midpoint 98. -/
theorem collision_example :
    (11413+126)/127 = 90 ∧ Nat.sqrt 11413 = 106 ∧
    Nat.gcd ((98+9)*(98+9-10) - (98+7)*(98+7-10)) 11413 = 101 ∧
    11413 = 101*113 ∧ Nat.Prime 101 ∧ Nat.Prime 113 := by
  exact ⟨by decide, (Nat.eq_sqrt.mpr (by decide)).symm, by decide, by decide⟩

end PrimeFactors.AffineFactorialAddress
