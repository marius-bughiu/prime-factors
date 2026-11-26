import PrimeFactors.GeometricMatchMoments
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.ReduceModChar

/-! The single direction −1 in a geometric product keeps its first surviving
coefficient over each hidden prime, provided no matching index is −1 there. -/

namespace PrimeFactors.GeometricNegativeDirection
open Finset Polynomial GeometricMatchMoments

/-- The scalar coefficient with direction fixed at −1. -/
noncomputable def coefficient {R : Type*} [CommRing R] (W : ℕ) (y g : R) (r : ℕ) : R :=
  (∏ i ∈ range (W+1), directionalFactor y g (-1) i).coeff r

noncomputable def hits {R : Type*} [CommRing R] [DecidableEq R] (W : ℕ) (y g : R) : Finset ℕ :=
  (range (W+1)).filter fun i => g^i=y

/-- Scalar coefficient extraction commutes with reducing the parameters. -/
theorem map_coefficient {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    (W : ℕ) (y g : R) (r : ℕ) :
    f (coefficient W y g r) = coefficient W (f y) (f g) r := by
  unfold coefficient
  rw [← coeff_map, Polynomial.map_prod]
  simp only [directionalFactor, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, Polynomial.map_one,
    map_pow, map_mul, map_neg, map_one, Polynomial.map_neg]

/-- Every hit contributes at least one zero factor of the perturbation variable. -/
theorem below {R : Type*} [CommRing R] [DecidableEq R] (W : ℕ) (y g : R)
    {k : ℕ} (hk : k < (hits W y g).card) : coefficient W y g k = 0 := by
  let H := hits W y g
  have sub : H ⊆ range (W+1) := filter_subset _ _
  apply (first_product_coefficient sub (fun i => directionalFactor y g (-1) i) _).1 k hk
  intro i hi
  have h : g^i=y := (mem_filter.mp hi).2
  rw [coeff_zero_eq_eval_zero]
  simp [directionalFactor, h]

/-- The first possible coefficient is nonzero exactly when every matching
index avoids −1 in the residue field. All coefficients below the number of
matches vanish, including when a matching index is −1. -/
theorem first_possible {K : Type*} [Field K] [DecidableEq K] (W : ℕ) (y g : K) (ny : y≠0) :
    let H := hits W y g
    (∀ k < H.card, coefficient W y g k = 0) ∧
      (coefficient W y g H.card ≠ 0 ↔ ∀ i ∈ H, (i:K) ≠ -1) := by
  let S := range (W+1)
  let H := hits W y g
  have sub : H ⊆ S := filter_subset _ _
  have hit (i : ℕ) (hi : i∈H) : g^i=y := (mem_filter.mp hi).2
  have outside (i : ℕ) (hi : i∈S \ H) : y-g^i ≠ 0 := by
    apply sub_ne_zero.mpr
    intro eq
    exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨(mem_sdiff.mp hi).1, eq.symm⟩)
  have unit : (∏ i ∈ S \ H, (y-g^i)) * y^H.card ≠ 0 :=
    mul_ne_zero (prod_ne_zero_iff.mpr outside) (pow_ne_zero _ ny)
  constructor
  · exact fun _ hk => below W y g hk
  · change ((∏ i ∈ S, directionalFactor y g (-1) i).coeff H.card ≠ 0) ↔ _
    rw [directional_reading sub y g (-1) hit, mul_ne_zero_iff, and_iff_right unit, prod_ne_zero_iff]
    simp only [sub_ne_zero, ne_comm (a := (-1:K))]
    rfl

/-- If W+1<p no possible index is congruent to −1. Thus one fixed direction
measures the exact local multiplicity for every nonzero target. -/
theorem first_order {p W : ℕ} [Fact p.Prime] (room : W+1<p) (y g : ZMod p) (ny : y≠0) :
    let r := (hits W y g).card
    (∀ k < r, coefficient W y g k = 0) ∧ coefficient W y g r ≠ 0 := by
  obtain ⟨low, leading⟩ := first_possible W y g ny
  refine ⟨low, leading.mpr ?_⟩
  intro i hi eq
  have bound := mem_range.mp (mem_filter.mp hi).1
  have z : ((i+1:ℕ):ZMod p)=0 := by rw [Nat.cast_add, Nat.cast_one, eq, neg_add_cancel]
  have dvd := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp z
  have := Nat.le_of_dvd (Nat.zero_lt_succ i) dvd
  omega

/-- If the p-side count is smaller, then at that order the coefficient is
nonzero modulo p and vanishes modulo q. The gcd of this one public residue
is exactly q. Only the p-side needs the bound on W. -/
theorem unequal_gcd {p q W : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (y g : ZMod (p*q)) (room : W+1<p) :
    let e := ZMod.chineseRemainder cop
    let rp := (hits W (e y).1 (e g).1).card
    let rq := (hits W (e y).2 (e g).2).card
    (e y).1≠0 → rp<rq → (p*q).gcd (coefficient W y g rp).val = q := by
  let e := ZMod.chineseRemainder cop
  let f := (RingHom.fst (ZMod p) (ZMod q)).comp e.toRingHom
  let h := (RingHom.snd (ZMod p) (ZMod q)).comp e.toRingHom
  intro _ rp rq yp lt
  let v := coefficient W y g rp
  have left : f v ≠ 0 := (map_coefficient f W y g rp) ▸ (first_order room (f y) (f g) yp).2
  have right : h v = 0 := (map_coefficient h W y g rp).trans (below W (h y) (h g) lt)
  have P : (v.val:ZMod p)=f v := by rw [← map_natCast f, ZMod.natCast_zmod_val]
  have Q : (v.val:ZMod q)=h v := by rw [← map_natCast h, ZMod.natCast_zmod_val]
  apply Nat.gcd_mul_of_coprime_of_dvd
  · apply hp.out.coprime_iff_not_dvd.mpr
    intro divides
    exact left (P.symm.trans ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr divides))
  · exact (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp (Q.trans right)

/-- An integer digit supplied by a public acquisition only has to agree with
the integer coefficient modulo N. Its gcd with N then returns the higher-count
prime even if the representative of the digit is negative. -/
theorem digit_gcd {p q W : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (y g digit : ℤ) (room : W+1<p) (yp : (y:ZMod p) ≠ 0) :
    let rp := (hits W (y:ZMod p) (g:ZMod p)).card
    let rq := (hits W (y:ZMod q) (g:ZMod q)).card
    rp < rq → digit ≡ coefficient W y g rp [ZMOD (p:ℤ)*q] → (p*q).gcd digit.natAbs=q := by
  intro rp rq lt eq
  have projected (l : ℕ) (d : (l:ℤ) ∣ (p:ℤ)*q) :
      (digit:ZMod l)=coefficient W (y:ZMod l) (g:ZMod l) rp := by
    apply ((ZMod.intCast_eq_intCast_iff ..).mpr (eq.of_dvd d)).trans
    exact map_coefficient (Int.castRingHom (ZMod l)) W y g rp
  have lp := projected p (dvd_mul_right ..)
  have lq := projected q (dvd_mul_left ..)
  apply Nat.gcd_mul_of_coprime_of_dvd
  · apply hp.out.coprime_iff_not_dvd.mpr
    intro h
    exact (first_order room (y:ZMod p) (g:ZMod p) yp).2 (lp.symm.trans
      ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (Int.natCast_dvd.mpr h)))
  · apply Int.natCast_dvd.mp
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (lq.trans (below W (y:ZMod q) (g:ZMod q) lt))

/-- Full public interval [365,386] for 33127=157·211. Base 12 is lifted by
one exponentiation to the 33127th power. A single negative-direction product
modulo N³ returns digit 29202, whose gcd is 157. -/
theorem example_33127 :
    (12:ZMod 36353507819383)^33127 = 21047812126195 ∧
    (21047812126195:ZMod 36353507819383)^32763 = 15412069234561 ∧
    (∏ i ∈ range 22, ((15412069234561:ZMod 36353507819383)*(1-33127) -
       (21047812126195*(1+33127))^i)) = 32046220163058 ∧
    33127^3=(36353507819383:ℕ) ∧ 33127^2*29202=(32046220163058:ℕ) ∧
    Nat.gcd 33127 29202=157 ∧ 157*211=(33127:ℕ) := by
  exact ⟨by reduce_mod_char, by reduce_mod_char, by decide +kernel, rfl, rfl, by decide +kernel, rfl⟩

end PrimeFactors.GeometricNegativeDirection
