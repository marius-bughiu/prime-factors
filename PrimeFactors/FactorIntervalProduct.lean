import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring

/-! Moving a window of consecutive factors. The entering and leaving endpoints give
a sharp bound for univariate polynomial updates required to work at every translation. -/

namespace PrimeFactors.FactorIntervalProduct

open Polynomial
open scoped BigOperators

/-- Offsets `a,…,a+w−1` in a common translation variable. -/
noncomputable def block {R : Type*} [CommRing R] (a w : ℕ) : R[X] :=
  ∏ i ∈ Finset.range w, (X + C ((a + i : ℕ) : R))

theorem degree_block {R : Type*} [CommRing R] [Nontrivial R] (a w : ℕ) :
    (block (R := R) a w).natDegree = w := by
  unfold block
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)]
  simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

theorem block_append {R : Type*} [CommRing R] (a u v : ℕ) :
    block (R := R) a (u+v) = block a u * block (a+u) v := by
  simp only [block, Finset.prod_range_add, Nat.add_assoc]

/-- Exact sliding factorial ratio, cross-multiplied so it is valid over composite moduli.
The shift is `h` and the overlap has length `o`. -/
theorem shift_update {R : Type*} [CommRing R] (a h o : ℕ) :
    block (R := R) (a+h) (h+o) * block a h =
      block a (h+o) * block (a+h+o) h := by
  rw [show block (R := R) (a+h) (h+o) = block (a+h) o * block (a+h+o) h by
    rw [Nat.add_comm h o, block_append]]
  rw [block_append (R := R) a h o]
  ring

/-- The nonwrapped offsets give precisely the zeros at negative integers below `p`. -/
theorem eval_neg_eq_zero_iff {p a w k : ℕ} [Fact p.Prime]
    (fits : a+w ≤ p) (hk : k < p) :
    (block (R := ZMod p) a w).eval (-(k : ZMod p)) = 0 ↔ a ≤ k ∧ k < a+w := by
  simp only [block, eval_prod, Finset.prod_eq_zero_iff, Finset.mem_range,
    eval_add, eval_X, eval_C, neg_add_eq_zero]
  constructor
  · rintro ⟨i, hi, eq⟩
    have castEq := (ZMod.natCast_eq_natCast_iff' _ _ _).mp eq
    rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (show a+i < p by omega)] at castEq
    omega
  · rintro ⟨hl, hu⟩
    refine ⟨k-a, by omega, ?_⟩
    rw [show a + (k-a) = k by omega]

private theorem degree_of_window_zeros {p a d : ℕ} [Fact p.Prime] (fits : a+d ≤ p)
    (P : (ZMod p)[X]) (nonzero : P ≠ 0)
    (zeros : ∀ i < d, P.eval (-((a+i : ℕ) : ZMod p)) = 0) :
    d ≤ P.natDegree := by
  by_contra! low
  let f (i : Fin d) : ZMod p := -((a+i.val : ℕ) : ZMod p)
  apply nonzero
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (f := f)
  · intro i j eq
    have castEq := neg_inj.mp eq
    have residues := (ZMod.natCast_eq_natCast_iff' _ _ _).mp castEq
    rw [Nat.mod_eq_of_lt (show a+i.val < p by have := i.isLt; omega),
      Nat.mod_eq_of_lt (show a+j.val < p by have := j.isLt; omega)] at residues
    exact Fin.ext (by omega)
  · exact fun i => zeros i.val i.isLt
  · simpa using low

/-- Even a one-sided zero detector for a new hit after an old miss must vanish at
`min h w` different translations. Neither exact products nor conditions on old hits
are required. The polynomial is over the hidden prime field. -/
theorem entering_degree {p h w : ℕ} [Fact p.Prime] (fits : h+w ≤ p)
    (P : (ZMod p)[X]) (nonzero : P ≠ 0)
    (detects : ∀ x, (block 0 w).eval x ≠ 0 → (block h w).eval x = 0 → P.eval x = 0) :
    min h w ≤ P.natDegree := by
  apply degree_of_window_zeros (a := max h w) (by omega) P nonzero
  intro i hi
  have under : max h w+i < p := by omega
  apply detects
  · apply mt (eval_neg_eq_zero_iff (a := 0) (w := w) (by omega) under).mp
    omega
  · rw [eval_neg_eq_zero_iff fits under]
    omega

/-- Both sides of a universal rational shift have the same necessary degree bound.
It suffices for their cross-multiplied relation to hold as functions on the finite field. -/
theorem ratio_degrees {p h w : ℕ} [Fact p.Prime] (fits : h+w ≤ p)
    (A B : (ZMod p)[X]) (ha : A ≠ 0) (hb : B ≠ 0)
    (relation : ∀ x, (block h w).eval x * B.eval x = (block 0 w).eval x * A.eval x) :
    min h w ≤ A.natDegree ∧ min h w ≤ B.natDegree := by
  constructor
  · apply entering_degree fits A ha
    intro x old fresh
    simpa [fresh, old] using (relation x).symm
  · apply degree_of_window_zeros (a := 0) (by omega) B hb
    intro i hi
    let x : ZMod p := -((0+i : ℕ) : ZMod p)
    have under : 0+i < p := by omega
    have old : (block (R := ZMod p) 0 w).eval x = 0 :=
      (eval_neg_eq_zero_iff (by omega) under).mpr (by omega)
    have fresh : (block (R := ZMod p) h w).eval x ≠ 0 := by
      apply mt (eval_neg_eq_zero_iff fits under).mp
      omega
    change B.eval x = 0
    simpa [old, fresh] using relation x

private theorem difference_degree_lt {F : Type*} [Field F] {P : F[X]} (c : F)
    (nd : taylor c P - P ≠ 0) :
    (taylor c P - P).natDegree < P.natDegree := by
  have hp : P ≠ 0 := by rintro rfl; simp at nd
  have same : (taylor c P).leadingCoeff = P.leadingCoeff := by
    rw [taylor_apply, leadingCoeff_comp (by rw [natDegree_X_add_C]; decide),
      leadingCoeff_X_add_C, one_pow, mul_one]
  have ht : taylor c P ≠ 0 := leadingCoeff_ne_zero.mp (same ▸ leadingCoeff_ne_zero.mpr hp)
  have hd : (taylor c P).degree = P.degree := by
    rw [degree_eq_natDegree ht, degree_eq_natDegree hp, natDegree_taylor]
  have drop := Polynomial.degree_sub_lt hd ht same
  rw [degree_eq_natDegree nd, degree_eq_natDegree ht, natDegree_taylor] at drop
  exact WithBot.coe_lt_coe.mp drop

/-- A two-valued polynomial classifier on a promised occupied window needs the
entire interpolation degree, even though its behaviour off that window is unrestricted.
The two nonempty parts may have different lengths. Negative offsets agree with `block`. -/
theorem promised_split_degree {p l r : ℕ} [Fact p.Prime] (fits : l+r+2 ≤ p)
    (P : (ZMod p)[X])
    (labels : ∀ i : ℕ, i < l+r+2 →
      P.eval (-(i : ZMod p)) = if i ≤ l then 0 else 1) :
    l+r+1 ≤ P.natDegree := by
  classical
  let D := taylor (-1 : ZMod p) P - P
  have diff (i : ℕ) : D.eval (-(i : ZMod p)) =
      P.eval (-((i+1 : ℕ) : ZMod p))-P.eval (-(i : ZMod p)) := by
    simp [D, taylor_eval, add_comm, neg_add_rev]
  have transition : D.eval (-(l : ZMod p)) = 1 := by
    rw [diff, labels (l+1) (by omega), labels l (by omega)]
    simp
  have nd : D ≠ 0 := by
    intro h
    simp [h] at transition
  let pos (i : Fin (l+r)) := if i.val < l then i.val else i.val+1
  have within (i : Fin (l+r)) : pos i < l+r+1 := by
    dsimp [pos]; split_ifs <;> have := i.isLt <;> omega
  let f (i : Fin (l+r)) : ZMod p := -((pos i : ℕ) : ZMod p)
  have inj : Function.Injective f := by
    intro i j he
    have res := (ZMod.natCast_eq_natCast_iff' _ _ _).mp (neg_inj.mp he)
    rw [Nat.mod_eq_of_lt (show pos i < p by have := within i; omega),
      Nat.mod_eq_of_lt (show pos j < p by have := within j; omega)] at res
    apply Fin.ext
    dsimp [pos] at res
    split_ifs at res <;> omega
  have bound : l+r ≤ D.natDegree := by
    by_contra! h
    apply nd
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero D inj
    · intro i
      have wi := within i
      change D.eval (-((pos i : ℕ) : ZMod p)) = 0
      rw [diff, labels (pos i+1) (by omega), labels (pos i) (by omega)]
      dsimp [pos]; split_ifs <;> simp_all <;> omega
    · simpa using h
  have drop := difference_degree_lt (-1 : ZMod p) nd
  change D.natDegree < P.natDegree at drop
  omega

/-- Ordinary interpolation attains the bound on the promise set. -/
theorem promised_split_exists {p l r : ℕ} [Fact p.Prime] (fits : l+r+2 ≤ p) :
    ∃ P : (ZMod p)[X], P.natDegree = l+r+1 ∧ ∀ i : ℕ, i < l+r+2 →
      P.eval (-(i : ZMod p)) = if i ≤ l then 0 else 1 := by
  classical
  let s := Finset.range (l+r+2)
  let v (i : ℕ) : ZMod p := -(i : ZMod p)
  let y (i : ℕ) : ZMod p := if i ≤ l then 0 else 1
  have inj : Set.InjOn v s := by
    intro a ha b hb eq
    have res := (ZMod.natCast_eq_natCast_iff' _ _ _).mp (neg_inj.mp eq)
    have ha' : a < l+r+2 := Finset.mem_range.mp ha
    have hb' : b < l+r+2 := Finset.mem_range.mp hb
    simpa [Nat.mod_eq_of_lt (lt_of_lt_of_le ha' fits), Nat.mod_eq_of_lt (lt_of_lt_of_le hb' fits)]
      using res
  let P := Lagrange.interpolate s v y
  have labels : ∀ i : ℕ, i < l+r+2 → P.eval (v i) = y i :=
    fun _ hi => Lagrange.eval_interpolate_at_node y inj (Finset.mem_range.mpr hi)
  have upper := natDegree_le_of_degree_le (Lagrange.degree_interpolate_le y inj)
  change P.natDegree ≤ s.card - 1 at upper
  simp [s] at upper
  exact ⟨P, le_antisymm (by omega) (promised_split_degree fits P labels), labels⟩

/-- Two degree-w products give a rational zero/one classifier on the occupied
translations. The denominator is nonzero at every promised point. -/
theorem rational_half_selector {p w i : ℕ} [Fact p.Prime] (fits : 2*w ≤ p) (hi : i < 2*w) :
    let x : ZMod p := -(i : ZMod p)
    let L := (block (R := ZMod p) 0 w).eval x
    let R := (block (R := ZMod p) w w).eval x
    L+R ≠ 0 ∧ L/(L+R) = if i < w then 0 else 1 := by
  dsimp only
  have under : i < p := by omega
  have l := eval_neg_eq_zero_iff (p := p) (a := 0) (w := w) (by omega) under
  have r := eval_neg_eq_zero_iff (p := p) (a := w) (w := w) (by omega) under
  split_ifs with v
  · have hl := l.mpr (by omega)
    have hr := mt r.mp (by omega)
    simp [hl, hr]
  · have hl := mt l.mp (by omega)
    have hr := r.mpr (by omega)
    simp [hl, hr]

/-- Any rational classifier defined on both occupied halves and giving opposite
zero/one answers has numerator degree at least w. Its carrier is required to work
only at the 2w promised offsets. -/
theorem rational_half_degree {p w : ℕ} [Fact p.Prime] (fits : 2*w ≤ p)
    (positive : 0 < w) (A B : (ZMod p)[X])
    (defined : ∀ i < 2*w, B.eval (-(i : ZMod p)) ≠ 0)
    (labels : ∀ i < 2*w, A.eval (-(i : ZMod p)) / B.eval (-(i : ZMod p)) =
      if i < w then 0 else 1) : w ≤ A.natDegree := by
  have nonzero : A ≠ 0 := by
    intro ha
    have endpt := labels w (by omega)
    simp [ha] at endpt
  apply degree_of_window_zeros (a := 0) (by omega) A nonzero
  intro i hi
  have q := labels i (by omega)
  simpa [hi, defined i (by omega)] using q

/-- A unit interval product certifies absence of every nontrivial divisor, for
arbitrary N, without any assumption about its prime factorization. -/
theorem excludes_of_unit {N a w d : ℕ}
    (unit : Nat.gcd N (∏ i ∈ Finset.range w, (a+i)) = 1)
    (lo : a ≤ d) (hi : d < a+w) (nontrivial : 1 < d) : ¬ d ∣ N := by
  intro divides
  have inside : d-a ∈ Finset.range w := Finset.mem_range.mpr (by omega)
  have dh := Finset.dvd_prod_of_mem (fun i => a+i) inside
  dsimp only at dh
  rw [show a+(d-a) = d by omega] at dh
  have common := Nat.dvd_gcd divides dh
  rw [unit, Nat.dvd_one] at common
  omega

/-- On the complete public band [107,150], the equal halves give an exclusion and a
proper factor. Multiplication of the two residues yields the same factor already. -/
theorem two_halves_example :
    let prodFrom := fun a w : ℕ => ∏ i ∈ Finset.range w, (a+i)
    (2*106^2 < 22663 ∧ 22663 ≤ 2*107^2 ∧ 150^2 ≤ 22663 ∧ 22663 < 151^2) ∧
    prodFrom 107 22 % 22663 = 7083 ∧ Nat.gcd 22663 7083 = 1 ∧
    prodFrom 129 22 % 22663 = 12969 ∧ Nat.gcd 22663 12969 = 131 ∧
    prodFrom 107 44 % 22663 = 6288 ∧ Nat.gcd 22663 6288 = 131 ∧
    Nat.gcd 22663 (7083+12969) = 1 ∧ 2228*(7083+12969)%22663 = 7083 ∧
    Nat.gcd 22663 2228 = 1 ∧ Nat.gcd 22663 (2228-1) = 131 ∧
    Nat.Prime 131 ∧ Nat.Prime 173 ∧ 131*173 = 22663 := by decide +kernel

theorem left_half_excludes {d : ℕ} (lo : 107 ≤ d) (hi : d < 129) : ¬ d ∣ 22663 := by
  exact excludes_of_unit (a := 107) (w := 22) (by decide +kernel) lo hi (by omega)

end PrimeFactors.FactorIntervalProduct
