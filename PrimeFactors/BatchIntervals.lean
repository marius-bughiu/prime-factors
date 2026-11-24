import Mathlib.Data.List.Prime
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- Canonical nodes of the interval tree on offset ranks. A pair records
(left endpoint, length). The requested slice is half-open. -/
def batchTiles (lo hi : ℕ) : (base height : ℕ) → List (ℕ × ℕ)
  | a, 0 => if lo ≤ a ∧ a < hi then [(a, 1)] else []
  | a, h+1 =>
    if hi ≤ a ∨ a + 2^(h+1) ≤ lo then []
    else if lo ≤ a ∧ a + 2^(h+1) ≤ hi then [(a, 2^(h+1))]
    else batchTiles lo hi a h ++ batchTiles lo hi (a+2^h) h

/-- No rank outside the requested slice appears, and every requested
rank inside the ambient block appears exactly once. -/
theorem batchTiles_exact (lo hi a h i : ℕ) :
    ((batchTiles lo hi a h).countP (fun v => decide (v.1 ≤ i ∧ i < v.1+v.2))) =
      if a ≤ i ∧ i < a+2^h ∧ lo ≤ i ∧ i < hi then 1 else 0 := by
  induction h generalizing a with
  | zero =>
    simp only [batchTiles, pow_zero]
    split <;> simp [List.countP, List.countP.go] <;> split_ifs <;> omega
  | succ h ih =>
    simp only [batchTiles]
    split
    · simp only [List.countP_nil]
      split_ifs <;> omega
    · split
      · simp [List.countP, List.countP.go]
        split_ifs <;> omega
      · rw [List.countP_append, ih, ih]
        simp only [pow_succ]
        split_ifs <;> omega

/-- All pieces have dyadic width and alignment relative to the root,
so a piece at a given rank is the same polynomial at every block start. -/
theorem batchTiles_aligned (lo hi a h : ℕ) (v : ℕ × ℕ) (hv : v ∈ batchTiles lo hi a h) :
    ∃ e ≤ h, ∃ k : ℕ, v = (a+2^e*k,2^e) := by
  induction h generalizing a with
  | zero =>
    simp only [batchTiles] at hv
    split at hv
    · exact ⟨0, by omega, 0, by simpa using hv⟩
    · simp at hv
  | succ h ih =>
    simp only [batchTiles] at hv
    split at hv
    · simp at hv
    · split at hv
      · exact ⟨h+1, by omega, 0, by simpa using hv⟩
      · rcases List.mem_append.mp hv with hl | hr
        · obtain ⟨e,he,k,hk⟩ := ih a hl
          exact ⟨e,by omega,k,hk⟩
        · obtain ⟨e,he,k,hk⟩ := ih (a+2^h) hr
          obtain ⟨m,hm⟩ := Nat.pow_dvd_pow 2 he
          exact ⟨e,by omega,m+k,by rw [hk,hm,Nat.mul_add,Nat.add_assoc]⟩

private def batchBoundary (a b u : ℕ) : ℕ :=
  if a < u ∧ u < b then 1 else 0

private theorem batchBoundary_split (a m b u : ℕ) (ham : a ≤ m) (hmb : m ≤ b) :
    batchBoundary a m u + batchBoundary m b u ≤ batchBoundary a b u := by
  unfold batchBoundary
  split_ifs <;> omega

private theorem batchTiles_budget (lo hi a h : ℕ) :
    (batchTiles lo hi a h).length ≤
      1+h*(batchBoundary a (a+2^h) lo + batchBoundary a (a+2^h) hi) := by
  induction h generalizing a with
  | zero => simp only [batchTiles, Nat.zero_mul, Nat.add_zero]; split <;> simp
  | succ h ih =>
    let m := a+2^h
    let b := a+2^(h+1)
    have ham : a ≤ m := by exact Nat.le_add_right _ _
    have hmb : m ≤ b := by dsimp [m,b]; simp only [pow_succ]; omega
    have he : m+2^h = b := by dsimp [m,b]; simp only [pow_succ]; omega
    change (batchTiles lo hi a (h+1)).length ≤
      1+(h+1)*(batchBoundary a b lo + batchBoundary a b hi)
    simp only [batchTiles]
    split
    · simp
    · rename_i intersects
      split
      · simp
      · rename_i incomplete
        change ¬ (hi ≤ a ∨ b ≤ lo) at intersects
        change ¬ (lo ≤ a ∧ b ≤ hi) at incomplete
        have cut : 1 ≤ batchBoundary a b lo + batchBoundary a b hi := by
          unfold batchBoundary
          split_ifs <;> omega
        have sub : (batchBoundary a m lo + batchBoundary a m hi) +
            (batchBoundary m b lo + batchBoundary m b hi) ≤
            batchBoundary a b lo + batchBoundary a b hi := by
          have := batchBoundary_split a m b lo ham hmb
          have := batchBoundary_split a m b hi ham hmb
          omega
        have l := ih a
        have r := ih m
        change (batchTiles lo hi a h).length ≤
          1+h*(batchBoundary a m lo + batchBoundary a m hi) at l
        rw [he] at r
        change ((batchTiles lo hi a h) ++ (batchTiles lo hi m h)).length ≤ _
        rw [List.length_append, Nat.add_mul, Nat.one_mul]
        have total := Nat.mul_le_mul_left h sub
        rw [Nat.mul_add] at total
        omega

/-- Every ragged endpoint slice takes at most twice the tree height plus
one evaluations from the shared set of node polynomials. -/
theorem batchTiles_length_le (lo hi a h : ℕ) :
    (batchTiles lo hi a h).length ≤ 2*h+1 := by
  have hb (u : ℕ) : batchBoundary a (a+2^h) u ≤ 1 := by
    unfold batchBoundary
    split <;> decide
  have sum : batchBoundary a (a+2^h) lo + batchBoundary a (a+2^h) hi ≤ 2 :=
    Nat.add_le_add (hb lo) (hb hi)
  have hmul := Nat.mul_le_mul_left h sum
  have := batchTiles_budget lo hi a h
  omega

/-- Different unit strides use the same polynomial in the offsets, evaluated
at different block starts. The extra power is a unit. -/
theorem batchIntervals_affine_node {R : Type*} [CommRing R] (b : Rˣ)
    (a u z : R) (offsets : List R) :
    (offsets.map (fun r => a+(b : R)*(z+r-u))).prod =
      (b : R)^offsets.length * (offsets.map (fun r => ((↑b⁻¹ : R)*a-u+z)+r)).prod := by
  have scale (r : R) : a+(b : R)*(z+r-u) = (b : R)*(((↑b⁻¹ : R)*a-u+z)+r) := by
    simp only [mul_add, mul_sub, ← mul_assoc (b : R) (↑b⁻¹ : R) a, b.mul_inv, one_mul]
    ring
  induction offsets with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    rw [scale, ih]
    ring

/-- A translation on the index line makes all unit-stride progressions
use a single sorted template for the wheel residues. -/
theorem batchIntervals_wheel_translate {W a b u : ℕ} (unit : b.Coprime W)
    (phase : a ≡ b*u [MOD W]) (j : ℕ) :
    (a+b*j).Coprime W ↔ (u+j).Coprime W := by
  have same := (phase.add_right (b*j)).gcd_eq
  rw [← Nat.mul_add, Nat.Coprime.gcd_mul_left_cancel _ unit] at same
  exact (congrArg (· = 1) same).to_iff

/-- A single gcd distinguishes exact membership of the smaller prime
among positive candidates below both q and 2p, including repeated candidates. -/
theorem batchIntervals_gcd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (C : List ℕ) (range : ∀ x ∈ C, 0 < x ∧ x < q ∧ x < 2*p) :
    (p*q).gcd C.prod = if p ∈ C then p else 1 := by
  have nq : ¬ q ∣ C.prod := by
    intro h
    obtain ⟨x,hx,hd⟩ := hq.prime.dvd_prod_iff.mp h
    exact (Nat.not_le.mpr (range x hx).2.1) (Nat.le_of_dvd (range x hx).1 hd)
  have pd : p ∣ C.prod ↔ p ∈ C := by
    rw [hp.prime.dvd_prod_iff]
    constructor
    · rintro ⟨x,hx,hd⟩
      rwa [← Nat.eq_of_dvd_of_lt_two_mul (range x hx).1.ne' hd (range x hx).2.2]
    · exact fun h => ⟨p,h,dvd_refl p⟩
  rw [Nat.Coprime.gcd_mul_right_cancel _ (hq.coprime_iff_not_dvd.mpr nq)]
  split
  · exact Nat.gcd_eq_left (pd.mpr ‹_›)
  · exact hp.coprime_iff_not_dvd.mpr (fun h => ‹p ∉ C› (pd.mp h))

/-- The band inequalities used in the batched gcd hold throughout the
public balanced range, even when the searched list omits the true prime. -/
theorem batchIntervals_balanced_gcd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p < q) (balanced : q ≤ 2*p) (C : List ℕ)
    (band : ∀ x ∈ C, 0 < x ∧ x ≤ (p*q).sqrt) :
    (p*q).gcd C.prod = if p ∈ C then p else 1 := by
  apply batchIntervals_gcd hp hq
  intro x hx
  obtain ⟨pos,small⟩ := band x hx
  have below : (p*q).sqrt < q := Nat.sqrt_lt.mpr (Nat.mul_lt_mul_of_pos_right ordered hq.pos)
  exact ⟨pos,lt_of_le_of_lt small below,lt_of_lt_of_le (lt_of_le_of_lt small below) balanced⟩

/-- Lifting a monic shift from N to 2N in both ways makes a root
modulo the smaller prime into a root modulo a divisor at least sqrt(2N). -/
theorem batchIntervals_parity_lift {p q c j : ℕ} (balanced : q ≤ 2*p)
    (qodd : Odd q) (root : p ∣ j+c) :
    2*p ∣ 2*(p*q) ∧ 2*(p*q) ≤ (2*p)^2 ∧
      (2*p ∣ j+c ∨ 2*p ∣ j+(c+p*q)) := by
  refine ⟨⟨q, by ring⟩, ?_, ?_⟩
  · calc
      2*(p*q) = 2*p*q := by ring
      _ ≤ 2*p*(2*p) := Nat.mul_le_mul_left _ balanced
      _ = _ := by ring
  · obtain ⟨v,hv⟩ := root
    obtain ⟨r,hr⟩ := qodd
    have parity : 2 ∣ v ∨ 2 ∣ v+q := by omega
    rcases parity with ⟨u,hu⟩ | ⟨u,hu⟩
    · left
      exact ⟨u,by rw [hv,hu]; ring⟩
    · right
      refine ⟨u,?_⟩
      calc
        j+(c+p*q) = p*(v+q) := by rw [Nat.mul_add, ← hv]; omega
        _ = _ := by rw [hu]; ring

/-- A bounded mixed-stride computation. Each subproduct is one evaluation
of a node polynomial for offsets [1, 5, 7, 11] in the wheel of modulus six. -/
theorem batchIntervals_mixed_example :
    let node := fun (offsets : List ℕ) (z : ℕ) => (offsets.map (z+·)).prod
    let common := node [1,5] 12056 * node [7] 12056 *
      node [5] 8608 * node [7] 8608 * node [5] 3023
    (common*node [7,11] 3023)%15049 = 2828 ∧
      Nat.gcd 15049 2828 = 101 ∧
      (common*node [5] 3029)%15049 = 5504 ∧ Nat.gcd 15049 5504 = 1 ∧
      Nat.Prime 101 ∧ Nat.Prime 149 ∧ 101*149 = 15049 := by decide +kernel

/-- Exact schedule sizes for the full balanced band of the 62-bit example.
The two partial blocks use rank windows [3729,11840) and [0,10793). -/
theorem batchIntervals_schedule_example :
    let n := 3221225472647483647
    let l := 1269099184
    let u := 1794777277
    let rank := fun (x : ℕ) => 8*(x/30) +
      ([1,7,11,13,17,19,23,29] : List ℕ).countP (fun r => decide (r < x%30))
    let d := 11840
    let H := 44400
    (2*(l-1)^2 < n ∧ n ≤ 2*l^2) ∧ ((u-1)^2 ≤ n ∧ n < u^2) ∧
      rank u-rank l = 140180824 ∧ (8*(1480-1))^2 < 140180824 ∧
      140180824 ≤ d^2 ∧ u/H-(l/H+1) = 11838 ∧
      rank (l%H) = 3729 ∧ rank (u%H) = 10793 ∧
      (batchTiles 3729 d 0 14).length + (batchTiles 0 10793 0 14).length = 18 := by
  decide +kernel

end PrimeFactors
