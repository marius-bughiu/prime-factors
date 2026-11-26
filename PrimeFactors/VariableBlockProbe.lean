import PrimeFactors.BlockSubresultantProbe
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic

/-! Width selection for the second block subresultant. The discriminant is
public. Its Jacobi sign can certify that a pivot cannot vanish at both prime
factors, but the sign by itself does not produce a shift at which it vanishes. -/
namespace PrimeFactors.VariableBlockProbe

open BlockSubresultantProbe Polynomial

def discriminant {R : Type*} [CommRing R] (m : R) : R :=
  3 * (3*(1+m^2)^2 - (m^2-1)^3)

theorem completion (m t : ℤ) :
    3*probe m t + discriminant m = (3*(4*t^2-1-m^2))^2 := by
  unfold probe discriminant
  ring

/-- No admissible real width makes the discriminant a rational square. -/
theorem discriminant_neg {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {m : R} (hm : 3 ≤ m) : discriminant m < 0 := by
  have pos : 0 ≤ m^2-9 := by nlinarith [mul_nonneg (sub_nonneg.mpr hm) (show 0 ≤ m+3 by linarith)]
  have expanded : discriminant m =
      -3*((m^2-9)^3+21*(m^2-9)^2+132*(m^2-9)+212) := by unfold discriminant; ring
  rw [expanded]
  nlinarith only [pow_nonneg pos 3, sq_nonneg (m^2-9), pos]

theorem probe_pos {m : ℤ} (hm : 3 ≤ m) (t : ℤ) : 0 < probe m t := by
  have low := sq_nonneg (3*(4*t^2-1-m^2))
  rw [← completion m t] at low
  linarith only [low, discriminant_neg hm]

/-- The public square-root remainder h gives the same modular pivot. -/
def widthCubic (h z : ℤ) : ℤ := z^3 + 24*h*z + 48*h*(h+1)

theorem center_cubic {n t h : ℤ} (shape : n = t^2+h) (m : ℤ) :
    probe m t ≡ widthCubic h (m^2-1) [ZMOD n] := by
  apply Int.modEq_iff_dvd.mpr
  exact ⟨-24*(2*t^2-2*h-(1+m^2)), by rw [shape]; unfold probe widthCubic; ring⟩

/-- The radicand in Cardano's formula for z³+24hz+48h(h+1) at a nonsquare
input has a nonsquare factor, even after the square factor (8h)² is removed. -/
theorem cardano_identity (h : ℤ) :
    (24*h*(h+1))^2+(8*h)^3 = (8*h)^2*(9*h^2+26*h+9) := by ring

theorem cardano_nonsquare {h : ℕ} (hp : 0 < h) (u : ℕ) :
    u^2 ≠ 9*h^2+26*h+9 := by
  let k := if h ≤ 3 then 3*h+3 else 3*h+4
  have gap : k^2 < 9*h^2+26*h+9 ∧ 9*h^2+26*h+9 < (k+1)^2 := by
    dsimp [k]
    split_ifs with small <;> constructor <;> nlinarith
  by_cases below : u ≤ k
  · exact (lt_of_le_of_lt (Nat.pow_le_pow_left below 2) gap.1).ne
  · exact (lt_of_lt_of_le gap.2 (Nat.pow_le_pow_left (by omega : k+1 ≤ u) 2)).ne'

/-- For any N, a negative public Jacobi sign excludes a whole-modulus pivot.
This implication needs neither a prime oracle nor random shifts. -/
theorem negative_symbol {n : ℕ} {m : ℤ} (neg : jacobiSym (discriminant m) n = -1)
    (t : ℤ) : ¬ (n : ℤ) ∣ probe m t := by
  intro whole
  let v := 3*(4*t^2-1-m^2)
  have same : discriminant m ≡ v^2 [ZMOD (n : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    have id : v^2-discriminant m = 3*probe m t := by
      dsimp [v]
      linear_combination -(completion m t)
    rw [id]
    exact dvd_mul_of_dvd_right whole 3
  have eq := jacobiSym.mod_left' same
  rw [neg, jacobiSym.pow_left] at eq
  have nonnegative := sq_nonneg (jacobiSym v n)
  rw [← eq] at nonnegative
  contradiction

/-- With a square root s of the discriminant in a field, the admissible
values of t² are the two elements displayed on the right. -/
theorem root_branches {F : Type*} [Field F] {m s : F} (ht : (12:F) ≠ 0)
    (hs : s^2 = discriminant m) (x : F) :
    48*x^4-24*(1+m^2)*x^2+(m^2-1)^3 = 0 ↔
    x^2 = (3*(1+m^2)+s)/12 ∨ x^2 = (3*(1+m^2)-s)/12 := by
  have ht3 : (3:F) ≠ 0 := by
    intro z
    apply ht
    linear_combination 4*z
  have factor : (12*x^2-3*(1+m^2)-s)*(12*x^2-3*(1+m^2)+s) =
      3*(48*x^4-24*(1+m^2)*x^2+(m^2-1)^3) := by
    unfold discriminant at hs
    linear_combination -hs
  rw [eq_div_iff ht, eq_div_iff ht]
  constructor
  · intro root
    rw [root, mul_zero, mul_eq_zero] at factor
    rcases factor with zero | zero
    · left; linear_combination zero
    · right; linear_combination zero
  · intro branch
    apply (mul_eq_zero.mp (show 3*(48*x^4-24*(1+m^2)*x^2+(m^2-1)^3)=0 from ?_)).resolve_left ht3
    rw [←factor, mul_eq_zero]
    rcases branch with eq | eq
    · left; linear_combination eq
    · right; linear_combination eq

private theorem unique_branch {F : Type*} [Field F] [Fintype F] [DecidableEq F] {a b : F}
    (mixed : quadraticChar F (a*b) = -1) :
    ∃ t : F, t ≠ 0 ∧ ∀ x : F, (x^2 = a ∨ x^2 = b) ↔ (x=t ∨ x= -t) := by
  rw [map_mul] at mixed
  have an : a ≠ 0 := by rintro rfl; simp at mixed
  have bn : b ≠ 0 := by rintro rfl; simp at mixed
  have fromSquare {u v : F} (un : u ≠ 0) (yes : IsSquare u) (no : ¬ IsSquare v) :
      ∃ t : F, t ≠ 0 ∧ ∀ x : F, (x^2 = u ∨ x^2 = v) ↔ (x=t ∨ x= -t) := by
    obtain ⟨t,eq⟩ := yes
    rw [←sq] at eq
    refine ⟨t,fun h => un (by simp [eq,h]), fun x => ?_⟩
    have miss : x^2 ≠ v := fun e => no (e ▸ IsSquare.sq x)
    simp only [miss, or_false, eq, sq_eq_sq_iff_eq_or_eq_neg]
  rcases quadraticChar_dichotomy an with first | first
  · rw [first, one_mul] at mixed
    exact fromSquare an ((quadraticChar_one_iff_isSquare an).mp first)
      (quadraticChar_neg_one_iff_not_isSquare.mp mixed)
  · rw [first, neg_one_mul] at mixed
    have second : quadraticChar F b = 1 := by omega
    obtain ⟨t,tn,ht⟩ := fromSquare bn ((quadraticChar_one_iff_isSquare bn).mp second)
      (quadraticChar_neg_one_iff_not_isSquare.mp first)
    exact ⟨t,tn,fun x => (or_comm (a:=x^2=a) (b:=x^2=b)).trans (ht x)⟩

/-- A positive local criterion. The two factors of the quadratic in x² have
opposite characters, so precisely the two opposite square roots of one
branch are admissible shifts. -/
theorem two_shifts {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m s : F} (ht : (12:F) ≠ 0)
    (hs : s^2 = discriminant m) (mixed : quadraticChar F (3*(m^2-1)) = -1) :
    ∃ t : F, t ≠ 0 ∧ ∀ x : F,
      (48*x^4-24*(1+m^2)*x^2+(m^2-1)^3=0 ↔ x=t ∨ x= -t) := by
  have mn : m^2-1 ≠ 0 := by intro z; simp [z] at mixed
  have prod : ((3*(1+m^2)+s)/12)*((3*(1+m^2)-s)/12) =
      3*(m^2-1)*((m^2-1)/12)^2 := by
    rw [div_mul_div_comm, div_pow, ←mul_div_assoc, pow_two (12:F)]
    congr 1
    unfold discriminant at hs
    linear_combination -hs
  have chars := congrArg (quadraticChar F) prod
  rw [map_mul (quadraticChar F) (3*(m^2-1)), mixed,
    quadraticChar_sq_one' (div_ne_zero mn ht), mul_one] at chars
  obtain ⟨t,tn,roots⟩ := unique_branch chars
  exact ⟨t,tn,fun x => (root_branches ht hs x).trans (roots x)⟩

/-- At a fixed center the width is a root of a monic sextic, so even in
small characteristic it can attain at most six distinct residues. -/
theorem width_count {R : Type*} [Field R] (h : R) (S : Finset R)
    (hit : ∀ m ∈ S, (m^2-1)^3+24*h*(m^2-1)+48*h*(h+1) = 0) : S.card ≤ 6 := by
  let z : R[X] := X^2-1
  let f : R[X] := z^3+C (24*h)*z+C (48*h*(h+1))
  have degree : f.natDegree = 6 := by
    dsimp [f,z]
    compute_degree!
  have nz : f ≠ 0 := fun hz => by rw [hz,natDegree_zero] at degree; contradiction
  rw [← degree]
  apply card_le_degree_of_subset_roots
  intro m hm
  apply (mem_roots nz).mpr
  simpa [IsRoot,f,z] using hit m hm

/-- At p=13, h=3 (equivalently t=6), the width bound is attained. -/
theorem six_at_thirteen : ∀ i : Fin 13, (13 ∣ widthCubic 3 ((i.val : ℤ)^2-1) ↔
    i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=9 ∨ i.val=10 ∨ i.val=11) := by decide +kernel

/-- The first negative public sign in the odd width menu 3,5,7 yields both
primes from N. All 49 integers in the corresponding rectangle are units. -/
theorem selected_example :
    jacobiSym (discriminant (3:ℤ)) 42781 = 1 ∧
    jacobiSym (discriminant (5:ℤ)) 42781 = 1 ∧
    jacobiSym (discriminant (7:ℤ)) 42781 = -1 ∧
    (42781:ℕ).sqrt = 206 ∧
    Int.gcd (probe 7 206) 42781 = 179 ∧
    (42781:ℕ) = 179*239 ∧ Nat.Prime 179 ∧ Nat.Prime 239 ∧
    (List.range 49).all (fun i => (182+i).gcd 42781 == 1) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · norm_num [discriminant]
  · norm_num [discriminant]
  · norm_num [discriminant]
  · exact le_antisymm (Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr (by decide)))
      (Nat.le_sqrt'.mpr (by decide))
  all_goals decide +kernel

end PrimeFactors.VariableBlockProbe
