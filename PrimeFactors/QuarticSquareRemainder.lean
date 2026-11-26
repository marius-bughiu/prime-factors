import PrimeFactors.BlockSubresultantProbe
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp

/-! Varying the width of the quartic probe with the square-root center.
The exact degree below is computed after passage to the field of a divisor. -/
namespace PrimeFactors.QuarticSquareRemainder

open Polynomial
open BlockSubresultantProbe (probe)

/-- The same coefficient evaluated using the public remainder instead of the center. -/
def residual (m r : ℤ) : ℤ :=
  48*r^2 + 24*(1+m^2)*r + (m^2-1)^3

theorem remainder_identity (m t r : ℤ) :
    probe m t - residual m r = (t^2+r)*(48*(t^2-r)-24*(1+m^2)) := by
  unfold probe residual
  ring

/-- Choosing the width equal to the center gives a quadratic in the remainder
after the elementary factor t²−1 has been separated. -/
theorem diagonal_width (t : ℤ) : probe t t = (t^2-1)*(t^4+22*t^2+1) := by
  unfold probe
  ring

theorem diagonal_remainder (t r : ℤ) :
    probe t t - (t^2-1)*(r^2-22*r+1) =
      (t^2+r)*((t^2-1)*(t^2-r+22)) := by
  rw [diagonal_width]
  ring

variable {K : Type*} [Field K]

/-- Numerator of the quartic at rational width A/B, multiplied by B⁶. -/
noncomputable def cleared (A B : K[X]) : K[X] :=
  C 48 * (X^4*B^6) - C 24 * (X^2*((A^2+B^2)*B^4)) + (A^2-B^2)^3

theorem eval_cleared (A B : K[X]) (t m : K) (width : m*B.eval t=A.eval t) :
    (cleared A B).eval t = (B.eval t)^6*(48*t^4-24*(1+m^2)*t^2+(m^2-1)^3) := by
  simp only [cleared, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow, ←width]
  ring

/-- A variable numerator cannot cancel the fourth power of X at infinity:
the two potential leading degrees have different remainders modulo six.
A may be zero and A,B need not be relatively prime. -/
theorem degree (A B : K[X]) (good : (48 : K)≠0) (den : B≠0) :
    (cleared A B).natDegree = max (6*A.natDegree) (6*B.natDegree+4) := by
  let f := C (48:K) * (X^4*B^6)
  let g := C (24:K) * (X^2*((A^2+B^2)*B^4))
  let h := (A^2-B^2)^3
  change (f - g + h).natDegree = _
  have df : f.natDegree = 6*B.natDegree+4 := by
    simp only [f,natDegree_C_mul good,natDegree_X_pow_mul 4 (pow_ne_zero 6 den),natDegree_pow]
  have dg : g.natDegree ≤ 2 + max (2*A.natDegree) (2*B.natDegree) + 4*B.natDegree := by
    have hadd := natDegree_add_le (A^2) (B^2)
    have hprod := natDegree_mul_le (p:=A^2+B^2) (q:=B^4)
    have hX := natDegree_mul_le (p:=(X:K[X])^2) (q:=(A^2+B^2)*B^4)
    have hC := natDegree_C_mul_le (24:K) (X^2*((A^2+B^2)*B^4))
    change (C (24:K)*(X^2*((A^2+B^2)*B^4))).natDegree ≤ _
    simp only [natDegree_X_pow,natDegree_pow,natDegree_X] at hadd hprod hX
    omega
  by_cases order : A.natDegree ≤ B.natDegree
  · have dh0 := natDegree_sub_le (A^2) (B^2)
    simp only [natDegree_pow] at dh0
    have dh : h.natDegree = 3*(A^2-B^2).natDegree := natDegree_pow _ _
    have fg : (f-g).natDegree = f.natDegree :=
      natDegree_sub_eq_left_of_natDegree_lt (by omega)
    rw [natDegree_add_eq_left_of_natDegree_lt (by omega : h.natDegree < (f-g).natDegree),
      fg,df,max_eq_right (by omega)]
  · have dh0 : (A^2-B^2).natDegree=(A^2).natDegree :=
      natDegree_sub_eq_left_of_natDegree_lt (by simp only [natDegree_pow]; omega)
    have dh : h.natDegree=6*A.natDegree := by
      simp only [h,natDegree_pow,dh0]
      omega
    have fg := natDegree_sub_le f g
    rw [natDegree_add_eq_right_of_natDegree_lt (by omega : (f-g).natDegree < h.natDegree),
      dh,max_eq_left (by omega)]

/-- Only zeros where the denominator is invertible give a rational-width
reading. Counting the cleared roots can also include poles. -/
theorem count (A B : K[X]) (good : (48:K)≠0) (den : B≠0) (S : Finset K)
    (hit : ∀ t ∈ S, ∃ m : K, B.eval t≠0 ∧ m*B.eval t=A.eval t ∧
      48*t^4-24*(1+m^2)*t^2+(m^2-1)^3=0) :
    S.card ≤ max (6*A.natDegree) (6*B.natDegree+4) := by
  have d := degree A B good den
  have nz : cleared A B ≠ 0 := by
    intro eq
    rw [eq,natDegree_zero] at d
    omega
  rw [← d]
  apply card_le_degree_of_subset_roots
  intro t ht
  obtain ⟨m,_,width,zero⟩ := hit t ht
  apply (mem_roots nz).2
  change (cleared A B).eval t = 0
  rw [eval_cleared A B t m width,zero,mul_zero]

/-- A reduction of integer coefficients can lower polynomial degrees. As long
as the denominator polynomial survives, the integer degrees still give upper bounds. -/
theorem count_reduced (A B : ℤ[X]) (f : ℤ →+* K) (good : (48:K)≠0)
    (den : B.map f≠0) (S : Finset K)
    (hit : ∀ t ∈ S, ∃ m : K, (B.map f).eval t≠0 ∧ m*(B.map f).eval t=(A.map f).eval t ∧
      48*t^4-24*(1+m^2)*t^2+(m^2-1)^3=0) :
    S.card ≤ max (6*A.natDegree) (6*B.natDegree+4) := by
  apply (count (A.map f) (B.map f) good den S hit).trans
  exact max_le_max (Nat.mul_le_mul_left _ natDegree_map_le)
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ natDegree_map_le) _)

/-- The reciprocal quartic has a root precisely when the two indicated
square roots can be taken in the same field. Each root determines both signed
coordinates, so, when neither coordinate vanishes, the four sign choices are distinct. -/
theorem diagonal_coordinates {t : K} (two : (2:K)≠0) :
    t^4+22*t^2+1=0 ↔ ∃ a b : K, a^2= -5 ∧ b^2= -6 ∧ t=a+b := by
  constructor
  · intro hit
    have nonzero : t≠0 := fun eq => by simp [eq] at hit
    refine ⟨(t^2+1)/(2*t), (t^2-1)/(2*t), ?_, ?_, ?_⟩
    · field_simp [two,nonzero]
      linear_combination hit
    · field_simp [two,nonzero]
      linear_combination hit
    · field_simp [two,nonzero]
      ring
  · rintro ⟨a,b,ha,hb,rfl⟩
    calc
      _ = (a^2+b^2+11)^2 + 4*a*b*(a^2+b^2+11) + 4*a^2*b^2-120 := by ring
      _ = 0 := by rw [ha,hb]; ring

theorem diagonal_roots {t a b : K} (two : (2:K)≠0) (ha : a^2= -5) (hb : b^2= -6) :
    t^4+22*t^2+1=0 ↔ t=a+b ∨ t=a-b ∨ t= -a+b ∨ t= -a-b := by
  rw [diagonal_coordinates two]
  constructor
  · rintro ⟨x,y,hx,hy,rfl⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hx.trans ha.symm) with rfl|rfl <;>
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hb.symm) with rfl|rfl <;>
      simp [sub_eq_add_neg]
  · rintro (rfl|rfl|rfl|rfl)
    · exact ⟨a,b,ha,hb,rfl⟩
    · exact ⟨a,-b,ha,by simpa using hb,sub_eq_add_neg _ _⟩
    · exact ⟨-a,b,by simpa using ha,hb,rfl⟩
    · exact ⟨-a,-b,by simpa using ha,by simpa using hb,sub_eq_add_neg _ _⟩

/-- Distinct signed coordinate pairs give distinct roots. Their sum fixes
their difference, because their product in the difference-of-squares identity is one. -/
theorem coordinates_unique {a b x y : K} (two : (2:K)≠0)
    (ha : a^2= -5) (hb : b^2= -6) (hx : x^2= -5) (hy : y^2= -6)
    (same : a+b=x+y) : a=x ∧ b=y := by
  have inv (c d : K) (hc : c^2= -5) (hd : d^2= -6) : (c+d)*(c-d)=1 := by
    linear_combination hc-hd
  have first := inv a b ha hb
  have second := inv x y hx hy
  rw [←same] at second
  have unit : a+b≠0 := fun eq => by simp [eq] at first
  have diff := mul_left_cancel₀ unit (first.trans second.symm)
  have dx : 2*(a-x)=0 := by linear_combination same + diff
  have ax := sub_eq_zero.mp ((mul_eq_zero.mp dx).resolve_left two)
  exact ⟨ax,add_left_cancel (ax ▸ same)⟩

/-- The degree-six bound at width X is attained at the prime recovered below. -/
theorem six_classes (t : ZMod 509) :
    48*t^4-24*(1+t^2)*t^2+(t^2-1)^3=0 ↔
      t=1 ∨ t=508 ∨ t=192 ∨ t=114 ∨ t=395 ∨ t=317 := by
  letI : Fact (Nat.Prime 509) := ⟨by decide +kernel⟩
  have roots := diagonal_roots (t:=t) (a:=(153:ZMod 509)) (b:=39)
    (by decide) (by decide +kernel) (by decide +kernel)
  have id : 48*t^4-24*(1+t^2)*t^2+(t^2-1)^3 =
      (t-1)*(t+1)*(t^4+22*t^2+1) := by ring
  rw [id,mul_eq_zero,mul_eq_zero,sub_eq_zero,add_eq_zero_iff_eq_neg,roots]
  rw [show (-(1:ZMod 509))=508 by decide +kernel,
    show (153+39:ZMod 509)=192 by decide +kernel,show (153-39:ZMod 509)=114 by decide +kernel,
    show (-153+39:ZMod 509)=395 by decide +kernel,show (-153-39:ZMod 509)=317 by decide +kernel,or_assoc]

/-- A product-only split with odd width equal to the center; the three fixed
widths and the adjacent t²−1 factor all have unit gcd. -/
theorem worked_example :
    let n : ℕ := 156263
    let t : ℤ := n.sqrt
    let r := (n:ℤ)-t^2
    t=395 ∧ r=238 ∧ Int.gcd (576*t*(t^2-1)) n=1 ∧
    Int.gcd (probe 3 t) n=1 ∧ Int.gcd (probe 5 t) n=1 ∧ Int.gcd (probe 7 t) n=1 ∧
    Int.gcd (r^2-22*r+1) n=509 ∧ Int.gcd (probe t t) n=509 ∧
    Nat.Prime 307 ∧ Nat.Prime 509 ∧ 307*509=n := by
  have root : (156263:ℕ).sqrt=395 := Nat.eq_of_le_of_lt_succ
    (Nat.le_sqrt'.mpr (by decide)) (Nat.sqrt_lt'.mpr (by decide))
  simp only [root]
  decide +kernel

end PrimeFactors.QuarticSquareRemainder
