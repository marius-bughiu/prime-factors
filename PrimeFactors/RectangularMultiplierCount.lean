import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Count the distinct multipliers supplied by two comparable factors. The
odd and even constructions parameterize the two parity cases of a primitive
difference of squares. -/
namespace PrimeFactors.RectangularMultiplierCount
open Finset

private noncomputable def table (h : ℕ) (width : ℕ → ℕ) (entry : ℕ → ℕ → ℕ) : Finset ℕ :=
  (range h).biUnion fun j => (range (width j)).image (entry j)

private theorem size (h : ℕ) (width : ℕ → ℕ) (entry : ℕ → ℕ → ℕ) :
    (table h width entry).card ≤ ∑ j ∈ range h, width j := by
  apply Finset.card_biUnion_le.trans
  exact sum_le_sum fun j _ => (card_image_le.trans (by rw [card_range]))

def oddWidth (scale excess j : ℕ) := excess*(2*j+1)/(2*scale)+1
def evenWidth (scale excess j : ℕ) := excess*(j+1)/(2*scale)+1

noncomputable def allowed (K scale excess : ℕ) : Finset ℕ :=
  table ((K.sqrt+1)/2) (oddWidth scale excess) (fun j w => (2*j+1)*(2*j+1+2*w)) ∪
  table ((K/4).sqrt) (evenWidth scale excess) (fun j w => 4*(j+1)*(j+2+2*w))

private theorem odd_sum (scale excess L : ℕ) :
    2*scale*(∑ j ∈ range L, oddWidth scale excess j) ≤ 2*scale*L+excess*L^2 := by
  induction L with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ,oddWidth]
    have h := Nat.div_mul_le_self (excess*(2*j+1)) (2*scale)
    nlinarith only [ih,h]

private theorem even_sum (scale excess L : ℕ) :
    4*scale*(∑ j ∈ range L, evenWidth scale excess j) ≤ 4*scale*L+excess*L*(L+1) := by
  induction L with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ,evenWidth]
    have h := Nat.div_mul_le_self (excess*(j+1)) (2*scale)
    nlinarith only [ih,h]

/-- Count generated weight pairs before taking distinct products. Traversing
the two tables in pair order can visit the same multiplier more than once. -/
theorem pair_bound (scale excess L T : ℕ) :
    4*scale*((∑ j ∈ range L, oddWidth scale excess j)+(∑ j ∈ range T, evenWidth scale excess j)) ≤
      4*scale*(L+T)+2*excess*L^2+excess*T*(T+1) := by
  nlinarith only [odd_sum scale excess L,even_sum scale excess T]

/-- A finite, directly evaluable count. Including repeated products in the
estimate only increases its right hand side. -/
theorem bound (K scale excess : ℕ) :
    let L := (K.sqrt+1)/2
    let T := (K/4).sqrt
    4*scale*(allowed K scale excess).card ≤
      4*scale*(L+T)+2*excess*L^2+excess*T*(T+1) := by
  dsimp only
  let L := (K.sqrt+1)/2
  let T := (K/4).sqrt
  have upper := Finset.card_union_le (table L (oddWidth scale excess) (fun j w => (2*j+1)*(2*j+1+2*w)))
    (table T (evenWidth scale excess) (fun j w => 4*(j+1)*(j+2+2*w)))
  have both := upper.trans (Nat.add_le_add (size ..) (size ..))
  have weighted := Nat.mul_le_mul_left (4*scale) both
  apply weighted.trans
  exact pair_bound scale excess L T

/-- Apply the finite count without evaluating the materialized table. -/
theorem at_most (K scale excess upper : ℕ) (test :
    let L := (K.sqrt+1)/2
    let T := (K/4).sqrt
    4*scale*(L+T)+2*excess*L^2+excess*T*(T+1)<4*scale*(upper+1)) :
    (allowed K scale excess).card≤upper :=
  Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left ((bound K scale excess).trans_lt test))

/-- Both weights odd, with k=ab. The smaller weight is represented by 2j+1. -/
theorem odd_mem {a b K scale excess : ℕ} (sc : 0<scale) (ab : a≤b)
    (ao : a%2=1) (bo' : b%2=1) (cap : a*b≤K) (ratio : scale*b≤(scale+excess)*a) :
    a*b ∈ allowed K scale excess := by
  let j := a/2
  let w := (b-a)/2
  have ea : a=2*j+1 := by dsimp [j]; omega
  have eb : b=2*j+1+2*w := by dsimp [j,w]; omega
  have sa : a≤K.sqrt := Nat.le_sqrt.mpr ((Nat.mul_le_mul_left a ab).trans cap)
  have ji : j<(K.sqrt+1)/2 := by omega
  have small : (2*scale)*w ≤ excess*(2*j+1) := by
    rw [ea,eb] at ratio
    nlinarith only [ratio]
  have wi : w<oddWidth scale excess j := by
    dsimp [oddWidth]
    have h := (Nat.le_div_iff_mul_le (by omega : 0<2*scale)).mpr (by simpa [mul_comm] using small)
    omega
  apply mem_union_left
  exact mem_biUnion.mpr ⟨j,mem_range.mpr ji,mem_image.mpr ⟨w,mem_range.mpr wi,by rw [ea,eb]⟩⟩

/-- Opposite parities, with k=4ab. The larger weight exceeds the smaller
one by an odd integer. -/
theorem even_mem {a b K scale excess : ℕ} (sc : 0<scale) (ap : 0<a) (ab : a≤b)
    (opp : a%2≠b%2) (cap : 4*a*b≤K) (ratio : scale*b≤(scale+excess)*a) :
    4*a*b ∈ allowed K scale excess := by
  let j := a-1
  let w := (b-a)/2
  have ea : a=j+1 := by dsimp [j]; omega
  have eb : b=j+2+2*w := by dsimp [j,w]; omega
  have sq : a^2≤K/4 := (Nat.le_div_iff_mul_le (by decide)).mpr (by
    have h := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left a ab)
    nlinarith only [h,cap])
  have sa : a≤(K/4).sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using sq)
  have ji : j<(K/4).sqrt := by omega
  have small : (2*scale)*w ≤ excess*(j+1) := by
    rw [ea,eb] at ratio
    nlinarith only [ratio]
  have wi : w<evenWidth scale excess j := by
    dsimp [evenWidth]
    have h := (Nat.le_div_iff_mul_le (by omega : 0<2*scale)).mpr (by simpa [mul_comm] using small)
    omega
  apply mem_union_right
  exact mem_biUnion.mpr ⟨j,mem_range.mpr ji,mem_image.mpr ⟨w,mem_range.mpr wi,by rw [ea,eb]⟩⟩

end PrimeFactors.RectangularMultiplierCount
