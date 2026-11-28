import PrimeFactors.ConvexIntegerReadout
import PrimeFactors.OffsetTransposeBlockWindow
import PrimeFactors.OffsetTransposeQuartic

/-! Public comparison budget for locating the possible blocks at one known
nonnegative shift. Inputs are the product, radix, offset and a block-product
candidate. All comparisons are rational and all searches use integer indices. -/
namespace PrimeFactors.OffsetTransposeReadout

open OffsetTransposeQuartic ConvexIntegerReadout

/-- For positive leading digit a, b(a+t)=C gives b≤C/(t+1). -/
def lastIndex (B t C : ℕ) := min (B-1) (C/(t+1))

def score (B t C j : ℕ) : ℚ :=
  level (mkRat B 1) (mkRat t 1) (mkRat C 1) (mkRat j 1)

theorem score_eq (B t C j : ℕ) : score B t C j=level B t C j := by
  simp only [score,Rat.mkRat_one,Int.cast_natCast]

theorem strict_steps (B t C j : ℕ) (positive : 1≤j) (inside : j+1<lastIndex B t C) :
    score B t C (j+1)-score B t C j < score B t C (j+2)-score B t C (j+1) := by
  have hj : j≤C/(t+1) := (by omega : j≤lastIndex B t C).trans (min_le_right ..)
  have cap : j*(t+1)≤C := (Nat.le_div_iff_mul_le (by omega)).mp hj
  have tx : t*j≤C := by rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm j t] at cap; omega
  have step := step_increases (B:ℚ) (t:=(t:ℚ)) (C:=(C:ℚ)) (x:=(j:ℚ))
    (by positivity) (by exact_mod_cast (by omega : 0<j)) (by exact_mod_cast tx)
  simpa only [score_eq,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using step

/-- Two crossing indices with measured comparisons; a sentinel or a nonroot
can always be discarded by the exact tests in OffsetTransposeQuartic.Checked. -/
def reading (B N t C fuel : ℕ) : Reading :=
  read (score B t C) (mkRat (height B N C) 1) fuel 1 (lastIndex B t C)

theorem contains_digit {B a b t N C fuel : ℕ} (pos : 0<a) (order : a≤b) (top : b<B)
    (prod : (B*a+b)*(B*b+a+t)=N) (block : C=b*(a+t)) (budget : B≤2^fuel) :
    (reading B N t C fuel).comparisons ≤ 3*fuel ∧
    (b=(reading B N t C fuel).left ∨ b=(reading B N t C fuel).right) := by
  have bp : 0<b := by omega
  have base : 0<B := by omega
  have bdiv : b≤C/(t+1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by
    rw [block]
    exact Nat.mul_le_mul_left _ (by omega))
  have within : b≤lastIndex B t C := le_min (by omega) bdiv
  have cap := (min_le_left (B-1) (C/(t+1)))
  have room : lastIndex B t C-1+1 < 2^fuel := by unfold lastIndex at *; omega
  have checked : Checked (B:ℤ) N t C b := (check_iff (by exact_mod_cast base)).mpr (by
    refine ⟨a,(a+t:ℕ),by exact_mod_cast bp,by exact_mod_cast top,by positivity,
      by exact_mod_cast order,by positivity,by push_cast; rfl,?_,?_⟩
    · exact_mod_cast block.symm
    · exact_mod_cast (show (B*a+b)*(B*b+(a+t))=N by simpa only [Nat.add_assoc] using prod))
  have value := (root_level (by exact_mod_cast bp)).mp checked.2.2.2.2.2.2.2
  have exact_value : score B t C b=(height B N C:ℚ) := by
    simpa only [score_eq, Int.cast_natCast] using value
  have facts := read_spec (score B t C) (height B N C) fuel 1 (lastIndex B t C)
    (by omega) room (fun j => strict_steps B t C j)
  simpa only [reading,Rat.mkRat_one] using And.intro facts.1 (facts.2 b bp within exact_value)

/-- The search budget for a positive shift is at most t rows with at most
3*fuel rational comparisons on each nonempty row. -/
theorem locate {B a b t N fuel : ℕ} (pos : 0<a) (order : a≤b) (top : b<B)
    (shift : 0<t) (product : (B*a+b)*(B*b+a+t)=N) (budget : B≤2^fuel) :
    ∃ j<t, let r := reading B N t (OffsetTransposeBlockWindow.candidate B N t j) fuel
      r.comparisons≤3*fuel ∧ (b=r.left ∨ b=r.right) := by
  obtain ⟨j,hj,eq⟩ := OffsetTransposeBlockWindow.contains_positive order top (by omega) shift product
  exact ⟨j,hj,contains_digit pos order top product eq budget⟩

/-- All candidate rows together stay within this comparison budget,
including rows on which neither returned index gives a valid digit. -/
theorem total_cost (B N t fuel : ℕ) :
    (∑ j ∈ Finset.range t, (reading B N t (OffsetTransposeBlockWindow.candidate B N t j) fuel).comparisons)
      ≤ t*(3*fuel) := by
  simp only [reading,Rat.mkRat_one]
  apply (Finset.sum_le_sum (fun j (_ : j∈Finset.range t) =>
    read_cost (score B t (OffsetTransposeBlockWindow.candidate B N t j))
      (height B N (OffsetTransposeBlockWindow.candidate B N t j)) fuel 1
      (lastIndex B t (OffsetTransposeBlockWindow.candidate B N t j)))).trans
  simp

/-- On this deliberately chosen 24-bit product the sole block-product
candidate gives two crossing indices. Only the first reconstructs the primes. -/
theorem example_24 :
    OffsetTransposeBlockWindow.candidate 64 10850303 1 0=2623 ∧
    height 64 10850303 2623=1623 ∧
    (let r := reading 64 10850303 1 2623 6; (r.left,r.right,r.comparisons)=(61,62,14)) ∧
    words 64 1 2623 61=(2749,3947) ∧ 2749*3947=10850303 ∧
    Nat.Prime 2749 ∧ Nat.Prime 3947 := by
  refine ⟨by decide,by decide,?_,by decide,by decide,by norm_num,by norm_num⟩
  decide +kernel

end PrimeFactors.OffsetTransposeReadout
