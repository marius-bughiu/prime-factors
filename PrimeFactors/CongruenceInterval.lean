import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith

namespace PrimeFactors.CongruenceInterval

/-- The least element of the residue class at or above a real lower endpoint
lies strictly below that endpoint plus one modulus. -/
theorem first {L : ℝ} {M : ℕ} (r : ℤ) (pos : 0<M) :
    let x : ℤ := r + M*⌈(L-r)/M⌉
    x ≡ r [ZMOD M] ∧ L ≤ (x:ℝ) ∧ (x:ℝ) < L+M := by
  have mp : (0:ℝ)<M := by exact_mod_cast pos
  let q := (L-r)/M
  have eq : q*M=L-r := div_mul_cancel₀ _ mp.ne'
  have lo := mul_le_mul_of_nonneg_right (Int.le_ceil q) mp.le
  have hi := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one q) mp
  dsimp
  constructor
  · exact Int.modEq_iff_dvd.mpr ⟨-⌈q⌉,by dsimp [q]; ring⟩
  · push_cast
    change L ≤ r + (M:ℝ)*⌈q⌉ ∧ r + (M:ℝ)*⌈q⌉ < L+M
    constructor <;> linarith only [lo,hi,eq]

/-- A closed interval containing at most one integer with this specific
residue has width strictly smaller than two moduli, regardless of the offset. -/
theorem width_of_unique {L U : ℝ} {M : ℕ} (r : ℤ) (pos : 0<M)
    (unique : ∀ x y : ℤ, x ≡ r [ZMOD M] → y ≡ r [ZMOD M] →
      (x:ℝ) ∈ Set.Icc L U → (y:ℝ) ∈ Set.Icc L U → x=y) :
    U-L < 2*(M:ℝ) := by
  by_contra! wide
  let x : ℤ := r+M*⌈(L-r)/M⌉
  obtain ⟨hx,low,upper⟩ := first (L := L) r pos
  change L≤(x:ℝ) at low
  change (x:ℝ)<L+M at upper
  have mp : (0:ℝ)<M := by exact_mod_cast pos
  have hy : x+M ≡ r [ZMOD M] := by
    apply Int.ModEq.trans _ hx
    exact Int.modEq_iff_dvd.mpr ⟨-1,by ring⟩
  have eq := unique x (x+M) hx hy
    ⟨low,by linarith⟩ ⟨by push_cast; linarith,by push_cast; linarith⟩
  have impossible : (M:ℤ)=0 := by omega
  exact (by exact_mod_cast (Nat.ne_of_gt pos) : (M:ℤ)≠0) impossible

end PrimeFactors.CongruenceInterval
