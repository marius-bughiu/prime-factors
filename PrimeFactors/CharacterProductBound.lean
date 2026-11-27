import PrimeFactors.TwoCharacterWindow

/-! Uniform Pólya–Vinogradov bounds for the single and pair characters in a
coprime family of 3 mod 4 moduli, with a common bit cap on each modulus. -/
namespace PrimeFactors.CharacterProductBound
open TwoCharacterWindow

theorem at_predecessor {a : ℕ} (three : a%4=3) : char a (a-1) = -1 := by
  have eq : (((a-1:ℕ):ℤ)) ≡ -1 [ZMOD a] := by
    rw [Int.modEq_iff_dvd, Nat.cast_sub (by omega : 1≤a)]
    exact ⟨-1,by push_cast; ring⟩
  rw [char,jacobiSym.mod_left' eq,jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)),
    ZMod.χ₄_nat_three_mod_four three]

/-- CRT supplies -1 in one coordinate and 1 in the other. Each factor may be
composite and need not be squarefree. -/
theorem nonprincipal_pair {a b : ℕ} (ha : a%4=3) (hb : b%4=3) (co : a.Coprime b) :
    ∃ x, char (a*b) x = -1 := by
  let x := Nat.chineseRemainder co (a-1) 1
  refine ⟨x.val,?_⟩
  have left := jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr x.property.1)
  have right := jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr x.property.2)
  rw [char,jacobiSym.mul_right' _ (by omega) (by omega),left,right]
  simpa [char] using at_predecessor ha

/-- One common integer multiplier bounds each single-character interval sum. -/
theorem single (pv : PublishedPV) {a ra H C step : ℕ}
    (large : 100≤a) (three : a%4=3) (stride : step.Coprime a)
    (rad : a≤ra^2) (bits : a≤2^H) (constant : 5220+347*H≤2220*C)
    (first len : ℕ) : total a first step len ≤ (C*ra:ℕ) := by
  apply progression_bound pv large (Nat.odd_iff.mpr (by omega)) ⟨a-1,at_predecessor three⟩
    stride rad bits
  calc
    _ ≤ ra*(2220*C) := Nat.mul_le_mul_left _ constant
    _ = _ := by ring

/-- The error of a product character costs at most C times the product of the
two supplied square-root upper bounds. Rounding C once suffices for all pairs. -/
theorem pair (pv : PublishedPV) {a b ra rb H C step : ℕ}
    (largeA : 100≤a) (largeB : 100≤b) (ha : a%4=3) (hb : b%4=3) (co : a.Coprime b)
    (strideA : step.Coprime a) (strideB : step.Coprime b) (radA : a≤ra^2) (radB : b≤rb^2)
    (bitsA : a≤2^H) (bitsB : b≤2^H) (constant : 5220+694*H≤2220*C)
    (first len : ℕ) : total (a*b) first step len ≤ (C*ra*rb:ℕ) := by
  have large : 100≤a*b := largeA.trans (Nat.le_mul_of_pos_right _ (by omega))
  have rad : a*b≤(ra*rb)^2 := by rw [mul_pow]; exact Nat.mul_le_mul radA radB
  have bits : a*b≤2^(H+H) := by rw [pow_add]; exact Nat.mul_le_mul bitsA bitsB
  have odd := (Nat.odd_iff.mpr (by omega : a%2=1)).mul (Nat.odd_iff.mpr (by omega : b%2=1))
  apply progression_bound pv large odd (nonprincipal_pair ha hb co) (strideA.mul_right strideB) rad bits
  calc
    _ ≤ (ra*rb)*(2220*C) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

end PrimeFactors.CharacterProductBound
