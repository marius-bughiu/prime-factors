import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- The interval of products consistent with the leading digits of two inputs. -/
theorem product_prefix_interval (x y L : ℕ) (pos : 0 < L) :
    (x / L) * (y / L) * L ^ 2 ≤ x * y ∧
      x * y < (x / L + 1) * (y / L + 1) * L ^ 2 := by
  have next (z : ℕ) : z < (z / L + 1) * L := by
    have := Nat.mod_add_div z L
    have := Nat.mod_lt z pos
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (z / L)]
    omega
  constructor
  · calc
      _ = (x / L * L) * (y / L * L) := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.div_mul_le_self x L) (Nat.div_mul_le_self y L)
  · calc
      _ ≤ ((x / L + 1) * L) * y := Nat.mul_le_mul_right y (next x).le
      _ < ((x / L + 1) * L) * ((y / L + 1) * L) :=
        Nat.mul_lt_mul_of_pos_left (next y) (Nat.mul_pos (Nat.succ_pos _) pos)
      _ = _ := by ring

/-- A common width-M interval resolves the wrapping of the low product. -/
theorem product_prefix_guard {x y N L M : ℕ} (pos : 0 < L)
    (width : (x / L + y / L + 1) * L ^ 2 ≤ M) (congr : x * y ≡ N [MOD M]) :
    x * y = N ↔ (x / L) * (y / L) * L ^ 2 ≤ N ∧
      N < (x / L + 1) * (y / L + 1) * L ^ 2 := by
  have bounds := product_prefix_interval x y L pos
  constructor
  · rintro rfl
    exact bounds
  · intro target
    have expand : (x / L + 1) * (y / L + 1) * L ^ 2 =
        (x / L) * (y / L) * L ^ 2 + (x / L + y / L + 1) * L ^ 2 := by ring
    rw [expand] at bounds target
    obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le bounds.1
    obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le target.1
    rw [hu, hv] at congr
    have reduced := Nat.ModEq.add_left_cancel' _ congr
    have eq : u = v := reduced.eq_of_lt_of_lt (by omega) (by omega)
    omega

/-- For factors of at most h+d bits, their h-bit prefixes and the bottom
h+1+2d product bits suffice. This omits h-1 bits of a full-width product. -/
theorem product_prefix_guard_pow {x y N h d : ℕ}
    (hx : x < 2 ^ h * 2 ^ d) (hy : y < 2 ^ h * 2 ^ d)
    (congr : x * y ≡ N [MOD 2 ^ (h + 1) * (2 ^ d) ^ 2]) :
    x * y = N ↔ (x / 2 ^ d) * (y / 2 ^ d) * (2 ^ d) ^ 2 ≤ N ∧
      N < (x / 2 ^ d + 1) * (y / 2 ^ d + 1) * (2 ^ d) ^ 2 := by
  have pos : 0 < 2 ^ d := Nat.two_pow_pos _
  have ax := (Nat.div_lt_iff_lt_mul pos).mpr hx
  have ay := (Nat.div_lt_iff_lt_mul pos).mpr hy
  apply product_prefix_guard pos _ congr
  apply Nat.mul_le_mul_right
  rw [pow_succ]
  omega

example : 11 * 13 ≡ 79 [MOD 64] ∧ ¬ (11 / 2 * (13 / 2) * 2 ^ 2 ≤ 79) := by decide

end PrimeFactors
