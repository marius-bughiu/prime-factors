import PrimeFactors.ShiftParameter
import PrimeFactors.PartialOrder
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

namespace PrimeFactors

/-- Five prescribed rational shifts fail on the same balanced prime pair.
Each listed pair gives the numerator and denominator of a shift at N.
Clearing denominators turns rational squareness into integer squareness. -/
theorem five_shifts_miss :
    let p : ℤ := 32433156901
    let q : ℤ := 34543964027
    let n := p*q
    ∀ ab ∈ [(1,1), (n+1,1), (n^2+n+1,1), (n^2+1,2), (n+1,n+3)],
      ¬ IsSquare ((2*ab.2*p+ab.1)*(2*ab.2*q+ab.1)) := by
  intro p q n ab hab
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only
  · exact shift_local_obstruction (ℓ := 3) (by decide) (by decide +kernel) (by decide +kernel)
  · exact shift_local_obstruction (ℓ := 5) (by decide) (by decide +kernel) (by decide +kernel)
  · exact shift_local_obstruction (ℓ := 11) (by decide) (by decide +kernel) (by decide +kernel)
  · exact shift_local_obstruction (ℓ := 13) (by decide) (by decide +kernel) (by decide +kernel)
  · exact shift_local_obstruction (ℓ := 17) (by decide) (by decide +kernel) (by decide +kernel)

private theorem portfolio_prime_32433156901 : Nat.Prime 32433156901 := by
  apply prime_of_partial_order_cover (4691107227 : ZMod 32433156901) (F := 36036841) (ps := [1399, 25759])
    (by decide) (by decide) (by decide)
  · exact Covers.cons 1 (p := 1399) (by norm_num) (Covers.cons 1 (p := 25759) (by norm_num) covers_one)
  · reduce_mod_char
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · change Nat.Coprime (((4691107227 : ZMod 32433156901)^25759 - 1).val) 32433156901
      have h : (4691107227 : ZMod 32433156901)^25759 = 29092641726 := by reduce_mod_char
      rw [h]
      decide +kernel
    · change Nat.Coprime (((4691107227 : ZMod 32433156901)^1399 - 1).val) 32433156901
      have h : (4691107227 : ZMod 32433156901)^1399 = 12015160686 := by reduce_mod_char
      rw [h]
      decide +kernel

private theorem portfolio_prime_34543964027 : Nat.Prime 34543964027 := by
  apply prime_of_partial_order_cover (31019687658 : ZMod 34543964027) (F := 844637) (ps := [47, 17971])
    (by decide) (by decide) (by decide)
  · exact Covers.cons 1 (p := 47) (by norm_num) (Covers.cons 1 (p := 17971) (by norm_num) covers_one)
  · reduce_mod_char
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · change Nat.Coprime (((31019687658 : ZMod 34543964027)^17971 - 1).val) 34543964027
      have h : (31019687658 : ZMod 34543964027)^17971 = 14977376688 := by reduce_mod_char
      rw [h]
      decide +kernel
    · change Nat.Coprime (((31019687658 : ZMod 34543964027)^47 - 1).val) 34543964027
      have h : (31019687658 : ZMod 34543964027)^47 = 6449102759 := by reduce_mod_char
      rw [h]
      decide +kernel

theorem five_shifts_input :
    Nat.Prime 32433156901 ∧ Nat.Prime 34543964027 ∧
    (1120369805270190800327 : ℕ) = 32433156901 * 34543964027 :=
  ⟨portfolio_prime_32433156901, portfolio_prime_34543964027, rfl⟩

end PrimeFactors
