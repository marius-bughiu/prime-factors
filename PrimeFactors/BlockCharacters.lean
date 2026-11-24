import PrimeFactors.FactorSum
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.Prime

namespace PrimeFactors

/-- If an odd-length list of discriminants has square product, an odd-prime
square test must accept at least one member, including at primes dividing the product. -/
theorem exists_square_mod_of_odd_square_product (ℓ : ℕ) [Fact ℓ.Prime]
    (ds : List ℤ) (odd : Odd ds.length) (square : IsSquare ds.prod) :
    ∃ d ∈ ds, IsSquare (d : ZMod ℓ) := by
  by_contra! none
  have signs : ds.map (legendreSym ℓ) = ds.map (fun _ => (-1 : ℤ)) := by
    apply List.map_congr_left
    intro d hd
    exact (legendreSym.eq_neg_one_iff ℓ).mpr (none d hd)
  have negative : legendreSym ℓ ds.prod = -1 := by
    calc
      legendreSym ℓ ds.prod = (ds.map (legendreSym ℓ)).prod :=
        map_list_prod (legendreSym.hom ℓ).toMonoidHom ds
      _ = (-1 : ℤ) ^ ds.length := by rw [signs]; simp
      _ = -1 := odd.neg_one_pow
  obtain ⟨r, hr⟩ := square
  exact (legendreSym.eq_neg_one_iff ℓ).mp negative ⟨(r : ZMod ℓ), by simp [hr]⟩

/-- These consecutive parity-compatible false sums of 149·293 cannot all be
rejected by any one odd prime. -/
theorem single_prime_obstruction_43657 (ℓ : ℕ) [Fact ℓ.Prime] (odd : ℓ ≠ 2) :
    AdmissibleSum (43657 : ZMod ℓ) 422 ∨ AdmissibleSum (43657 : ZMod ℓ) 426 ∨
      AdmissibleSum (43657 : ZMod ℓ) 430 := by
  let D := fun s : ℤ => s ^ 2 - 4 * 43657
  obtain ⟨d, mem, sq⟩ := exists_square_mod_of_odd_square_product ℓ [D 422, D 426, D 430]
    (by decide) ⟨493056, by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  simp only [admissibleSum_iff_isSquare odd]
  rcases mem with rfl | rfl | rfl
  · left; simpa only [D, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using sq
  · right; left; simpa only [D, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using sq
  · right; right; simpa only [D, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using sq

/-- Two tests do reject the whole three-candidate block. -/
theorem two_primes_exclude_43657 :
    43657 = 149 * 293 ∧ Nat.Prime 149 ∧ Nat.Prime 293 ∧
    ∀ s ∈ ([422, 426, 430] : List ℕ),
      ¬ (AdmissibleSum (43657 : ZMod 5) (s : ZMod 5) ∧
         AdmissibleSum (43657 : ZMod 7) (s : ZMod 7)) := by
  refine ⟨by decide, by norm_num, by norm_num, ?_⟩
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> unfold AdmissibleSum <;> decide

end PrimeFactors
