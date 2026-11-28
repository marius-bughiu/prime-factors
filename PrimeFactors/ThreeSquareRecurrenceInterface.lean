import PrimeFactors.ThreeSquareIntegerCensus

/-! Translate a supplied prime-square recurrence for counts of ordered signed
integer triples into the project's three-square recurrence. The source
requires a positive target and uses the Legendre symbol and integer division.
Only the case α = 1 enters this adapter.

[ATLAS recurrence, pinned statement](https://github.com/facebookresearch/atlas-lean/blob/1839d43ea6d44c0c7218fe0ba86c23fed33d800a/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean#L2383-L2391)
[ATLAS ordered signed count](https://github.com/facebookresearch/atlas-lean/blob/1839d43ea6d44c0c7218fe0ba86c23fed33d800a/MathlibExt/NumberTheory/QuadraticForms/ThreeSquares.lean#L31-L34) -/

namespace PrimeFactors.ThreeSquareRecurrenceInterface

open ThreeSquareIntegerCensus FiniteThreeSquareTwists

/-- Integer geometric quotient in the source recurrence. -/
private def geometric (p : ℕ) (k : ℕ) : ℤ := ((p:ℤ)^k-1)/((p:ℤ)-1)

/-- The α=1 specialization of the external positive-target formula, stated
over the independently defined finite set of signed triples. Its lower count
is zero when n/p² is nonintegral. -/
def PrimeSquareInput : Prop :=
  ∀ (p n : ℕ) [Fact p.Prime], 3≤p → 1≤n →
    ((points (p^2*n)).card:ℤ) =
      (geometric p 2-legendreSym p (-(n:ℤ))*geometric p 1)*(points n).card -
      (p:ℤ)*geometric p 1*
        (if p^2∣n then ((points (n/p^2)).card:ℤ) else 0)

private theorem quotients {p : ℕ} (hp : 3≤p) :
    geometric p 2=(p:ℤ)+1 ∧ geometric p 1=1 := by
  have den : (p:ℤ)-1≠0 := by omega
  unfold geometric
  rw [show (p:ℤ)^2-1=((p:ℤ)-1)*((p:ℤ)+1) by ring,
    Int.mul_ediv_cancel_left _ den,pow_one,Int.ediv_self den]
  exact ⟨rfl,rfl⟩

/-- At zero the origin contributes one, both before and after scaling.
Divisibility by p² holds here, so the lower count subtracts exactly p. -/
theorem at_zero {p : ℕ} [Fact p.Prime] :
    (r₃ (p^2*0):ℤ) = ((p:ℤ)+1-jacobiSym (-(0:ℤ)) p)*r₃ 0 -
      (if p^2∣0 then (p:ℤ)*r₃ (0/p^2) else 0) := by
  rw [←jacobiSym.legendreSym.to_jacobiSym]
  simp [zero_count]

/-- The positive-target input suffices for every natural target, including zero. -/
theorem hirschhorn_sellers (h : PrimeSquareInput) : HirschhornSellers := by
  intro p n pp odd
  letI : Fact p.Prime := ⟨pp⟩
  rcases n.eq_zero_or_pos with rfl|np
  · exact at_zero
  have hp : 3≤p := by
    obtain ⟨k,hk⟩ := odd
    have low := pp.two_le
    omega
  have eq := h p n hp np
  obtain ⟨g2,g1⟩ := quotients hp
  rw [g2,g1,mul_one,mul_one,jacobiSym.legendreSym.to_jacobiSym] at eq
  simp only [card_points] at eq
  by_cases integral : p^2∣n <;> simpa only [integral,if_true,if_false,mul_zero] using eq

end PrimeFactors.ThreeSquareRecurrenceInterface
