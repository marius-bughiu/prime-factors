import PrimeFactors.ResidueCount
import Mathlib.Logic.Equiv.Prod
import Mathlib.SetTheory.Cardinal.Finite

namespace PrimeFactors

/-- Combining coprime moduli preserves exactly the pairs of local constraints on the sum. -/
theorem admissibleSum_crt_iff {a b : ℕ} (h : a.Coprime b) (n s : ZMod (a * b)) :
    let e := ZMod.chineseRemainder h
    AdmissibleSum n s ↔ AdmissibleSum (e n).1 (e s).1 ∧ AdmissibleSum (e n).2 (e s).2 := by
  let e := ZMod.chineseRemainder h
  change AdmissibleSum n s ↔ AdmissibleSum (e n).1 (e s).1 ∧ AdmissibleSum (e n).2 (e s).2
  constructor
  · rintro ⟨x, y, rfl, rfl⟩
    rw [map_add, map_mul]
    exact ⟨⟨(e x).1, (e y).1, rfl, rfl⟩, ⟨(e x).2, (e y).2, rfl, rfl⟩⟩
  · rintro ⟨⟨x, y, hxy, hs⟩, ⟨u, v, huv, ht⟩⟩
    refine ⟨e.symm (x, u), e.symm (y, v), e.injective ?_, e.injective ?_⟩
    · rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
      exact Prod.ext hxy huv
    · rw [map_add, e.apply_symm_apply, e.apply_symm_apply]
      exact Prod.ext hs ht

/-- The exact number of admissible classes per period multiplies for coprime moduli. -/
theorem card_admissibleSum_crt {a b : ℕ} (h : a.Coprime b) (N : ℕ) :
    Nat.card {s : ZMod (a * b) // AdmissibleSum (N : ZMod (a * b)) s} =
      Nat.card {s : ZMod a // AdmissibleSum (N : ZMod a) s} *
      Nat.card {s : ZMod b // AdmissibleSum (N : ZMod b) s} := by
  rw [← Nat.card_prod]
  apply Nat.card_congr
  refine Equiv.trans ?_ Equiv.subtypeProdEquivProd
  apply (ZMod.chineseRemainder h).toEquiv.subtypeEquiv
  intro s
  simpa only [RingEquiv.coe_toEquiv, map_natCast, Prod.fst_natCast, Prod.snd_natCast] using
    admissibleSum_crt_iff h (N : ZMod (a * b)) s

/-- A worked example using only the product: six of the 35 sum classes survive. -/
theorem card_admissibleSum_143_mod_35 :
    Nat.card {s : ZMod 35 // AdmissibleSum (143 : ZMod 35) s} = 6 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  change Nat.card {s : ZMod (5 * 7) // AdmissibleSum ((143 : ℕ) : ZMod (5 * 7)) s} = 6
  rw [card_admissibleSum_crt (a := 5) (b := 7) (by decide) 143,
    card_admissibleSum_eq 5 _ (by decide), card_admissibleSum_eq 7 _ (by decide),
    card_factorSumResidues_of_nonsquare 5 _ (by decide) (by
      rintro ⟨x, hx⟩
      exact (by decide : ∀ z : ZMod 5, ((143 : ℕ) : ZMod 5) ≠ z * z) x hx),
    card_factorSumResidues_of_nonsquare 7 _ (by decide) (by
      rintro ⟨x, hx⟩
      exact (by decide : ∀ z : ZMod 7, ((143 : ℕ) : ZMod 7) ≠ z * z) x hx)]

end PrimeFactors
