import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace PrimeFactors.NormRowAdvice

/-- For a fixed factor p, a specified product residue modulo M, and a
real interval of width W, there are at most 1+W/(pM) possible partners.
The interval may have fractional endpoints and no primality is required. -/
theorem partner_count {S : Finset ℕ} {p M a : ℕ} {L W : ℝ} (pp : 0<p) (mp : 0<M)
    (cop : M.Coprime p) (width : 0≤W)
    (inside : ∀ q ∈ S, L≤(p : ℝ)*q ∧ (p : ℝ)*q<L+W ∧ p*q ≡ a [MOD M]) :
    (S.card : ℝ)≤1+W/((p : ℝ)*M) := by
  have step : (0 : ℝ)<(p : ℝ)*M := by positivity
  have nonneg := div_nonneg width step.le
  rcases S.eq_empty_or_nonempty with rfl | nonempty
  · simpa using (show (0 : ℝ)≤1+W/((p : ℝ)*M) by linarith)
  let first := S.min' nonempty
  have first_mem : first ∈ S := S.min'_mem nonempty
  let index (q : ℕ) := (q-first)/M
  have restore (q : ℕ) (hq : q ∈ S) : q=first+index q*M := by
    have le : first≤q := S.min'_le _ hq
    have same := Nat.ModEq.cancel_left_of_coprime cop
      ((inside first first_mem).2.2.trans (inside q hq).2.2.symm)
    have dv : M∣q-first := (Nat.modEq_iff_dvd' le).mp same
    dsimp [index]
    rw [Nat.div_mul_cancel dv]
    omega
  let limit := ⌊W/((p : ℝ)*M)⌋₊
  have count : S.card≤(Finset.range (limit+1)).card := by
    apply Finset.card_le_card_of_injOn index
    · intro q hq
      have low := (inside first first_mem).1
      have high := (inside q hq).2.1
      have eqn : (q : ℝ)=first+(index q : ℝ)*M := by exact_mod_cast restore q hq
      have block : (index q : ℝ)≤W/((p : ℝ)*M) := by
        apply (le_div_iff₀ step).mpr
        rw [eqn] at high
        nlinarith only [low,high]
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor block))
    · intro q hq r hr eqn
      rw [restore q hq,restore r hr,eqn]
  rw [Finset.card_range] at count
  have real_count : (S.card : ℝ)≤(limit : ℝ)+1 := by exact_mod_cast count
  have flo : (limit : ℝ)≤W/((p : ℝ)*M) := Nat.floor_le nonneg
  linarith

end PrimeFactors.NormRowAdvice
