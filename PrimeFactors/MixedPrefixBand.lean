import PrimeFactors.MixedPrefixSlab
import Mathlib.Tactic.FieldSimp

/-! Convert a high product prefix and a band of first-factor quotient values
from natural-number arithmetic to the rational slab used by the area bound. -/

namespace PrimeFactors.MixedPrefixBand

/-- The first-factor quotient gives the slab, and the high-word quotient of
the product gives the interval for the translated, normalized product. -/
theorem bounds {B D L step H m r s p q i j : ℕ} (dp : 0<D) (sp : 0<step)
    (eqp : p=D*i+r) (eqq : q=D*j+s) (pos : B+m*L≤i) (last : i≤B+m*L+L)
    (head : p*q/step=H) :
    let ρ : ℚ := (r:ℚ)/D
    let σ : ℚ := (s:ℚ)/D
    let T : ℚ := (H*step:ℕ)/(D:ℚ)^2
    let U : ℚ := (step:ℚ)/(D:ℚ)^2
    let x₀ : ℚ := (B+m*L:ℕ)+ρ
    x₀≤(i:ℚ)+ρ ∧ (i:ℚ)+ρ≤x₀+L ∧
      T≤((i:ℚ)+ρ)*((j:ℚ)+σ) ∧ ((i:ℚ)+ρ)*((j:ℚ)+σ)≤T+U := by
  dsimp only
  have d : (0:ℚ)<D := by exact_mod_cast dp
  have identity : ((i:ℚ)+r/D)*(j+s/D)=(p*q:ℕ)/(D:ℚ)^2 := by
    rw [eqp,eqq]
    push_cast
    field_simp [d.ne']
    ring
  have floor : H*step≤p*q := head ▸ Nat.div_mul_le_self _ _
  have next : p*q<(H+1)*step := (Nat.div_lt_iff_lt_mul sp).mp (by omega)
  have endcap : (p*q:ℕ)≤H*step+step := by simpa only [Nat.succ_mul] using next.le
  have left' : ((B+m*L:ℕ):ℚ)≤i := by exact_mod_cast pos
  have right' : (i:ℚ)≤(B+m*L:ℕ)+(L:ℚ) := by exact_mod_cast last
  rw [identity]
  refine ⟨add_le_add_right left' _,by linarith only [right'],?_,?_⟩
  · exact div_le_div_of_nonneg_right (by exact_mod_cast floor) (sq_nonneg _)
  · rw [←add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast endcap) (sq_nonneg _)

/-- The upper endpoint for a target-width normalized prefix start. -/
theorem top {B D H step : ℕ} (dp : 0<D) (cap : H*step≤4*B^2*D^2) :
    (H*step:ℕ)/(D:ℚ)^2 ≤ 4*(B:ℚ)^2 := by
  apply (div_le_iff₀ (sq_pos_of_pos (by exact_mod_cast dp : (0:ℚ)<D))).mpr
  exact_mod_cast cap

/-- Two raw product steps fitting in D² give a half-unit normalized width. -/
theorem width {D step : ℕ} (dp : 0<D) (cap : 2*step≤D^2) :
    (step:ℚ)/(D:ℚ)^2 ≤ 1/2 := by
  apply (div_le_iff₀ (sq_pos_of_pos (by exact_mod_cast dp : (0:ℚ)<D))).mpr
  have h : 2*(step:ℚ)≤(D:ℚ)^2 := by exact_mod_cast cap
  linarith only [h]

end PrimeFactors.MixedPrefixBand
