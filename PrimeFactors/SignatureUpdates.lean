import Mathlib.Tactic

/-! Update a modular-power signature when adding a CRT contribution to the
current reduced residue. Powers are taken in a group so left targets may use
the inverse of a right-hand update. -/

namespace PrimeFactors.SignatureUpdates

/-- Adding two reduced digits needs at most one subtraction of the period. -/
theorem update {G : Type*} [Group G] (g : G) (offset slope : ℤ) {r d M : ℕ}
    (hr : r<M) (hd : d<M) :
    g^(offset+slope*((r+d)%M:ℕ)) =
      g^(offset+slope*r)*(if r+d<M then g^(slope*d) else g^(slope*((d:ℤ)-M))) := by
  by_cases small : r+d<M
  · rw [if_pos small,Nat.mod_eq_of_lt small,←zpow_add]
    congr 1; push_cast; ring
  · have hr' : r+d-M<M := by omega
    rw [if_neg small,Nat.mod_eq_sub_mod (by omega : M≤r+d),Nat.mod_eq_of_lt hr',←zpow_add]
    congr 1
    rw [Nat.cast_sub (by omega : M≤r+d),Nat.cast_add]
    ring

/-- One precomputed inverse period supplies the other multiplier in either half.
The two components are (right unwrapped, right wrapped) or (left wrapped,
left unwrapped), respectively. -/
theorem digit_powers {G : Type*} [Group G] (g : G) {d M : ℕ} (hd : d≤M) :
    g^(d:ℤ)*(g^(M:ℤ))⁻¹ = g^((d:ℤ)-M) ∧
    g^((M-d:ℕ):ℤ)*(g^(M:ℤ))⁻¹ = g^(-(d:ℤ)) := by
  rw [←zpow_neg,←zpow_add,←zpow_add,Nat.cast_sub hd]
  constructor
  · rfl
  · congr 1; ring

end PrimeFactors.SignatureUpdates
