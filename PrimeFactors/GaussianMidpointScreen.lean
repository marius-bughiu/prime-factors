import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum.Prime

/-! In a given step-four Fermat midpoint class, testing for a square
difference modulo 16 or 32 forces the stronger midpoint class. -/
namespace PrimeFactors.GaussianMidpointScreen

/-- Writing the modular square test by addition avoids truncated subtraction. -/
def Screen (d n m : ℕ) : Prop := ∃ z : ℕ, m^2 ≡ n+z^2 [MOD d]

theorem screen_iff {d n m : ℕ} (above : n≤m^2) :
    Screen d n m ↔ ∃ z : ℕ, m^2-n ≡ z^2 [MOD d] := by
  constructor
  · rintro ⟨z,h⟩
    exact ⟨z,Nat.ModEq.add_left_cancel' n (by simpa only [Nat.add_sub_of_le above] using h)⟩
  · rintro ⟨z,h⟩
    exact ⟨z,by simpa only [Nat.add_sub_of_le above] using h.add_left n⟩

private theorem from_table {d n m r c : ℕ} (eight : 8∣d) (pos : 0<d)
    (nr : n%8=r) (mc : m%4=c) (pass : Screen d n m)
    (table : ∀ a b : Fin d, a.val%4=c → a.val^2 ≡ r+b.val^2 [MOD 8] →
      a.val^2+1 ≡ 2*a.val+b.val^2 [MOD d]) : 2*m ≡ n+1 [MOD d] := by
  obtain ⟨z,h⟩ := pass
  let a : Fin d := ⟨m%d,Nat.mod_lt _ pos⟩
  let b : Fin d := ⟨z%d,Nat.mod_lt _ pos⟩
  have am : a.val ≡ m [MOD d] := Nat.mod_modEq _ _
  have bz : b.val ≡ z [MOD d] := Nat.mod_modEq _ _
  have small : a.val%4=c := Eq.trans (am.of_dvd ((by decide : 4∣8).trans eight)) mc
  have rn : n ≡ r [MOD 8] := nr ▸ (Nat.mod_modEq n 8).symm
  have square := ((am.pow 2).trans h).of_dvd eight
  have localEq := table a b small (square.trans (rn.add ((bz.pow 2).of_dvd eight).symm))
  have sumEq := ((am.pow 2).add_right 1).symm.trans
    (localEq.trans ((am.mul_left 2).add (bz.pow 2)))
  apply (Nat.ModEq.add_right_cancel' (z^2) ?_).symm
  simpa only [Nat.add_right_comm n (z^2) 1] using (h.add_right 1).symm.trans sumEq

/-- For product remainder one modulo eight, the modulo-16 screen suffices. -/
theorem one_mod_eight {n m : ℕ} (one : n%8=1) (class4 : m ≡ (n+1)/2 [MOD 4])
    (pass : Screen 16 n m) : m ≡ (n+1)/2 [MOD 8] := by
  have mc : m%4=1 := by unfold Nat.ModEq at class4; omega
  have double := from_table (r:=1) (c:=1) (by decide) (by decide) one mc pass
    (by decide +kernel)
  unfold Nat.ModEq at double ⊢
  omega

/-- For product remainder five modulo eight the modulo-32 screen suffices. -/
theorem five_mod_eight {n m : ℕ} (five : n%8=5) (class4 : m ≡ (n+1)/2 [MOD 4])
    (pass : Screen 32 n m) : m ≡ (n+1)/2 [MOD 16] := by
  have mc : m%4=3 := by unfold Nat.ModEq at class4; omega
  have double := from_table (r:=5) (c:=3) (by decide) (by decide) five mc pass
    (by decide +kernel)
  unfold Nat.ModEq at double ⊢
  omega

/-- Within the step-four class, the modulo-256 survivors are exactly the
same after imposing the strongest warranted stride. -/
theorem mod256_iff {n m : ℕ} (one : n%4=1) (class4 : m ≡ (n+1)/2 [MOD 4]) :
    Screen 256 n m ↔ Screen 256 n m ∧ m ≡ (n+1)/2 [MOD (if n%8=5 then 16 else 8)] := by
  refine ⟨fun h => ⟨h,?_⟩,And.left⟩
  obtain ⟨z,hz⟩ := h
  by_cases five : n%8=5
  · rw [if_pos five]
    exact five_mod_eight five class4 ⟨z,hz.of_dvd (by decide)⟩
  · rw [if_neg five]
    exact one_mod_eight (by omega) class4 ⟨z,hz.of_dvd (by decide)⟩

/-- A midpoint before the true one illustrates sharpness on each branch.
Both products also pass the floor-square-root remainder gate. -/
theorem sharp_controls :
    Nat.Prime 521 ∧ Nat.Prime 1009 ∧ 521*1009=525689 ∧ 525689=725^2+8^2 ∧
    525689%8=1 ∧ 525689≤729^2 ∧ 729<(521+1009)/2 ∧
    729 ≡ (525689+1)/2 [MOD 4] ∧ Screen 8 525689 729 ∧ ¬(729 ≡ (525689+1)/2 [MOD 8]) ∧
    Nat.Prime 293 ∧ Nat.Prime 457 ∧ 293*457=133901 ∧ 133901=365^2+26^2 ∧
    133901%8=5 ∧ 133901≤367^2 ∧ 367<(293+457)/2 ∧
    367 ≡ (133901+1)/2 [MOD 4] ∧ Screen 16 133901 367 ∧ ¬(367 ≡ (133901+1)/2 [MOD 16]) := by
  have first : Screen 8 525689 729 := ⟨0,by decide⟩
  have second : Screen 16 133901 367 := ⟨2,by decide⟩
  norm_num [first,second,Nat.ModEq]
  decide

end PrimeFactors.GaussianMidpointScreen
