import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Explicit elementary growth bounds for Chebyshev's factorial ratio.
The integer inequalities keep numerator and denominator separate. -/

namespace PrimeFactors.ChebyshevFactorialRatio

def num (m : ℕ) := (30*m).factorial * m.factorial
def den (m : ℕ) := (15*m).factorial * (10*m).factorial * (6*m).factorial

private def block (c m : ℕ) := (c*m+1).ascFactorial c
private def up (m : ℕ) := block 30 m * (m+1)
private def down (m : ℕ) := block 15 m * block 10 m * block 6 m

private theorem advance (c m : ℕ) : (c*(m+1)).factorial = (c*m).factorial*block c m := by
  rw [Nat.mul_succ,block,Nat.factorial_mul_ascFactorial]

private theorem num_next (m : ℕ) : num (m+1)=num m*up m := by
  unfold num up
  rw [advance 30 m,Nat.factorial_succ m]
  rw [Nat.mul_comm (m+1) m.factorial,Nat.mul_mul_mul_comm]

private theorem den_next (m : ℕ) : den (m+1)=den m*down m := by
  simp only [den,down,advance]; ac_rfl

private theorem extrema (c m : ℕ) :
    (c*m)^c ≤ block c m ∧ block c m ≤ (c*(m+1))^c := by
  refine ⟨(Nat.pow_le_pow_left (Nat.le_succ _) _).trans (Nat.pow_succ_le_ascFactorial (c*m+1) c),?_⟩
  simpa only [Nat.mul_succ,block] using Nat.ascFactorial_le_pow_add (c*m) c

private abbrev A : ℕ := 30^30
private abbrev B : ℕ := 15^15*10^10*6^6

private theorem up_extrema (m : ℕ) : A*m^31 ≤ up m ∧ up m ≤ A*(m+1)^31 := by
  obtain ⟨lo,hi⟩ := extrema 30 m
  have low := Nat.mul_le_mul lo (Nat.le_succ m)
  have high := Nat.mul_le_mul_right (m+1) hi
  simpa only [A,up,mul_pow,pow_succ m 30,pow_succ (m+1) 30,Nat.mul_assoc] using And.intro low high

private theorem down_extrema (m : ℕ) : B*m^31 ≤ down m ∧ down m ≤ B*(m+1)^31 := by
  have bound (t : ℕ) : (15*t)^15*(10*t)^10*(6*t)^6=B*t^31 := by
    rw [mul_pow,mul_pow,mul_pow]; dsimp only [B]; ring
  have low := Nat.mul_le_mul (Nat.mul_le_mul (extrema 15 m).1 (extrema 10 m).1) (extrema 6 m).1
  have high := Nat.mul_le_mul (Nat.mul_le_mul (extrema 15 m).2 (extrema 10 m).2) (extrema 6 m).2
  rw [bound] at low high
  exact ⟨low,high⟩

/-- The ratio (m+1)/m decreases with m; all comparisons use integer powers. -/
private theorem lift {s t k m : ℕ} (kp : 0<k) (km : k≤m)
    (base : s*(k+1)^31 < t*k^31) : s*(m+1)^31 < t*m^31 := by
  have frac : k*(m+1) ≤ (k+1)*m := by rw [Nat.mul_succ,Nat.succ_mul]; omega
  have p := Nat.pow_le_pow_left frac 31
  simp only [mul_pow] at p
  have mp : 0<m^31 := Nat.pow_pos (kp.trans_le km)
  apply Nat.lt_of_mul_lt_mul_right (a:=k^31)
  calc
    s*(m+1)^31*k^31 = s*(k^31*(m+1)^31) := by
      rw [Nat.mul_assoc,Nat.mul_comm ((m+1)^31)]
    _ ≤ s*((k+1)^31*m^31) := Nat.mul_le_mul_left _ p
    _ = (s*(k+1)^31)*m^31 := (Nat.mul_assoc ..).symm
    _ < (t*k^31)*m^31 := Nat.mul_lt_mul_of_pos_right base mp
    _ = t*m^31*k^31 := Nat.mul_right_comm ..

private theorem step {k m lo hi : ℕ} (kp : 0<k) (km : k≤m)
    (lower : (2^lo*B)*(k+1)^31 < A*k^31)
    (upper : A*(k+1)^31 < (2^hi*B)*k^31) :
    2^lo*down m < up m ∧ up m < 2^hi*down m := by
  obtain ⟨u₀,u₁⟩ := up_extrema m
  obtain ⟨d₀,d₁⟩ := down_extrema m
  have l := lift kp km lower
  have h := lift kp km upper
  rw [mul_assoc] at l
  rw [mul_assoc] at h
  exact ⟨((Nat.mul_le_mul_left _ d₁).trans_lt l).trans_le u₀,
    (u₁.trans_lt h).trans_le (Nat.mul_le_mul_left _ d₀)⟩

private theorem precise {m : ℕ} (le : 512≤m) :
    2^39*down m < up m ∧ up m < 2^40*down m :=
  step (by decide : 0<512) le (by decide +kernel) (by decide +kernel)

private theorem coarse_step (m : ℕ) : down m ≤ up m ∧ up m ≤ 2^71*down m := by
  rcases m with _|m
  · decide +kernel
  · have ⟨a,b⟩ := step (lo:=0) (hi:=71) (by decide : 0<1) (Nat.succ_pos m)
        (by decide +kernel) (by decide +kernel)
    exact ⟨by simpa using a.le,b.le⟩

/-- Starting already at 512, adjacent factorial ratios lie strictly between 2^39
and 2^40. No division or integrality of the factorial ratio is required. -/
theorem successive {m : ℕ} (large : 512≤m) :
    2^39*(num m*den (m+1)) < num (m+1)*den m ∧
      num (m+1)*den m < 2^40*(num m*den (m+1)) := by
  obtain ⟨a,b⟩ := precise large
  have pos : 0<num m*den m := by unfold num den; positivity
  rw [num_next,den_next]
  simpa only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using
    And.intro (Nat.mul_lt_mul_of_pos_right a pos) (Nat.mul_lt_mul_of_pos_right b pos)

private theorem combine {m e f lo hi : ℕ}
    (l : 2^lo*down m ≤ up m) (h : up m ≤ 2^hi*down m)
    (prev : 2^e*den m≤num m ∧ num m≤2^f*den m) :
    2^(e+lo)*den (m+1)≤num (m+1) ∧ num (m+1)≤2^(f+hi)*den (m+1) := by
  rw [num_next,den_next,pow_add,pow_add]
  exact ⟨by simpa only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using Nat.mul_le_mul prev.1 l,
    by simpa only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using Nat.mul_le_mul prev.2 h⟩

private theorem coarse (m : ℕ) : 2^0*den m≤num m ∧ num m≤2^(71*m)*den m := by
  induction m with
  | zero => decide +kernel
  | succ m ih =>
    obtain ⟨l,h⟩ := coarse_step m
    have b := combine (lo:=0) (by simpa using l) h ih
    simpa only [Nat.mul_succ,Nat.zero_add] using b

private theorem envelope {C : ℕ} (slack : 19968≤C) (m : ℕ) :
    2^(39*m-C)*den m≤num m ∧ num m≤2^(40*m+C)*den m := by
  induction m with
  | zero =>
    simp only [num,den,Nat.mul_zero,Nat.zero_sub,Nat.zero_add,Nat.factorial_zero,Nat.mul_one,pow_zero,true_and,le_refl]
    exact Nat.one_le_pow _ _ (by decide)
  | succ m ih =>
    by_cases low : m<512
    · obtain ⟨l,h⟩ := coarse (m+1)
      have elo : 39*(m+1)-C=0 := by omega
      rw [elo]
      exact ⟨l,h.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega)))⟩
    · obtain ⟨a,b⟩ := precise (by omega : 512≤m)
      have result := combine a.le b.le ih
      have elo : 39*(m+1)-C≤(39*m-C)+39 := by omega
      have ehi : 40*(m+1)+C=40*m+C+40 := by omega
      exact ⟨(Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0<2) elo)).trans result.1,
        ehi ▸ result.2⟩

/-- Uniform integer upper bound, including the initial 512 ratios. -/
theorem upper (m : ℕ) : num m ≤ 2^(40*m+32768)*den m := (envelope (C:=32768) (by decide) m).2

/-- Uniform integer lower bound, with the same additive exponent allowance. -/
theorem lower (m : ℕ) : 2^(39*m)*den m ≤ 2^32768*num m := by
  have room : 39*m ≤ 32768+(39*m-32768) := by omega
  calc
    _ ≤ 2^(32768+(39*m-32768))*den m :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) room)
    _ = 2^32768*(2^(39*m-32768)*den m) := by rw [pow_add,mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ (envelope (C:=32768) (by decide) m).1

end PrimeFactors.ChebyshevFactorialRatio
