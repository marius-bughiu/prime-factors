import PrimeFactors.QuarticDivisorWindow
import Mathlib.Tactic

namespace PrimeFactors.QuarticBasisTranslation

open QuarticDivisorWindow QuarticFactorLane

/-- Coefficients of P(x+h), with the constant term first. -/
noncomputable def translate (v : Fin 5 → ℤ) (h : ℤ) : Fin 5 → ℤ :=
  ![value (weights v) 1 h, slope v h, v 2+3*h*v 3+6*h^2*v 4, v 3+4*h*v 4, v 4]

theorem eval_translate (v : Fin 5 → ℤ) (x h : ℤ) :
    value (weights (translate v h)) 1 x = value (weights v) 1 (x+h) := by
  simp [translate,weights,value,QuarticDivisorWindow.slope]
  ring

theorem slope_translate (v : Fin 5 → ℤ) (x h : ℤ) :
    slope (translate v h) x = slope v (x+h) := by
  simp [translate,QuarticDivisorWindow.slope]
  ring

/-- After moving the center by stride*h, translation gives exactly the new lattice. -/
theorem jets_translate (v : Fin 5 → ℤ) (n t h : ℤ) :
    jets (translate v h) n (t-h) ↔ jets v n t := by
  simp [jets,eval_translate,slope_translate]

/-- An ordered binomial minor, expanded along its first row. -/
private noncomputable def minor : List ℕ → List ℕ → ℤ
  | [], _ => 1
  | i::tail, cols => (cols.zipIdx.map (fun (j,k) =>
      (-1:ℤ)^k*(i.choose j : ℤ)*minor tail (cols.eraseIdx k))).sum

private noncomputable def subsets (k : ℕ) : List (List ℕ) :=
  [0,1,2,3,4].sublists.filter (fun I => I.length=k)

/-- Sum of square coefficients of minors whose translation degree is e. -/
noncomputable def minorCoeff (k e : ℕ) : ℤ :=
  ((subsets k).map (fun I => ((subsets k).map (fun J =>
    if I.sum=J.sum+e then (minor I J)^2 else 0)).sum)).sum

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Every squared-minor coefficient of the dimension-five binomial matrix.
For a k-minor the degree is at most k(5-k) ≤ 6. -/
theorem minor_coefficients :
    ([1,2,3,4].map (fun k => (List.range 7).map (minorCoeff k))) =
    [[5,30,46,17,1,0,0],[10,90,227,205,80,13,1],
     [10,90,227,205,80,13,1],[5,30,46,17,1,0,0]] := by decide +kernel

/-- Squared Frobenius norms for the first and second exterior powers.
Here u is the square of the scaled shift. -/
noncomputable def f₁ (u : ℚ) : ℚ := 5+30*u+46*u^2+17*u^3+u^4
noncomputable def f₂ (u : ℚ) : ℚ := 10+90*u+227*u^2+205*u^3+80*u^4+13*u^5+u^6

noncomputable def ratio (r : ℚ) : ℚ := 2^20*(f₁ (r^2)*f₂ (r^2))^4

theorem worst_norms : f₁ (3^2) = 22955 ∧ f₂ (3^2) = 1992610 := by decide +kernel

theorem ratio_mono {a b : ℚ} (ap : 0≤a) (ab : a≤b) : ratio a≤ratio b := by
  have bp := ap.trans ab
  unfold ratio f₁ f₂
  gcongr

/-- The numerical potential comparison only needs a positive common lower
bound for all possible final potentials, and a 3/4 decrease per swap. -/
theorem swap_cutoff {steps limit : ℕ} {P : ℕ → ℚ} {L R : ℚ}
    (lp : 0<L) (last : L≤P steps) (first : P 0≤R*L)
    (drop : ∀ i<steps, 4*P (i+1) ≤ 3*P i) (cut : R*(3:ℚ)^limit < 4^limit) :
    steps < limit := by
  have chain (i : ℕ) (hn : i≤steps) : (4:ℚ)^i*P i ≤ 3^i*P 0 := by
    induction i with
    | zero => simp
    | succ i ih =>
      calc
        (4:ℚ)^(i+1)*P (i+1) = 4^i*(4*P (i+1)) := by ring
        _ ≤ 4^i*(3*P i) := mul_le_mul_of_nonneg_left (drop i (by omega)) (by positivity)
        _ = 3*(4^i*P i) := by ring
        _ ≤ 3*(3^i*P 0) := mul_le_mul_of_nonneg_left (ih (by omega)) (by norm_num)
        _ = 3^(i+1)*P 0 := by ring
  have bound : (4:ℚ)^steps ≤ R*3^steps := (mul_le_mul_iff_of_pos_right lp).mp (by
    calc
      (4:ℚ)^steps*L ≤ 4^steps*P steps := mul_le_mul_of_nonneg_left last (by positivity)
      _ ≤ 3^steps*P 0 := chain steps le_rfl
      _ ≤ 3^steps*(R*L) := mul_le_mul_of_nonneg_left first (by positivity)
      _ = R*3^steps*L := by ring)
  by_contra! large
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le large
  have sup : (3:ℚ)^d ≤ 4^d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  have contra : R*3^(limit+d) < (4:ℚ)^(limit+d) := by
    calc R*3^(limit+d) = (R*3^limit)*3^d := by ring
         _ < 4^limit*3^d := mul_lt_mul_of_pos_right cut (by positivity)
         _ ≤ 4^limit*4^d := mul_le_mul_of_nonneg_left sup (by positivity)
         _ = 4^(limit+d) := by ring
  exact (not_lt_of_ge bound) contra

theorem general_cut : ratio 3*(3:ℚ)^390 < 4^390 := by decide +kernel
theorem large_radius_cut : ratio (2+1/65536)*(3:ℚ)^307 < 4^307 := by decide +kernel

set_option exponentiation.threshold 512 in
/-- The two swap caps once the geometric comparison to the exterior minima has
supplied a potential lower bound L and the stated initial ratio. -/
theorem adjacent_swaps {steps W : ℕ} {P : ℕ → ℚ} {L : ℚ}
    (wp : 0<W) (lp : 0<L) (last : L≤P steps)
    (first : P 0≤ratio (2+1/(W:ℚ))*L) (drop : ∀ i<steps, 4*P (i+1) ≤ 3*P i) :
    steps≤389 ∧ (65536≤W → steps≤306) := by
  have one : (1:ℚ)≤W := by exact_mod_cast wp
  have pos : 0<(W:ℚ) := by positivity
  have rp : 0≤2+1/(W:ℚ) := by positivity
  have inv : 1/(W:ℚ)≤1 := (div_le_iff₀ pos).mpr (by simpa using one)
  have initial := first.trans (mul_le_mul_of_nonneg_right (ratio_mono rp (by linarith : 2+1/(W:ℚ)≤3)) lp.le)
  constructor
  · exact Nat.le_of_lt_succ (swap_cutoff lp last initial drop general_cut)
  · intro large
    have size : (65536:ℚ)≤W := by exact_mod_cast large
    have inv' : 1/(W:ℚ)≤1/65536 :=
      (div_le_div_iff₀ pos (by norm_num : (0:ℚ)<65536)).mpr (by simpa using size)
    have init := first.trans (mul_le_mul_of_nonneg_right (ratio_mono rp (add_le_add_left inv' 2)) lp.le)
    exact Nat.le_of_lt_succ (swap_cutoff lp last init drop large_radius_cut)

end PrimeFactors.QuarticBasisTranslation
