import PrimeFactors.QuarticDivisorWindow
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Real.Basic

namespace PrimeFactors.QuarticRankCounterexample

open QuarticDivisorWindow QuarticFactorLane Finset Module

/-- The span is over every short quartic satisfying the public jet tests at radius two. -/
noncomputable def shortSpan (t D : ℤ) : Submodule ℚ (Fin 5 → ℚ) :=
  Submodule.span ℚ {z | ∃ w : Fin 5 → ℤ, jets w 6901 t ∧ height w 2 < D^2 ∧
    z = fun i => (w i : ℚ)}

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

private def witness (occupied : Bool) : Fin 4 → Fin 5 → ℤ :=
  if occupied then
    ![![190,147,-67,-16,8], ![77,-41,-65,33,-20],
      ![-237,-194,-7,-45,5], ![31,-74,-78,56,29]]
  else
    ![![49,-56,30,-8,1], ![357,-78,-49,34,-4],
      ![84,127,17,-35,15], ![725,430,182,6,-110]]

/-- A dual vector for the empty window at center 79. -/
def normal : Fin 5 → ℤ := ![-332,6213,27176,65213,70620]

noncomputable def pairing (w : Fin 5 → ℤ) : ℤ := ∑ i, normal i * w i

/-- This dual certificate follows from the two jets, regardless of how a row was found. -/
theorem dual_divides (w : Fin 5 → ℤ) (hw : jets w 6901 3411) :
    (6901:ℤ)^2 ∣ pairing w := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := hw
  refine ⟨-332*a + 165*b - 82*w 2 - 557890*w 3 - 2851855428*w 4,?_⟩
  simp [pairing, normal, Fin.sum_univ_five]
  simp [weights, value, slope] at ha hb
  linarith

theorem empty_normal (w : Fin 5 → ℤ) (hw : jets w 6901 3411)
    (small : height w 2 < (75:ℤ)^2) : pairing w = 0 := by
  have bound (i : Fin 5) : |normal i| ≤ (8152:ℤ)*2^i.val := by
    fin_cases i <;> decide +kernel
  have size : |pairing w| ≤ 8152 * height w 2 := by
    unfold pairing height
    refine (abs_sum_le_sum_abs ..).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    calc
      _ ≤ (8152 * 2^i.val) * |w i| :=
        mul_le_mul_of_nonneg_right (bound i) (abs_nonneg _)
      _ = _ := by ring
  exact Int.eq_zero_of_abs_lt_dvd (dual_divides w hw) (by linarith)

private theorem occupied_normal (w : Fin 5 → ℤ) (hw : jets w 6901 3416)
    (small : height w 2 < (65:ℤ)^2) :
    value (weights w) 1 (-1) = 0 :=
  root_of_divisor (W:=2) hw (d:=67) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by linarith)

private noncomputable def functional (occupied : Bool) : (Fin 5 → ℚ) →ₗ[ℚ] ℚ :=
  let v : Fin 5 → ℚ := if occupied then ![1,-1,1,-1,1] else fun i => (normal i:ℚ)
  ∑ i, v i • LinearMap.proj i

private theorem ranks (hit : Bool) :
    finrank ℚ (shortSpan (if hit then 3416 else 3411) (if hit then 65 else 75)) = 4 := by
  let row (i : Fin 4) : Fin 5 → ℚ := fun j => (witness hit i j:ℚ)
  have members : ∀ i, jets (witness hit i) 6901 (if hit then 3416 else 3411) ∧
      height (witness hit i) 2 < (if hit then (65:ℤ) else 75)^2 := by
    intro i
    cases hit <;> fin_cases i <;> unfold jets <;> decide +kernel
  have lower : Submodule.span ℚ (Set.range row) ≤
      shortSpan (if hit then 3416 else 3411) (if hit then 65 else 75) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.subset_span ⟨witness hit i,(members i).1,(members i).2,rfl⟩
  have li : LinearIndependent ℚ row := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    have lin (j : Fin 5) := congrFun ha j
    have e₀ := lin 0
    have e₁ := lin 1
    have e₂ := lin 2
    have e₃ := lin 3
    cases hit <;>
      norm_num [Fin.sum_univ_four,row,witness] at e₀ e₁ e₂ e₃ <;>
      fin_cases i <;> (first | change a 0 = 0 | change a 1 = 0 | change a 2 = 0 | change a 3 = 0) <;>
      linarith only [e₀,e₁,e₂,e₃]
  have le := Submodule.finrank_mono lower
  rw [finrank_span_eq_card li,Fintype.card_fin] at le
  have upper : shortSpan (if hit then 3416 else 3411) (if hit then 65 else 75) ≤
      LinearMap.ker (functional hit) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,small,rfl⟩
    change functional hit (fun i => (w i:ℚ)) = 0
    cases hit
    · have hz := empty_normal w hw small
      simpa [pairing, functional, Fin.sum_univ_five, normal] using
        (show ((pairing w:ℤ):ℚ)=0 by exact_mod_cast hz)
    · have hz := occupied_normal w hw small
      simpa [value, weights, functional, Fin.sum_univ_five, add_comm, add_left_comm, add_assoc] using
        (show ((value (weights w) 1 (-1):ℤ):ℚ)=0 by exact_mod_cast hz)
  have nz : functional hit ≠ 0 := by
    intro absent
    have h := LinearMap.congr_fun absent (![1,0,0,0,0] : Fin 5 → ℚ)
    cases hit <;> norm_num [functional,Fin.sum_univ_five,normal] at h
  have rankKer := Module.Dual.finrank_ker_add_one_of_ne_zero nz
  rw [Module.finrank_pi,Fintype.card_fin] at rankKer
  have up := Submodule.finrank_mono upper
  omega

/-- The exact rank, counting every short polynomial, agrees on an occupied and an empty window. -/
theorem equal_ranks : finrank ℚ (shortSpan 3416 65) = 4 ∧ finrank ℚ (shortSpan 3411 75) = 4 :=
  ⟨ranks true,ranks false⟩

private def between : Fin 5 → Fin 5 → ℤ :=
  ![![216,-57,29,48,8], ![-53,-92,57,-31,36], ![-669,-124,-99,40,28],
    ![-375,181,231,-14,-19], ![-48,-535,-29,3,-15]]

/-- The intermediate center 73 has five short independent rows. Along centers 69, 73, 79,
the exact ranks are 4, 5, 4, ruling out monotonicity even for this single product. -/
theorem middle_rank : finrank ℚ (shortSpan 3414 69) = 5 := by
  let row (i : Fin 5) : Fin 5 → ℚ := fun j => (between i j:ℚ)
  have certified (i : Fin 5) : jets (between i) 6901 3414 ∧ height (between i) 2 < (69:ℤ)^2 := by
    fin_cases i <;> unfold jets <;> decide +kernel
  have lower : Submodule.span ℚ (Set.range row) ≤ shortSpan 3414 69 := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.subset_span ⟨between i,(certified i).1,(certified i).2,rfl⟩
  have li : LinearIndependent ℚ row := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    have eqn (j : Fin 5) := congrFun ha j
    have e₀ := eqn 0
    have e₁ := eqn 1
    have e₂ := eqn 2
    have e₃ := eqn 3
    have e₄ := eqn 4
    norm_num [Fin.sum_univ_five,row,between] at e₀ e₁ e₂ e₃ e₄
    fin_cases i <;>
      (first | change a 0 = 0 | change a 1 = 0 | change a 2 = 0 |
        change a 3 = 0 | change a 4 = 0) <;>
      linarith only [e₀,e₁,e₂,e₃,e₄]
  have lo := Submodule.finrank_mono lower
  rw [finrank_span_eq_card li,Fintype.card_fin] at lo
  have hi := (shortSpan 3414 69).finrank_le
  rw [Module.finrank_pi,Fintype.card_fin] at hi
  omega

/-- The empty window's normal fails a necessary identity for a multiple of an evaluation vector. -/
theorem hankel_minor : normal 0 * normal 2 - (normal 1)^2 = -(6901:ℤ)^2 := by decide +kernel

/-- The first short quartic in that same window has no real root at all. -/
theorem empty_quartic (x : ℝ) : 0 < 49 - 56*x + 30*x^2 - 8*x^3 + x^4 := by
  calc
    0 < ((x-2)^2+3)^2 := sq_pos_of_pos (by positivity)
    _ = _ := by ring

/-- Both centers use the public stride-two anchor. Only the first window contains a divisor. -/
theorem same_product :
    Nat.Prime 67 ∧ Nat.Prime 103 ∧ 67*103=6901 ∧
    (6901:ℤ) ∣ 69+2*3416 ∧ (6901:ℤ) ∣ 79+2*3411 ∧
    (69:ℤ)+2*(-1)=67 ∧ (67:ℤ) ∣ 6901 ∧
    (∀ d : ℤ, 75≤d → d≤83 → ¬ d ∣ 6901) ∧
    (6901:ℕ)^3 * 5^5 * 2^10 < 65^10 := by
  refine ⟨by decide +kernel,by decide +kernel,rfl,by decide +kernel,by decide +kernel,
    rfl,by decide +kernel,?_,by decide +kernel⟩
  intro d lo hi
  interval_cases d <;> decide +kernel

end PrimeFactors.QuarticRankCounterexample
