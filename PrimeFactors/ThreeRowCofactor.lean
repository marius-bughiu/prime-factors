import PrimeFactors.QuarticDivisorWindow
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.LinearCombination

namespace PrimeFactors.ThreeRowCofactor

variable {R : Type*} [CommRing R]

noncomputable def eval (v : Fin 5 → R) (x : R) : R :=
  v 0 + v 1*x + v 2*x^2 + v 3*x^3 + v 4*x^4

noncomputable def slope (v : Fin 5 → R) (x : R) : R :=
  v 1 + 2*v 2*x + 3*v 3*x^2 + 4*v 4*x^3

/-- Coefficients of K=(X−t)²(X−x) and (X+2t+x)K, in increasing degree. -/
noncomputable def cubic (x t : R) : Fin 5 → R :=
  ![-t^2*x,t^2+2*t*x,-(2*t+x),1,0]

noncomputable def quartic (x t : R) : Fin 5 → R :=
  ![-(2*t+x)*t^2*x,2*t^3+4*t^2*x+2*t*x^2,-(3*t^2+2*t*x+x^2),0,1]

/-- Three zeros counting multiplicity leave two free coefficients. This holds even
over a ring with zero divisors when the root difference is invertible. -/
theorem representation {v : Fin 5 → R} {x t : R} (unit : IsUnit (x-t))
    (at_t : eval v t=0) (at_t' : slope v t=0) (at_x : eval v x=0) (j : Fin 5) :
    v j = v 3*cubic x t j + v 4*quartic x t j := by
  unfold eval at at_t at_x
  unfold slope at at_t'
  have h2 : v 2 = v 3*(-(2*t+x)) + v 4*(-(3*t^2+2*t*x+x^2)) := by
    apply (unit.pow 2).mul_left_cancel
    linear_combination at_x - at_t - (x-t)*at_t'
  have h1 : v 1 = v 3*(t^2+2*t*x) + v 4*(2*t^3+4*t^2*x+2*t*x^2) := by
    linear_combination at_t' - 2*t*h2
  have h0 : v 0 = v 3*(-t^2*x) + v 4*(-(2*t+x)*t^2*x) := by
    linear_combination at_t - t*h1 - t^2*h2
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · change v 3 = v 3*1+v 4*0; ring
  · change v 4 = v 3*0+v 4*1; ring

/-- Every three chosen coefficient columns have zero determinant. -/
theorem minor_zero (v : Fin 3 → Fin 5 → R) (col : Fin 3 → Fin 5) {x t : R}
    (unit : IsUnit (x-t)) (at_t : ∀ i, eval (v i) t=0)
    (at_t' : ∀ i, slope (v i) t=0) (at_x : ∀ i, eval (v i) x=0) :
    (Matrix.of fun i j => v i (col j)).det=0 := by
  let mat : Matrix (Fin 3) (Fin 3) R := fun i j =>
    v i 3*cubic x t (col j) + v i 4*quartic x t (col j)
  have eq : (Matrix.of fun i j => v i (col j)) = mat := by
    ext i j
    exact representation unit (at_t i) (at_t' i) (at_x i) (col j)
  rw [eq,Matrix.det_fin_three]
  dsimp only [mat]
  ring

/-- A short three-row determinant is divisible by the cofactor q, including
composite q coprime to the root difference. Further divisibility by the smaller
factor or a zero determinant can prevent the gcd from giving a proper split. -/
theorem cofactor_dvd (v : Fin 3 → Fin 5 → ℤ) (col : Fin 3 → Fin 5)
    {n t d x : ℤ} {q W : ℕ} (qd : (q:ℤ) ∣ n) (dd : d ∣ n) (offset : d ∣ x-t)
    (unit : IsCoprime (x-t) (q:ℤ)) (nearby : |x|≤(W:ℤ))
    (jet : ∀ i, QuarticDivisorWindow.jets (v i) n t)
    (short : ∀ i, QuarticDivisorWindow.height (v i) W < d^2) :
    (q:ℤ) ∣ (Matrix.of fun i j => v i (col j)).det := by
  let rows (i : Fin 3) (j : Fin 5) : ZMod q := v i j
  have cast_eval (i : Fin 3) (z : ℤ) :
      eval (rows i) (z : ZMod q) =
        ((QuarticFactorLane.value (QuarticDivisorWindow.weights (v i)) 1 z : ℤ) : ZMod q) := by
    simp [rows,eval,QuarticFactorLane.value,QuarticDivisorWindow.weights]
  have cast_slope (i : Fin 3) :
      slope (rows i) (t : ZMod q) =
        ((QuarticDivisorWindow.slope (v i) t : ℤ) : ZMod q) := by
    simp [rows,slope,QuarticDivisorWindow.slope]
  have u : IsUnit ((x:ZMod q)-t) := by
    obtain ⟨a,b,bezout⟩ := unit
    apply isUnit_iff_exists_inv'.mpr
    refine ⟨(a : ZMod q),?_⟩
    have e := congrArg (Int.castRingHom (ZMod q)) bezout
    simpa using e
  have qn : (q:ℤ) ∣ n^2 := qd.trans (dvd_pow_self _ (by decide : 2≠0))
  have modzero := minor_zero rows col u
    (fun i => (cast_eval i t).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr
      (qn.trans (jet i).1)))
    (fun i => (cast_slope i).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr
      (qd.trans (jet i).2)))
    (fun i => by rw [cast_eval,QuarticDivisorWindow.root_of_divisor (jet i) dd offset nearby (short i)]
                 exact Int.cast_zero)
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
  rw [Int.cast_det]
  exact modzero

/-- The progression itself makes the other root different modulo every prime of
the cofactor when the candidate divisor and the cofactor are coprime. -/
theorem progression_cofactor (v : Fin 3 → Fin 5 → ℤ) (col : Fin 3 → Fin 5)
    {n c s t d x : ℤ} {q W : ℕ} (qd : (q:ℤ) ∣ n) (dd : d ∣ n)
    (cop : IsCoprime d (q:ℤ)) (stride : IsCoprime s n)
    (anchor : n ∣ c+s*t) (position : d=c+s*x) (nearby : |x|≤(W:ℤ))
    (jet : ∀ i, QuarticDivisorWindow.jets (v i) n t)
    (short : ∀ i, QuarticDivisorWindow.height (v i) W < d^2) :
    (q:ℤ) ∣ (Matrix.of fun i j => v i (col j)).det := by
  have diff : IsCoprime (x-t) (q:ℤ) := by
    obtain ⟨k,hk⟩ := qd.trans anchor
    obtain ⟨a,b,bezout⟩ := cop
    rw [position] at bezout
    refine ⟨a*s,b+a*k,?_⟩
    linear_combination bezout - a*hk
  exact cofactor_dvd v col qd dd
    (QuarticDivisorWindow.progression_offset stride anchor dd position) diff nearby jet short

namespace Example

/-- One public midpoint window spans all eleven odd possibilities, 129 through 149. -/
noncomputable def rows : Matrix (Fin 5) (Fin 5) ℤ := Matrix.of
  ![![-4828,-175,146,-24,1], ![-3568,-440,37,9,7], ![1056,1328,70,-17,8],
    ![5041,-1562,263,-22,1], ![-3817,1456,606,209,-15]]

theorem three_short (i : Fin 5) :
    QuarticDivisorWindow.jets (rows i) 22663 11262 ∧
    (QuarticDivisorWindow.height (rows i) 5 < (129:ℤ)^2 ↔ i.val<3) := by
  fin_cases i <;> unfold QuarticDivisorWindow.jets <;> decide +kernel

theorem occupied :
    (139:ℤ)+2*11262=22663 ∧ (139:ℤ)+2*(-4)=131 ∧
    ∀ i : Fin 3, QuarticFactorLane.value
      (QuarticDivisorWindow.weights (rows (i.castLE (by decide)))) 1 (-4)=0 := by
  refine ⟨by decide,by decide,?_⟩
  intro i
  fin_cases i <;> decide +kernel

theorem high_minor : (rows.submatrix ![0,1,2] ![2,3,4]).det=21971 := by
  rw [Matrix.det_fin_three]
  decide +kernel

/-- Three rows recover one prime by gcd. The product and primality of both factors
are verified for the same input. -/
theorem split :
    let q := Nat.gcd (rows.submatrix ![0,1,2] ![2,3,4]).det.natAbs 22663
    let p := 22663/q
    q=173 ∧ p=131 ∧ Nat.Prime p ∧ Nat.Prime q ∧ p*q=22663 := by
  rw [high_minor]
  decide +kernel

/-- Each of the five four-row normalized minors is coprime to the product. -/
theorem four_row_misses (i : Fin 5) :
    Nat.gcd ((rows.submatrix i.succAbove Fin.succ).det.natAbs/22663) 22663=1 := by
  rw [Matrix.det_succ_row_zero,Fin.sum_univ_four]
  simp only [Matrix.det_fin_three]
  fin_cases i <;> decide +kernel

end Example

end PrimeFactors.ThreeRowCofactor
