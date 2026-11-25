import PrimeFactors.QuarticFactorLane
import PrimeFactors.DifferenceLane
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.GCongr

namespace PrimeFactors.QuarticLaneReuse
open QuarticFactorLane

/-- The five-point leading coefficient identity at 0, r, 2r, z and z+r.
The intervening differences collected in O are all odd if r is even and z odd. -/
private theorem interpolate (w : Weights) (N u H r z : ℤ) :
    let P := fun t => value w N (u+H*t)
    2*r^2*(z*(z+r)*(z-r)*(z-2*r))*(w.c*H^4) =
      (z-r)*(z-2*r)*P 0 - 2*(z+r)*(z-2*r)*P r + z*(z+r)*P (2*r) -
      2*r*(z+r)*P z + 2*r*(z-2*r)*P (z+r) := by
  dsimp [value]
  ring

/-- For two full dyadic lanes with displacement H times an odd z and
radix H·2^(k+1), the leading coefficient must be divisible by 4·(2^(k+1))².
Only three grid values in one lane and two in the other are needed. -/
theorem leading_of_two_lanes {w : Weights} {N u H z : ℤ} (k : ℕ)
    (hH : H≠0) (hz : Odd z) :
    let r : ℤ := 2^(k+1)
    let M := 8*(H*r)^4
    let P := fun t => value w N (u+H*t)
    M ∣ P 0 → M ∣ P r → M ∣ P (2*r) → M ∣ P z → M ∣ P (z+r) →
      4*r^2 ∣ w.c := by
  intro r M P d₀ d₁ d₂ d₃ d₄
  let O := z*(z+r)*(z-r)*(z-2*r)
  have total : M ∣ 2*r^2*O*(w.c*H^4) := by
    rw [show 2*r^2*O*(w.c*H^4) = _ from interpolate w N u H r z]
    exact dvd_add (dvd_sub (dvd_add (dvd_sub (dvd_mul_of_dvd_right d₀ _)
      (dvd_mul_of_dvd_right d₁ _)) (dvd_mul_of_dvd_right d₂ _))
      (dvd_mul_of_dvd_right d₃ _)) (dvd_mul_of_dvd_right d₄ _)
  have scaled : (2*r^2*H^4)*(4*r^2) ∣ (2*r^2*H^4)*(O*w.c) := by
    convert total using 1 <;> dsimp [M] <;> ring
  have hr : r≠0 := by dsimp [r]; positivity
  have common : 2*r^2*H^4≠0 := by positivity
  have reduced := (mul_dvd_mul_iff_left common).mp scaled
  have evenR : Even r := ⟨2^k, by dsimp [r]; ring⟩
  have oddO : Odd O := ((hz.mul (hz.add_even evenR)).mul (hz.sub_even evenR)).mul
    (hz.sub_even ⟨r, by ring⟩)
  obtain ⟨b,hb⟩ := oddO
  have cop : IsCoprime (2:ℤ) O := ⟨-b,1, by linarith⟩
  have ep : 4*r^2 = (2:ℤ)^(2+(k+1)*2) := by rw [pow_add,pow_mul]; norm_num [r]
  rw [ep] at reduced ⊢
  exact (cop.pow_left).dvd_of_dvd_mul_left reduced

/-- Any odd integer on a lane can be replaced, without changing the dyadic
residue, by an integer coprime to 30 on the same lane. -/
theorem from_unit_lane {w : Weights} {N D R u x : ℤ} (cop : IsCoprime D 15) (sub : R∣D)
    (valid : ∀ y : ℤ, y ≡ u [ZMOD R] → IsCoprime y 30 → D ∣ value w N y)
    (odd : Odd x) (lane : x ≡ u [ZMOD R]) : D ∣ value w N x := by
  obtain ⟨a,b,bez⟩ := cop
  obtain ⟨j,jx⟩ := odd
  let y := x+D*a*(1-x)
  have yx : y ≡ x [ZMOD D] := Int.modEq_iff_dvd.mpr ⟨-a*(1-x),by dsimp [y]; ring⟩
  have yunit : IsCoprime y 30 := by
    refine ⟨1,-(j*b),?_⟩
    dsimp [y]
    rw [jx]
    linear_combination -2*j*bez
  have d := valid y ((yx.of_dvd sub).trans lane) yunit
  have eq : value w N y ≡ value w N x [ZMOD D] := by
    unfold value
    gcongr
  exact Int.modEq_zero_iff_dvd.mp (eq.symm.trans (Int.modEq_zero_iff_dvd.mpr d))

/-- A check on four translated coefficients can also rule out every single
root outside the specified lane. T is half the lane radix and C is the
power of two dividing the leading coefficient (an odd multiple of C). -/
theorem single_root_lane (e : ℕ) {a₀ a₁ a₂ a₃ c C D : ℤ} (nonzero : C≠0) (lead : Odd c) :
    let T : ℤ := 2^e
    2*C*T^4 ∣ D → 2*C*T^4 ∣ a₀ → 2*C*T^3 ∣ a₁ →
    2*C*T^2 ∣ a₂ → 2*C*T ∣ a₃ →
    ∀ h : ℤ, D ∣ a₀+a₁*h+a₂*h^2+a₃*h^3+C*c*h^4 → (2:ℤ)^(e+1) ∣ h := by
  intro T dM d₀ d₁ d₂ d₃ h root
  obtain ⟨b₀,h₀⟩ := d₀
  obtain ⟨b₁,h₁⟩ := d₁
  obtain ⟨b₂,h₂⟩ := d₂
  obtain ⟨b₃,h₃⟩ := d₃
  have layers (t : ℕ) (bound : t≤e+1) : (2:ℤ)^t ∣ h := by
    induction t with
    | zero => simp
    | succ t ih =>
      obtain ⟨z,hz⟩ := ih (by omega)
      rcases Int.even_or_odd z with ⟨q,hq⟩|odd
      · exact ⟨q,by rw [hz,hq,pow_succ];ring⟩
      · exfalso
        obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show t≤e by omega)
        let H : ℤ := 2^t
        let K : ℤ := 2^k
        have fact : T=H*K := by dsimp [T,H,K];rw [hk,pow_add]
        have hh : h=H*z := hz
        let L := K^4*b₀+K^3*b₁*z+K^2*b₂*z^2+K*b₃*z^3
        have expanded : a₀+a₁*h+a₂*h^2+a₃*h^3+C*c*h^4 = C*H^4*(2*L+c*z^4) := by
          rw [h₀,h₁,h₂,h₃,hh,fact]
          dsimp [L]
          ring
        have small : (C*H^4)*2 ∣ 2*C*T^4 := ⟨K^4,by rw [fact];ring⟩
        have even := small.trans (dM.trans root)
        rw [expanded] at even
        have nonzeroH : C*H^4≠0 := by dsimp [H];positivity
        obtain ⟨s,hs⟩ := (mul_dvd_mul_iff_left nonzeroH).mp even
        obtain ⟨b,hb⟩ := lead.mul (odd.pow : Odd (z^4))
        omega
  exact layers _ le_rfl

/-- Five consecutive evaluations give the exact whole-lane criterion for a quartic. -/
theorem grid_iff (w : Weights) (N u R M : ℤ) :
    (∀ i : ℕ, i≤4 → M∣value w N (u+R*i)) ↔
    (∀ k : ℤ, M∣value w N (u+R*k)) := by
  constructor
  · intro grid
    have bound : (polynomial w N).natDegree ≤ 4 := by unfold polynomial; compute_degree
    have checks (i : ℕ) (hi : i≤4) : M ∣ (polynomial w N).eval (u+R*i) := by
      rw [eval_polynomial]
      exact grid i hi
    intro k
    simpa only [eval_polynomial] using DifferenceLane.finite_grid_dvd M u R _ bound checks k
  · intro full i _
    exact full i

/-- An upper bound on the number K of residues in the common parent class,
together with pair divisibility, bounds the magnitude of the leading term. -/
theorem leading_size {c K r : ℤ} (hc : c≠0) (nK : 0≤K) (cap : K≤r)
    (div : 4*r^2 ∣ c) : 4*K^2 ≤ |c| := by
  obtain ⟨q,eq⟩ := div
  have nq : q≠0 := by intro z; simp [eq,z] at hc
  have aq : 1≤|q| := by have := abs_pos.mpr nq; omega
  have nr : 0≤4*r^2 := by positivity
  rw [eq,abs_mul,abs_of_nonneg nr]
  calc 4*K^2 ≤ 4*r^2 := by gcongr
       _ ≤ 4*r^2*|q| := le_mul_of_one_le_right nr aq

/-- In the centered projected basis the leading coefficient is v₃+v₄. -/
theorem centered_leading_cost (v₃ v₄ : ℤ) {A B : ℤ} (ha : 0≤A) (hb : 0≤B) :
    min A B * |v₃+v₄| ≤ A*|v₃|+B*|v₄| := by
  calc min A B * |v₃+v₄| ≤ min A B*(|v₃|+|v₄|) :=
         mul_le_mul_of_nonneg_left (abs_add_le ..) (le_min ha hb)
       _ ≤ _ := by rw [mul_add]; gcongr <;> simp

/-- A sharp example for every separation. Two consecutive linear factors
in the matching lane give an even product; the other lane contributes H². -/
def witness (u H r z x : ℤ) : ℤ :=
  4*r^2*(x-u)*(x-u-H*r)*(x-u-H*z)*(x-u-H*z-H*r)

theorem witness_on_lanes (u H r z k : ℤ) :
    8*(H*r)^4 ∣ witness u H r z (u+H*r*k) ∧
    8*(H*r)^4 ∣ witness u H r z (u+H*z+H*r*k) := by
  have par : 2 ∣ k*(k-1) := by
    rcases Int.even_or_odd k with ⟨s,hs⟩|⟨s,hs⟩
    · exact ⟨s*(k-1), by rw [hs]; ring⟩
    · exact ⟨k*s, by rw [hs]; ring⟩
  obtain ⟨s,hs⟩ := par
  constructor
  · refine ⟨s*(r*k-z)*(r*k-z-r),?_⟩
    unfold witness
    linear_combination 4*H^4*r^4*(r*k-z)*(r*k-z-r)*hs
  · refine ⟨s*(z+r*k)*(z+r*k-r),?_⟩
    unfold witness
    linear_combination 4*H^4*r^4*(z+r*k)*(z+r*k-r)*hs

/-- The recorded polynomial for 96577 has an entire second center at 23.
These two centers form one reciprocal orbit. -/
theorem small_reciprocal_example :
    let w : Weights := ⟨-2880,-2880,304,304,-63185120⟩
    (∀ k : ℤ, 8*32^4 ∣ value w 96577 (7+32*k)) ∧
    (∀ k : ℤ, 8*32^4 ∣ value w 96577 (23+32*k)) ∧
    (7:ℤ)*23 ≡ 96577 [ZMOD 32] := by
  intro w
  have lift (u : ℤ) (points : ∀ i : Fin 5, 8*32^4 ∣ value w 96577 (u+32*(i.val:ℤ))) :
      ∀ k : ℤ, 8*32^4 ∣ value w 96577 (u+32*k) := by
    apply (grid_iff ..).mp
    intro i hi
    exact points ⟨i,by omega⟩
  exact ⟨lift 7 (by decide +kernel),lift 23 (by decide +kernel),by decide +kernel⟩

end PrimeFactors.QuarticLaneReuse
