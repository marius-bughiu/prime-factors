import PrimeFactors.QuarticDivisorWindow

namespace PrimeFactors.QuarticIntervalExtension


open QuarticFactorLane QuarticDivisorWindow

/-- Ascending quartic coefficients, including degenerate lower degrees. -/
noncomputable def eval (v : Fin 5 → ℤ) (x : ℤ) : ℤ :=
  v 0 + v 1*x + v 2*x^2 + v 3*x^3 + v 4*x^4

/-- Scaled Taylor coefficients at l with width u-l. -/
noncomputable def shifted (v : Fin 5 → ℤ) (l u : ℤ) : Fin 5 → ℤ :=
  let w := u-l
  ![eval v l, w*(v 1+2*v 2*l+3*v 3*l^2+4*v 4*l^3),
    w^2*(v 2+3*v 3*l+6*v 4*l^2),w^3*(v 3+4*v 4*l),w^4*v 4]

/-- Coefficients of the homogenized quartic in x-l and u-x. No division
or rounding is required, even on intervals with negative endpoints. -/
noncomputable def bernstein (v : Fin 5 → ℤ) (l u : ℤ) : Fin 5 → ℤ :=
  let h := shifted v l u
  ![h 0,4*h 0+h 1,6*h 0+3*h 1+h 2,4*h 0+3*h 1+2*h 2+h 3,
    h 0+h 1+h 2+h 3+h 4]

private theorem homogeneous (v : Fin 5 → ℤ) (l u x : ℤ) :
    let k := bernstein v l u
    (u-l)^4*eval v x =
      k 0*(u-x)^4+k 1*(x-l)*(u-x)^3+k 2*(x-l)^2*(u-x)^2+
      k 3*(x-l)^3*(u-x)+k 4*(x-l)^4 := by
  simp [bernstein,shifted,eval]
  ring

/-- Positive homogeneous coefficients certify strict positivity throughout
the closed block. The constant term suffices for a singleton. -/
theorem eval_positive {v : Fin 5 → ℤ} {l u x : ℤ}
    (good : ∀ i, 0 < bernstein v l u i) (lx : l≤x) (xu : x≤u) : 0<eval v x := by
  rcases eq_or_lt_of_le (lx.trans xu) with same|wide
  · obtain rfl : l=x := by omega
    exact good 0
  let k := bernstein v l u
  have z : 0≤x-l := by omega
  have y : 0≤u-x := by omega
  have b0 := good 0
  have b1 := good 1
  have b2 := good 2
  have b3 := good 3
  have b4 := good 4
  have equation := homogeneous v l u x
  change (u-l)^4*eval v x =
    k 0*(u-x)^4+k 1*(x-l)*(u-x)^3+k 2*(x-l)^2*(u-x)^2+
    k 3*(x-l)^3*(u-x)+k 4*(x-l)^4 at equation
  have parts : 0 ≤ k 1*(x-l)*(u-x)^3+k 2*(x-l)^2*(u-x)^2+k 3*(x-l)^3*(u-x) := by
    dsimp [k]; positivity
  have positive : 0<(u-l)^4*eval v x := by
    rw [equation]
    by_cases right : x=u
    · have xp : 0<x-l := by omega
      have h4 : 0<k 4*(x-l)^4 := mul_pos b4 (pow_pos xp _)
      linarith only [parts,h4,show 0≤k 0*(u-x)^4 from mul_nonneg b0.le (by positivity)]
    · have up : 0<u-x := by omega
      have h0 : 0<k 0*(u-x)^4 := mul_pos b0 (pow_pos up _)
      linarith only [parts,h0,show 0≤k 4*(x-l)^4 from mul_nonneg b4.le (by positivity)]
  exact pos_of_mul_pos_right positive (by positivity)

/-- Coefficients of (c+s*x)² + sign*F(x). -/
noncomputable def margin (v : Fin 5 → ℤ) (c s sign : ℤ) : Fin 5 → ℤ :=
  ![c^2+sign*v 0,2*c*s+sign*v 1,s^2+sign*v 2,sign*v 3,sign*v 4]

theorem eval_margin (v : Fin 5 → ℤ) (c s sign x : ℤ) :
    eval (margin v c s sign) x = (c+s*x)^2+sign*value (weights v) 1 x := by
  simp [margin,eval,weights,value]; ring

noncomputable def block (v : Fin 5 → ℤ) (c s l u : ℤ) : Bool :=
  decide (∀ i, 0 < bernstein (margin v c s 1) l u i) &&
  decide (∀ i, 0 < bernstein (margin v c s (-1)) l u i)

theorem block_bound {v : Fin 5 → ℤ} {c s l u x : ℤ} (cert : block v c s l u=true)
    (lx : l≤x) (xu : x≤u) : |value (weights v) 1 x| < (c+s*x)^2 := by
  simp only [block,Bool.and_eq_true,decide_eq_true_eq] at cert
  have low := eval_positive cert.1 lx xu
  have high := eval_positive cert.2 lx xu
  rw [eval_margin] at low high
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

/-- Inclusive upper endpoints of all but the last block. A cut moves the
next block to the next integer, allowing very wide intervals and short lists. -/
noncomputable def covered (v : Fin 5 → ℤ) (c s l u : ℤ) : List ℤ → Bool
  | [] => block v c s l u
  | e::es => decide (l≤e ∧ e<u) && block v c s l e && covered v c s (e+1) u es

theorem covered_bound {v : Fin 5 → ℤ} {c s l u x : ℤ} {cuts : List ℤ}
    (cert : covered v c s l u cuts=true) (lx : l≤x) (xu : x≤u) :
    |value (weights v) 1 x| < (c+s*x)^2 := by
  induction cuts generalizing l with
  | nil => exact block_bound cert lx xu
  | cons e es ih =>
    simp only [covered,Bool.and_eq_true,decide_eq_true_eq] at cert
    by_cases early : x≤e
    · exact block_bound cert.1.2 lx early
    · exact ih cert.2 (by omega)

/-- Checking the two neighboring offsets proves maximality of this connected
integer interval for this particular magnitude test. Other rows or separated
components can cover more offsets. -/
theorem maximal_component {v : Fin 5 → ℤ} {c s l u : ℤ} {cuts : List ℤ}
    (ordered : l≤u) (cert : covered v c s l u cuts=true)
    (prev : (c+s*(l-1))^2 ≤ |value (weights v) 1 (l-1)|)
    (next : (c+s*(u+1))^2 ≤ |value (weights v) 1 (u+1)|) :
    (∀ x, l≤x → x≤u → |value (weights v) 1 x| < (c+s*x)^2) ∧
    ∀ a b : ℤ, a≤l → u≤b → (∀ x, a≤x → x≤b → |value (weights v) 1 x| < (c+s*x)^2) →
      a=l ∧ b=u := by
  refine ⟨fun _ => covered_bound cert,?_⟩
  intro a b al ub all
  constructor
  · by_contra! neq
    exact (not_lt_of_ge prev) (all (l-1) (by omega) (by omega))
  · by_contra! neq
    exact (not_lt_of_ge next) (all (u+1) (by omega) (by omega))

/-- Natural endpoint exclusion for a product and an odd center. Each sub-block
can use the identical polynomial and the same modular absence-of-root witness. -/
theorem odd_interval_excludes {v : Fin 5 → ℤ} {n c L U m : ℕ} {t l u : ℤ} {cuts : List ℤ}
    (hn : n%2=1) (hc : c%2=1) (anchor : (n:ℤ) ∣ (c:ℤ)+2*t)
    (hj : jets v n t) (cert : covered v c 2 l u cuts=true)
    (left : (c:ℤ)+2*l≤L) (right : (U:ℤ)≤c+2*u)
    (hm : 0<m) (miss : misses v m=true)
    (d : ℕ) (lo : L≤d) (hi : d≤U) : ¬d∣n := by
  intro hd
  have odd := Nat.odd_iff.mpr hn
  have unit : IsCoprime (2:ℤ) (n:ℤ) := by exact_mod_cast (Nat.coprime_two_left.mpr odd).isCoprime
  obtain ⟨q,hq⟩ := hd
  obtain ⟨k,hk⟩ := (Nat.odd_mul.mp (hq ▸ odd)).1
  have dz : (d:ℤ) ∣ (n:ℤ) := by exact_mod_cast (show d∣n from ⟨q,hq⟩)
  let x := ((d:ℤ)-c)/2
  have pos : (d:ℤ)=(c:ℤ)+2*x := by dsimp [x]; omega
  have h := covered_bound (x:=x) cert (by omega) (by omega)
  rw [←pos] at h
  have dv := square_divides hj dz (progression_offset unit anchor dz pos)
  exact no_root hm miss x (Int.eq_zero_of_abs_lt_dvd dv h)

end PrimeFactors.QuarticIntervalExtension
