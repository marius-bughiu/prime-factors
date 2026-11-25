import PrimeFactors.CenteredSumQuartic
import PrimeFactors.ProjectedQuarticLevels
import PrimeFactors.LevelMaskCertificate

namespace PrimeFactors.ProjectedLevelCertificate
open QuarticFactorLane

noncomputable def zeroWeights : Weights := ⟨0,0,0,0,0⟩

/-- A public trace lift whose twelve labels vanish has a multiple of the
modulus as its trace at every factor pair on its unit residue lane. -/
theorem level_exists {R : ℕ} {N x y u : ℤ} {w : Weights}
    (pair : x*y=N) (unit : IsCoprime (360*(R:ℤ)^4) N)
    (cop : IsCoprime (8*(R:ℤ)^4) 45)
    (same : QuarticUnitLabels.label R u N w = QuarticUnitLabels.label R u N zeroWeights)
    (lane : x ≡ u [ZMOD (R:ℤ)]) :
    ∃ j : ℤ, trace w x y = (360*(R:ℤ)^4)*j := by
  have cx := (show IsCoprime (360*(R:ℤ)^4) (x*y) from pair.symm ▸ unit).of_mul_right_left
  have small := cx.symm.of_isCoprime_of_dvd_right (show (30:ℤ)∣360*(R:ℤ)^4 from
    ⟨12*(R:ℤ)^4, by ring⟩)
  have div := QuarticUnitLabels.divides_of_label_eq_at cop same lane small
  rw [show value zeroWeights N x = 0 by simp [value, zeroWeights], sub_zero,
    pair_identity w pair] at div
  exact cx.pow_right.dvd_of_dvd_mul_left div

/-- The projected spread omits the constant term of the centered sum basis. -/
theorem centered_spread (v : Fin 5 → ℤ) {x y N h c : ℤ} {s B : ℕ}
    (pair : x*y=N) (tx : |x+y-h| ≤ 2*(s:ℤ)) (zx : |x-c| ≤ B) :
    |trace (CenteredSumQuartic.coordinates N h c s v) x y-v 0| ≤
      ∑ i, |ProjectedQuarticLevels.withoutConstant v i| * (UnitQuarticBox.weight s B i:ℤ) := by
  let v' := ProjectedQuarticLevels.withoutConstant v
  have eq : trace (CenteredSumQuartic.coordinates N h c s v') x y =
      trace (CenteredSumQuartic.coordinates N h c s v) x y-v 0 := by
    simp [v', ProjectedQuarticLevels.withoutConstant, CenteredSumQuartic.coordinates, trace]
    ring
  rw [← eq, CenteredSumQuartic.trace_eq pair]
  apply UnitQuarticRecovery.terms_bound _ _ zx
  rwa [show x-c-(h-c-y)=x+y-h by ring]

/-- Recover the centered coefficients from the recorded five Laurent coefficients. -/
noncomputable def centeredLift (N h c s : ℤ) (w : Weights) : Fin 5 → ℤ :=
  let v₄ := w.c-w.d
  let v₁ := w.b+2*h*w.d+c*v₄
  let v₂ := w.a-v₁+2*h*w.d+(h+c)*v₄
  ![w.e+h*v₁+c*v₂-(2*N+h^2-2*s^2)*w.d-(N+c*h)*v₄, v₁, v₂, w.d, v₄]

theorem lift_reconstruct (N h c s : ℤ) (w : Weights) :
    CenteredSumQuartic.coordinates N h c s (centeredLift N h c s w) = w := by
  cases w
  simp [CenteredSumQuartic.coordinates,centeredLift]
  refine ⟨?_,?_,?_⟩ <;> ring

noncomputable def spread (v : Fin 5 → ℤ) (s B : ℕ) : ℤ :=
  |v 1| * (2*s) + |v 2| * B + |v 3| * (2*(s:ℤ)^2) + |v 4| * (2*(s:ℤ)*B)

theorem spread_eq (v : Fin 5 → ℤ) (s B : ℕ) :
    (∑ i, |ProjectedQuarticLevels.withoutConstant v i| * (UnitQuarticBox.weight s B i:ℤ)) =
      spread v s B := by
  simp [ProjectedQuarticLevels.withoutConstant,UnitQuarticBox.weight,spread,Fin.sum_univ_succ]
  ring

/-- A bounded Euclidean computation proposes a Bézout coefficient. Its caller
independently checks the multiplicative inverse, including on fuel exhaustion. -/
private noncomputable def inverseLoop : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ
  | 0, _, _, a, _ => a
  | fuel+1, l, r, a, b =>
    if r=0 then a else inverseLoop fuel r (l%r) b (a-((l/r:ℕ):ℤ)*b)

/-- For every nonzero factor residue, verify an explicit inverse of the
multiplier and check that its forced level residue belongs to the mask.
The inverse check itself suffices, without assuming the modulus is prime. -/
noncomputable def maskCovers (p mask : ℕ) (a₀ a₁ a₂ a₃ a₄ m : ℤ) : Bool :=
  (List.range p).all fun z =>
    let z' : ℤ := z
    let lhs := ((((a₄*z'+a₃)*z'+a₂)*z'+a₁)*z'+a₀) % p
    let multiplier := m*z'^2 % p
    let inv := inverseLoop p multiplier.toNat p 1 0
    z == 0 || decide (multiplier*inv ≡ 1 [ZMOD (p:ℤ)]) &&
      mask.testBit ((lhs*inv)%p).toNat

/-- Reduce the five coefficients once per row before the finite mask check. -/
structure Row where
  p : ℕ
  mask : ℕ
  n : ℤ
  a₀ : ℤ
  a₁ : ℤ
  a₂ : ℤ
  a₃ : ℤ
  a₄ : ℤ
  m : ℤ
  deriving DecidableEq

noncomputable def reducedRow (w : Weights) (N M : ℤ) (row : ℕ × ℕ) : Row :=
  let p : ℤ := row.1
  ⟨row.1,row.2,N%p,w.d*N^2%p,w.b*N%p,w.e%p,w.a%p,w.c%p,M%p⟩

noncomputable def Row.check (r : Row) : Bool := decide (0 < (r.p:ℤ)) && decide (r.n ≠ 0) &&
  maskCovers r.p r.mask r.a₀ r.a₁ r.a₂ r.a₃ r.a₄ r.m

noncomputable def traceMask (w : Weights) (N M : ℤ) (row : ℕ × ℕ) : Bool :=
  (reducedRow w N M row).check

theorem rows_checked {w : Weights} {N M : ℤ} {rows : List (ℕ × ℕ)} {reduced : List Row}
    (actual : rows.map (reducedRow w N M) = reduced) (good : reduced.all Row.check = true) :
    rows.all (traceMask w N M) = true := by
  rw [← actual, List.all_map] at good
  exact good

theorem mask_sound {w : Weights} {x y N M j : ℤ} {row : ℕ × ℕ}
    (passed : traceMask w N M row = true) (pair : x*y=N) (level : trace w x y = M*j) :
    row.2.testBit (j % (row.1:ℤ)).toNat = true := by
  rcases row with ⟨p, mask⟩
  simp only [traceMask, reducedRow, Row.check, Bool.and_eq_true, decide_eq_true_eq] at passed
  obtain ⟨⟨hp, nonzero⟩, table⟩ := passed
  let z := (x % (p:ℤ)).toNat
  have x0 := Int.emod_nonneg x hp.ne'
  have xlt := Int.emod_lt_of_pos x hp
  have zx : (z:ℤ) = x%p := Int.toNat_of_nonneg x0
  have hz : z < p := by exact_mod_cast (zx ▸ xlt : (z:ℤ) < p)
  have xmod : (z:ℤ) ≡ x [ZMOD (p:ℤ)] := zx ▸ Int.mod_modEq x p
  have nz : z ≠ 0 := by
    intro hzero
    have xZero : x%(p:ℤ) = 0 := by simpa [hzero] using zx.symm
    exact nonzero (by rw [← pair,Int.mul_emod,xZero,zero_mul,Int.zero_emod])
  have horner := (((((Int.mod_modEq w.c p).mul xmod).add (Int.mod_modEq w.a p)).mul
    xmod).add (Int.mod_modEq w.e p)).mul xmod
  have hleft := ((horner.add (Int.mod_modEq (w.b*N) p)).mul xmod).add
    (Int.mod_modEq (w.d*N^2) p)
  let multiplier := (M%p)*(z:ℤ)^2%p
  let inv := inverseLoop p multiplier.toNat p 1 0
  let lhs := (((((w.c % (p:ℤ))*(z:ℤ)+w.a%p)*z+w.e%p)*z+w.b*N%p)*z+w.d*N^2%p)%p
  have scaleMod : multiplier ≡ M*x^2 [ZMOD (p:ℤ)] :=
    (Int.mod_modEq _ p).trans ((Int.mod_modEq M p).mul (xmod.pow 2))
  have eq : (((w.c*x+w.a)*x+w.e)*x+w.b*N)*x+w.d*N^2 = j*(M*x^2) := by
    calc _ = value w N x := by unfold value; ring
         _ = _ := by rw [pair_identity w pair, level]; ring
  have same : lhs ≡ j*multiplier [ZMOD (p:ℤ)] :=
    (Int.mod_modEq _ p).trans (hleft.trans (eq ▸ (Int.ModEq.refl j).mul scaleMod.symm))
  have atZ := (List.all_eq_true.mp table) z (List.mem_range.mpr hz)
  change (z == 0 || decide (multiplier*inv ≡ 1 [ZMOD (p:ℤ)]) &&
    mask.testBit ((lhs*inv)%p).toNat) = true at atZ
  simp only [beq_iff_eq, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, nz,
    false_or] at atZ
  obtain ⟨inverse, bit⟩ := atZ
  have final : lhs*inv ≡ j [ZMOD (p:ℤ)] := calc
    lhs*inv ≡ (j*multiplier)*inv [ZMOD (p:ℤ)] := same.mul (Int.ModEq.refl inv)
    _ = j*(multiplier*inv) := mul_assoc ..
    _ ≡ j*1 [ZMOD (p:ℤ)] := (Int.ModEq.refl j).mul inverse
    _ = j := mul_one j
  change lhs*inv%(p:ℤ) = j%(p:ℤ) at final
  rwa [final] at bit

/-- Public inputs to the centered projected trace certificate. The reported
lower factor bound and lower sum bound are independently checked by products. -/
structure Control where
  N : ℕ
  R : ℕ
  U : ℕ
  L : ℕ
  A : ℕ
  w : Weights

namespace Control
variable (t : Control)

noncomputable def M : ℤ := 360*(t.R:ℤ)^4
noncomputable def sumHigh : ℕ := t.U+t.N/t.U
noncomputable def h : ℕ := (t.A+t.sumHigh)/2
noncomputable def c : ℕ := (t.L+t.U)/2
noncomputable def s : ℕ := max 1 ((t.sumHigh-t.A+3)/4)
noncomputable def r : ℕ := max 1 ((t.U-t.L+1)/2)
noncomputable def v : Fin 5 → ℤ := centeredLift t.N t.h t.c t.s t.w

/-- Every factor pair in the promised size and residue range yields one
surviving level. A verified empty block therefore excludes the whole group. -/
theorem excludes (u lo hi : ℤ) (rows : List (ℕ × ℕ))
    (factorBounds : 0<t.U ∧ (t.L-1)*t.U<t.N)
    (sumBounds : (t.A-1)^2<4*t.N ∧ 4*t.N≤t.A^2)
    (unit : Int.gcd t.M t.N=1 ∧ Int.gcd (8*(t.R:ℤ)^4) 45=1)
    (labels : QuarticUnitLabels.label t.R u t.N t.w =
      QuarticUnitLabels.label t.R u t.N zeroWeights)
    (ends : 0<t.M ∧ -((spread t.v t.s t.r-t.v 0)/t.M)=lo ∧
      (spread t.v t.s t.r+t.v 0)/t.M=hi)
    (checked : rows.all (traceMask t.w t.N t.M) = true)
    (empty : ∀ j : ℤ, lo≤j → j≤hi →
      (∀ row ∈ rows, row.2.testBit (j%(row.1:ℤ)).toNat = true) → False)
    (x y : ℕ) (pair : x*y=t.N) (hx : x≤t.U) (hy : y≤t.U)
    (lane : (x:ℤ) ≡ u [ZMOD (t.R:ℤ)]) : False := by
  have hA : ceilSqrt (4*t.N) = t.A := by
    apply le_antisymm (ceilSqrt_le_iff.mpr sumBounds.2)
    by_contra! small
    have prev : ceilSqrt (4*t.N) ≤ t.A-1 := by omega
    exact (not_le.mpr sumBounds.1) (ceilSqrt_le_iff.mp prev)
  have hxL : t.L≤x := by
    by_contra! small
    have prod := Nat.mul_le_mul (show x≤t.L-1 by omega) hy
    exact (not_le.mpr factorBounds.2) (pair ▸ prod)
  have widths := CenteredSumQuartic.dynamic_widths pair factorBounds.1 hxL hx hy
  rw [hA] at widths
  have pairZ : (x:ℤ)*y=t.N := by exact_mod_cast pair
  have width := centered_spread t.v (h := t.h) (c := t.c) (s := t.s) (B := t.r)
    pairZ widths.1 widths.2
  rw [show CenteredSumQuartic.coordinates t.N t.h t.c t.s t.v = t.w from lift_reconstruct ..,
    spread_eq] at width
  obtain ⟨j, lev⟩ := level_exists pairZ (Int.isCoprime_iff_gcd_eq_one.mpr unit.1)
    (Int.isCoprime_iff_gcd_eq_one.mpr unit.2) labels lane
  change trace t.w x y=t.M*j at lev
  have member := (ProjectedQuarticLevels.mem_levels ends.1).mpr
    (show |j*t.M-t.v 0| ≤ spread t.v t.s t.r from by
      rw [mul_comm j t.M, ← lev]; exact width)
  obtain ⟨jl, jh⟩ := Finset.mem_Icc.mp member
  rw [ends.2.1] at jl
  rw [ends.2.2] at jh
  apply empty j jl jh
  intro row inList
  exact mask_sound (List.all_eq_true.mp checked row inList) pairZ lev

end Control
end PrimeFactors.ProjectedLevelCertificate
