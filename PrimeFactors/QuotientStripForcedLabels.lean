import PrimeFactors.QuotientStripWideSlopeLabels
import PrimeFactors.QuotientStripSlopePopulation
import PrimeFactors.QuotientStripLevelMod24

/-!
# Integer labels forced by a stationary band

On the selected bands every primitive approximation accepted by the search
has the same direction. Each witness lies inside the signed integer bounds
of the implementation, has positive discriminant, and passes the full local
modulo-24 test. These predicates allow counting the actual surviving blocks.
-/

namespace PrimeFactors.QuotientStripForcedLabels

open QuotientStripWideSlopeGeometry QuotientStripWideSlopeGeometry.Band
set_option exponentiation.threshold 4096

/-- Direction contract of the full-width chord selector, with Q=r−1. -/
def Certified (n r a b : ℕ) (d : ℕ×ℕ) : Prop :=
  d.1.Coprime d.2 ∧ 0<d.2 ∧ d.2<r ∧
    |(d.1:ℝ)-d.2*((n:ℝ)/(a*b))| ≤ 1/(r:ℝ)

/-- Any primitive direction satisfying the public certificate. Uniqueness
on the counted blocks makes the result independent of tie choices. -/
noncomputable def assigned (n r a b : ℕ) : ℕ×ℕ :=
  Classical.epsilon (Certified n r a b)

/-- A subset of the actual surviving labels, using the admissible local pair
(1,N) and positive discriminants below the chosen range for the label. -/
def Survives (n a b : ℕ) (d : ℕ×ℕ) (z : ℤ) : Prop :=
  0≤z ∧ z<(n:ℤ) ∧ z ≡ (d.1:ℤ)+n*d.2 [ZMOD 24] ∧
  0<z^2-4*((d.1*d.2:ℕ):ℤ)*n ∧
  Rounded.labelLow n a b d.1 d.2 ≤ z ∧ z ≤ Rounded.labelHigh n a b d.1 d.2

theorem local_pair {n a b : ℕ} {d : ℕ×ℕ} {z : ℤ} (h : Survives n a b d z) :
    ∃ x y : ZMod 24, x*y=n ∧ (d.1:ZMod 24)*x+d.2*y=z := by
  refine ⟨1,n,one_mul _,?_⟩
  have eqn := (ZMod.intCast_eq_intCast_iff _ _ (24:ℕ)).mpr h.2.2.1
  push_cast at eqn
  rw [mul_one, mul_comm (d.2:ZMod 24)]
  exact eqn.symm

theorem forced {n r a b : ℕ} {d : ℕ×ℕ} {t L : ℝ}
    (G : Band (Real.sqrt n) r d.1 d.2 t L) (cop : d.1.Coprime d.2)
    (low : t-L≤a) (full : (b:ℝ)-a=2*r-1) (high : (b:ℝ)≤t) :
    assigned n r a b=d := by
  have sqN := Real.sq_sqrt (by positivity : (0:ℝ)≤n)
  obtain ⟨pos,cap,fit⟩ := G.own_certificate low full high
  rw [sqN] at fit
  have vc : d.2+1≤r := by exact_mod_cast (by linarith only [cap] : (d.2:ℝ)+1≤r)
  have cand : Certified n r a b d := ⟨cop, by exact_mod_cast pos, by omega, fit⟩
  obtain ⟨pr,qp,qs,good⟩ := (Classical.epsilon_spec (p:=Certified n r a b) ⟨d,cand⟩)
  rw [← sqN] at good
  have out := G.selected low (by linarith [G.rp] : (a:ℝ)≤b) high cop pr qp
    (by exact_mod_cast qs.le) good
  exact Prod.ext out.1 out.2

theorem integer_label {n r a b : ℕ} {d : ℕ×ℕ} {t L : ℝ} {z : ℤ}
    (G : Band (Real.sqrt n) r d.1 d.2 t L)
    (slo : 2^1023 ≤ Real.sqrt (n:ℝ)) (uc : d.1≤9*2^327) (vc : d.2≤7*2^327)
    (low : t-L≤a) (full : (b:ℝ)-a=2*r-1) (high : (b:ℝ)≤t)
    (res : z ≡ (d.1:ℤ)+n*d.2 [ZMOD 24])
    (disc : 0<(z:ℝ)^2-4*d.1*d.2*(Real.sqrt n)^2)
    (below : F (Real.sqrt n) d.1 d.2 b-pad (Real.sqrt n) d.2 a b≤z)
    (above : (z:ℝ)≤F (Real.sqrt n) d.1 d.2 a) : Survives n a b d z := by
  have sqN := Real.sq_sqrt (by positivity : (0:ℝ)≤n)
  obtain ⟨zl,zh⟩ := G.label_bounds slo (by exact_mod_cast uc) (by exact_mod_cast vc)
    low full high below above
  rw [sqN] at zh disc
  have ap := (G.slope_at low (by linarith [G.rp] : (a:ℝ)≤t)).1
  have bp : (0:ℝ)<b := by linarith [G.rp]
  have rounded := (Rounded.endpoints_iff (N:=(n:ℤ)) (a:=(a:ℤ)) (b:=(b:ℤ))
    (u:=(d.1:ℤ)) (v:=(d.2:ℤ)) (z:=z) (by exact_mod_cast sqN)
    (by exact_mod_cast ap) (by exact_mod_cast bp)).mpr
  push_cast at rounded
  have fl := (G.block_width low full high).1
  rw [min_eq_right fl,max_eq_left fl] at rounded
  refine ⟨by exact_mod_cast zl,by exact_mod_cast zh,res,?_,rounded ⟨below,above⟩⟩
  push_cast
  exact_mod_cast (by linarith only [disc] : 0<(z:ℝ)^2-4*((d.1:ℝ)*d.2)*n)

end PrimeFactors.QuotientStripForcedLabels
