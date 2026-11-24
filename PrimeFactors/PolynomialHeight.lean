import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace PrimeFactors.PolynomialHeight

/-- At a normalized site t = x+B/A, the condition means that the absolute
value of the reduced integer polynomial is at most H. -/
def Fits (A N H t : ℝ) : Prop :=
  N ≤ A^2*t^2+A*H ∧ A^2*t^2 ≤ N+A*H

theorem fits_iff {A N H B x : ℝ} (a : 0<A) :
    Fits A N H (x+B/A) ↔ |((A*x+B)^2-N)/A| ≤ H := by
  have ident : A^2*(x+B/A)^2=(A*x+B)^2 := by field_simp; ring
  rw [abs_div, abs_of_pos a, div_le_iff₀ a, abs_le]
  unfold Fits
  rw [ident]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

private theorem fits_neg {A N H x : ℝ} (h : Fits A N H x) : Fits A N H (-x) := by
  simpa [Fits] using h

/-- Two same-sign sites with inner distance at least c from the vertex and
separation at least d force the indicated height, irrespective of A. -/
theorem branch {A N H c d t y : ℝ} (a : 0<A) (n : 0<N) (h : 0≤H)
    (hc : 0≤c) (hd : 0<d) (start : c≤t) (span : t+d≤y)
    (first : Fits A N H t) (last : Fits A N H y) :
    N*(d*(2*c+d))^2 ≤ 2*H^2*((c+d)^2+c^2) := by
  have ht := hc.trans start
  let delta := d*(2*t+d)
  have dp : 0 < delta := mul_pos hd (by linarith)
  have monotone : (t+d)^2 ≤ y^2 := by
    apply pow_le_pow_left₀ (by linarith) span
  have next := (mul_le_mul_of_nonneg_left monotone (sq_nonneg A)).trans last.2
  have bound : A*delta ≤ 2*H := by
    apply le_of_mul_le_mul_left (a := A) _ a
    dsimp [delta]
    nlinarith [first.1, next]
  have ad : 0 ≤ A*delta := (mul_pos a dp).le
  have sqbound : (A*delta)^2 ≤ (2*H)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr bound) (show 0≤2*H+A*delta by linarith)]
  have step : N*delta^2 ≤ 2*H^2*((t+d)^2+t^2) := by
    calc
      _ ≤ (A^2*t^2+A*H)*delta^2 := mul_le_mul_of_nonneg_right first.1 (sq_nonneg _)
      _ = (A*delta)^2*t^2 + H*delta*(A*delta) := by ring
      _ ≤ (2*H)^2*t^2 + H*delta*(2*H) :=
        add_le_add (mul_le_mul_of_nonneg_right sqbound (sq_nonneg t))
          (mul_le_mul_of_nonneg_left bound (mul_nonneg h dp.le))
      _ = _ := by dsimp [delta]; ring
  have compare : (d*(2*c+d))^2*((t+d)^2+t^2) ≤ delta^2*((c+d)^2+c^2) := by
    have iden : delta^2*((c+d)^2+c^2) - (d*(2*c+d))^2*((t+d)^2+t^2) =
        2*d^4*(t-c)*(t+c+d) := by dsimp [delta]; ring
    nlinarith [mul_nonneg (mul_nonneg (show 0≤2*d^4 by positivity) (sub_nonneg.mpr start))
      (show 0≤t+c+d by linarith)]
  have den : 0 < (t+d)^2+t^2 := by positivity
  apply le_of_mul_le_mul_right (a := (t+d)^2+t^2) _ den
  calc
    _ = N*((d*(2*c+d))^2*((t+d)^2+t^2)) := by ring
    _ ≤ N*(delta^2*((c+d)^2+c^2)) := mul_le_mul_of_nonneg_left compare n.le
    _ = (N*delta^2)*((c+d)^2+c^2) := by ring
    _ ≤ (2*H^2*((t+d)^2+t^2))*((c+d)^2+c^2) :=
      mul_le_mul_of_nonneg_right step (by positivity)
    _ = _ := by ring

/-- The middle selected position on 2m+1 integer sites has at least distance
m from each endpoint. This applies even when the selected sites have gaps. -/
theorem odd_spaced {A N H m x y z : ℝ} (a : 0<A) (n : 0<N) (h : 0≤H) (hm : 0<m)
    (xy : x+m≤y) (yz : y+m≤z) (fx : Fits A N H x) (fy : Fits A N H y)
    (fz : Fits A N H z) : N*m^2 ≤ 2*H^2 := by
  have b : N*(m*(2*0+m))^2 ≤ 2*H^2*((0+m)^2+(0:ℝ)^2) := by
    by_cases sy : 0≤y
    · exact branch a n h le_rfl hm sy yz fy fz
    · exact branch a n h le_rfl hm (by linarith : 0 ≤ -y)
        (by linarith : -y+m≤ -x) (fits_neg fy) (fits_neg fx)
  apply le_of_mul_le_mul_right (a:=m^2) _ (sq_pos_of_pos hm)
  nlinarith [b]

/-- On 2(d+1) integer sites the two middle sites are at least one apart.
One of the two outward branches therefore starts at distance at least 1/2. -/
theorem even_spaced {A N H d x y z w : ℝ} (a : 0<A) (n : 0<N) (h : 0≤H) (hd : 0<d)
    (xy : x+d≤y) (yz : y+1≤z) (zw : z+d≤w) (fx : Fits A N H x)
    (fy : Fits A N H y) (fz : Fits A N H z) (fw : Fits A N H w) :
    N*(d*(d+1))^2 ≤ H^2*(2*d^2+2*d+1) := by
  have b : N*(d*(2*(1/2)+d))^2 ≤ 2*H^2*(((1/2)+d)^2+(1/2:ℝ)^2) := by
    by_cases sz : 1/2≤z
    · exact branch a n h (by norm_num) hd sz zw fz fw
    · exact branch a n h (by norm_num) hd (by linarith : 1/2 ≤ -y)
        (by linarith : -y+d ≤ -x) (fits_neg fy) (fits_neg fx)
  nlinarith
/-- On a centered grid the endpoint and the nearest point to the vertex have
opposite, equal heights. The same bound covers all the sites in between. -/
theorem balanced_grid {A N r c x : ℝ} (balanced : A^2*(r^2+c^2)=2*N)
    (lower : c^2≤x^2) (upper : x^2≤r^2) :
    Fits A N (A*(r^2-c^2)/2) x ∧
    A^2*c^2-N = -A*(A*(r^2-c^2)/2) ∧
    A^2*r^2-N = A*(A*(r^2-c^2)/2) := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left lower (sq_nonneg A)]
  · nlinarith [mul_le_mul_of_nonneg_left upper (sq_nonneg A)]
  · nlinarith
  · nlinarith

/-- The positive leading coefficient for the sharp real relaxation always exists. -/
theorem balanced_coefficient {N r c : ℝ} (n : 0<N) (rp : 0<r) :
    ∃ A : ℝ, 0<A ∧ A^2*(r^2+c^2)=2*N := by
  have den : 0<r^2+c^2 := by positivity
  refine ⟨Real.sqrt (2*N/(r^2+c^2)),Real.sqrt_pos.mpr (by positivity),?_⟩
  rw [Real.sq_sqrt (by positivity),div_mul_cancel₀ _ den.ne']

private theorem site_gap (z : ℕ → ℤ) (mon : StrictMono z) (i j : ℕ) :
    z i+j ≤ z (i+j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have step : z (i+j)<z ((i+j)+1) := mon (by omega)
    rw [Nat.cast_succ]
    change z i+((j:ℤ)+1) ≤ z ((i+j)+1)
    omega

/-- Among any 2m+1 chosen integer offsets, some reduced norm is at least
m sqrt(N/2) in absolute value. No bound on their total span is needed. -/
theorem odd_sites {A N H B : ℝ} (a : 0<A) (n : 0<N) (h : 0≤H)
    (z : ℕ → ℤ) (mon : StrictMono z) {m : ℕ} (mp : 0<m)
    (rows : ∀ i ≤ 2*m, |((A*(z i : ℝ)+B)^2-N)/A|≤H) :
    N*(m : ℝ)^2≤2*H^2 := by
  have one : z 0+(m : ℤ)≤z m := by simpa using site_gap z mon 0 m
  have two : z m+(m : ℤ)≤z (2*m) := by simpa [two_mul] using site_gap z mon m m
  have gap₁ : (z 0 : ℝ)+m≤z m := by exact_mod_cast one
  have gap₂ : (z m : ℝ)+m≤z (2*m) := by exact_mod_cast two
  exact odd_spaced a n h (by exact_mod_cast mp)
    (x:=(z 0 : ℝ)+B/A) (y:=(z m : ℝ)+B/A) (z:=(z (2*m) : ℝ)+B/A)
    (by linarith) (by linarith) ((fits_iff a).mpr (rows _ (by omega)))
    ((fits_iff a).mpr (rows _ (by omega))) ((fits_iff a).mpr (rows _ le_rfl))

/-- For 2(d+1) chosen integer sites the discrete parity correction is sharp. -/
theorem even_sites {A N H B : ℝ} (a : 0<A) (n : 0<N) (h : 0≤H)
    (z : ℕ → ℤ) (mon : StrictMono z) {d : ℕ} (dp : 0<d)
    (rows : ∀ i ≤ 2*d+1, |((A*(z i : ℝ)+B)^2-N)/A|≤H) :
    N*((d : ℝ)*(d+1))^2≤H^2*(2*(d : ℝ)^2+2*d+1) := by
  have one : z 0+(d : ℤ)≤z d := by simpa using site_gap z mon 0 d
  have two : z d < z (d+1) := mon (by omega)
  have three : z (d+1)+(d : ℤ)≤z (2*d+1) := by
    convert site_gap z mon (d+1) d using 2
    omega
  have gap₁ : (z 0 : ℝ)+d≤z d := by exact_mod_cast one
  have gap₂ : (z d : ℝ)+1≤z (d+1) := by exact_mod_cast (show z d+1≤z (d+1) by omega)
  have gap₃ : (z (d+1) : ℝ)+d≤z (2*d+1) := by exact_mod_cast three
  exact even_spaced a n h (by exact_mod_cast dp)
    (x:=(z 0 : ℝ)+B/A) (y:=(z d : ℝ)+B/A) (z:=(z (d+1) : ℝ)+B/A) (w:=(z (2*d+1) : ℝ)+B/A)
    (by linarith) (by linarith) (by linarith) ((fits_iff a).mpr (rows _ (by omega)))
    ((fits_iff a).mpr (rows _ (by omega))) ((fits_iff a).mpr (rows _ (by omega)))
    ((fits_iff a).mpr (rows _ le_rfl))

end PrimeFactors.PolynomialHeight
