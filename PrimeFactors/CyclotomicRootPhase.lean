import PrimeFactors.InverseCyclotomicMeasurements
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The phase of the scaled binary inverse cyclotomic polynomial

At a primitive root the complex reading divided by its conjugate gives
the power corresponding to the sum. At the canonical root of order 4B a
bounded error in a supplied complex reading still identifies the sum in
the balanced interval. Candidate phases in the comparison are exact.
-/

namespace PrimeFactors.CyclotomicRootPhase

open Polynomial
open scoped ComplexConjugate

noncomputable def reading (N : ℕ) (z : ℂ) : ℂ :=
  (InverseCyclotomicMeasurements.polynomial N).eval₂ (Int.castRingHom ℂ) z

theorem evaluated {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q) (z : ℂ) :
    reading (p*q) z=(1-z^p)*(1-z^q) := by
  simp only [reading,InverseCyclotomicMeasurements.sparse pp qp ord,eval₂_mul,eval₂_sub,
    eval₂_one,eval₂_pow,eval₂_X]

theorem phase_identity {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    {z : ℂ} (unit : ‖z‖=1) :
    reading (p*q) z=z^(p+q)*conj (reading (p*q) z) := by
  have basic : z*conj z=1 := by rw [Complex.mul_conj',unit]; norm_num
  have one (k : ℕ) : z^k*(1-conj (z^k))= -(1-z^k) := by
    rw [map_pow,mul_sub,mul_one,←mul_pow,basic,one_pow]
    ring
  rw [evaluated pp qp ord,pow_add,map_mul,map_sub,map_one,map_sub,map_one]
  calc
    _ = (z^p*(1-conj (z^p)))*(z^q*(1-conj (z^q))) := by rw [one,one]; ring
    _ = _ := by ring

theorem phase_ratio {p q m : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    {z : ℂ} (root : IsPrimitiveRoot z m) (mp : 0<m) (np : ¬m∣p) (nq : ¬m∣q) :
    reading (p*q) z / conj (reading (p*q) z)=z^(p+q) := by
  have nz : reading (p*q) z≠0 := by
    rw [evaluated pp qp ord]
    exact mul_ne_zero (sub_ne_zero.mpr (fun h => np ((root.pow_eq_one_iff_dvd _).mp h.symm)))
      (sub_ne_zero.mpr (fun h => nq ((root.pow_eq_one_iff_dvd _).mp h.symm)))
  exact (div_eq_iff (show conj (reading (p*q) z) ≠ 0 by simpa using nz)).mpr
    (phase_identity pp qp ord (root.norm'_eq_one mp.ne'))

theorem phase_iff_congruent {p q m : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    {z : ℂ} (root : IsPrimitiveRoot z m) (mp : 0<m) (np : ¬m∣p) (nq : ¬m∣q) (s : ℕ) :
    reading (p*q) z/conj (reading (p*q) z)=z^s ↔ p+q ≡ s [MOD m] := by
  rw [phase_ratio pp qp ord root mp np nq, root.eq_orderOf]
  exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨m,mp,root.pow_eq_one⟩).pow_eq_pow_iff_modEq

theorem identifies {p q m B s : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (hi : q<2*B) (size : 4*B≤m) {z : ℂ} (root : IsPrimitiveRoot z m) (small : s<m) :
    reading (p*q) z/conj (reading (p*q) z)=z^s ↔ p+q=s := by
  have ppos := pp.pos
  have qpos := qp.pos
  rw [phase_ratio pp qp ord root (by omega) (Nat.not_dvd_of_pos_of_lt ppos (by omega))
    (Nat.not_dvd_of_pos_of_lt qpos (by omega))]
  exact ⟨root.pow_inj (by omega) small, by rintro rfl; rfl⟩

noncomputable def canonical (m : ℕ) : ℂ := Complex.exp (2*Real.pi*Complex.I/m)

theorem primitive {m : ℕ} (pos : 0<m) : IsPrimitiveRoot (canonical m) m :=
  Complex.isPrimitiveRoot_exp m pos.ne'

private theorem canonical_pow (m j : ℕ) :
    canonical m^j = Complex.exp (((2*Real.pi*j/m : ℝ):ℂ)*Complex.I) := by
  unfold canonical
  rw [←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- In the first half-turn a chord of the canonical mth roots is at
least `4j/m` when the indices differ by `j`. -/
theorem chord {m j : ℕ} (pos : 0<m) (half : 2*j≤m) :
    4*(j:ℝ)/m ≤ ‖1-canonical m^j‖ := by
  have mpos : (0:ℝ)<m := by exact_mod_cast pos
  let t := 2*Real.pi*j/(m:ℝ)
  have low : 0≤t := by dsimp only [t]; positivity
  have top : t≤Real.pi := by
    apply (div_le_iff₀ mpos).mpr
    have b : 2*(j:ℝ)≤m := by exact_mod_cast half
    nlinarith only [mul_le_mul_of_nonneg_left b Real.pi_pos.le]
  have cosine := Real.cos_le_one_sub_mul_cos_sq (x:=t) (by rwa [abs_of_nonneg low])
  have sqeq : ‖1-Complex.exp ((t:ℂ)*Complex.I)‖^2=2-2*Real.cos t := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.one_re,Complex.exp_ofReal_mul_I_re,
      Complex.sub_im,Complex.one_im,zero_sub,Complex.exp_ofReal_mul_I_im]
    nlinarith only [Real.sin_sq_add_cos_sq t]
  have lower : 2/Real.pi*t ≤ ‖1-Complex.exp ((t:ℂ)*Complex.I)‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [show (2/Real.pi*t)^2=2*(2/Real.pi^2*t^2) by ring]
    linarith only [sqeq,cosine]
  rw [canonical_pow]
  change _≤‖1-Complex.exp ((t:ℂ)*Complex.I)‖
  convert lower using 1
  dsimp only [t]
  field_simp
  ring

theorem magnitude {p q B : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (bp : 0<B) (low : B≤p) (hi : q<2*B) : 1 ≤ ‖reading (p*q) (canonical (4*B))‖ := by
  have bound {k : ℕ} (lo : B≤k) (top : k<2*B) : 1 ≤ ‖1-canonical (4*B)^k‖ := by
    apply le_trans _ (chord (by omega) (by omega))
    apply (le_div_iff₀ (by positivity)).mpr
    push_cast
    exact_mod_cast (by omega : 1*(4*B)≤4*k)
  rw [evaluated pp qp ord,norm_mul]
  simpa using mul_le_mul (bound low (by omega)) (bound (low.trans ord.le) hi)
    (by norm_num : (0:ℝ)≤1) (norm_nonneg _)


/-- The principal argument gives the full balanced sum without searching through phase indices.
The only supplied complex datum is the exact reading. -/
theorem argument_readout {p q B : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (bp : 0<B) (low : B≤p) (high : q<2*B) :
    let w := reading (p*q) (canonical (4*B))
    (4*(B:ℝ))*(1+(w/conj w).arg/(2*Real.pi)) = ((p+q:ℕ):ℝ) := by
  dsimp only
  have cp := pp.pos
  have cq := qp.pos
  rw [phase_ratio pp qp ord (primitive (by omega)) (by omega)
    (Nat.not_dvd_of_pos_of_lt cp (by omega)) (Nat.not_dvd_of_pos_of_lt cq (by omega)),
    canonical_pow]
  let θ := 2*Real.pi*((p+q:ℕ):ℝ)/((4*B:ℕ):ℝ)
  have mp : (0:ℝ)<((4*B:ℕ):ℝ) := by positivity
  have sl : ((4*B:ℕ):ℝ)<2*((p+q:ℕ):ℝ) := by exact_mod_cast (by omega : 4*B<2*(p+q))
  have sh : ((p+q:ℕ):ℝ)<((4*B:ℕ):ℝ) := by exact_mod_cast (by omega : p+q<4*B)
  have lowAngle : Real.pi<θ := (lt_div_iff₀ mp).mpr (by
    nlinarith only [mul_lt_mul_of_pos_left sl Real.pi_pos])
  have highAngle : θ<2*Real.pi := (div_lt_iff₀ mp).mpr
    (mul_lt_mul_of_pos_left sh (by positivity))
  have phase : (Complex.exp ((θ:ℂ)*Complex.I)).arg=θ-2*Real.pi := by
    have period : Complex.exp (((θ-2*Real.pi:ℝ):ℂ)*Complex.I)=
        Complex.exp ((θ:ℂ)*Complex.I) := by
      rw [show (((θ-2*Real.pi:ℝ):ℂ)*Complex.I)=
        (θ:ℂ)*Complex.I-2*Real.pi*Complex.I by push_cast; ring,
        Complex.exp_sub,Complex.exp_two_pi_mul_I,div_one]
    rw [←period,Complex.exp_mul_I,Complex.arg_cos_add_sin_mul_I]
    exact ⟨by linarith, by linarith only [highAngle,Real.pi_pos]⟩
  change 4*(B:ℝ)*(1+(Complex.exp ((θ:ℂ)*Complex.I)).arg/(2*Real.pi))=_
  rw [phase]
  dsimp only [θ]
  push_cast
  field_simp
  ring

private theorem power_gap {B a b : ℕ} (bp : 0<B) (order : a<b) (span : b-a≤2*B) :
    1/(B:ℝ) ≤ ‖canonical (4*B)^a-canonical (4*B)^b‖ := by
  let z := canonical (4*B)
  have unit : ‖z‖=1 := (primitive (by omega : 0<4*B)).norm'_eq_one (by omega)
  have eqn : z^a-z^b=z^a*(1-z^(b-a)) := by
    rw [mul_sub,mul_one,←pow_add,show a+(b-a)=b by omega]
  change _≤‖z^a-z^b‖
  rw [eqn,norm_mul,norm_pow,unit,one_pow,one_mul]
  apply le_trans _ (chord (m:=4*B) (j:=b-a) (by omega) (by omega))
  have lower : 1≤((b-a:ℕ):ℝ) := by exact_mod_cast (by omega : 1≤b-a)
  push_cast
  rw [show (1/(B:ℝ)) = 4/(4*(B:ℝ)) by ring]
  gcongr
  linarith

/-- Candidate sums in the balanced interval give separated comparison phases. -/
theorem separation {B a b : ℕ} (bp : 0<B) (al : 2*B≤a) (ah : a<4*B)
    (bl : 2*B≤b) (bh : b<4*B) (ne : a≠b) :
    1/(B:ℝ) ≤ ‖canonical (4*B)^a-canonical (4*B)^b‖ := by
  rcases lt_or_gt_of_ne ne with h|h
  · exact power_gap bp h (by omega)
  · rw [norm_sub_rev]
    exact power_gap bp h (by omega)

noncomputable def residual (z w : ℂ) (s : ℕ) : ℝ := ‖w-z^s*conj w‖

private theorem sensitivity {z : ℂ} (unit : ‖z‖=1) (w t : ℂ) (s : ℕ) :
    |residual z w s-residual z t s| ≤ 2*‖w-t‖ := by
  apply (abs_norm_sub_norm_le _ _).trans
  have eqn : (w-z^s*conj w)-(t-z^s*conj t)=(w-t)-z^s*conj (w-t) := by
    rw [map_sub]
    ring
  rw [eqn]
  apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_pow,unit,one_pow,one_mul,Complex.norm_conj]
  linarith

private theorem exact_residual {z t : ℂ} {S : ℕ} (phase : t=z^S*conj t) (s : ℕ) :
    residual z t s=‖z^S-z^s‖*‖t‖ := by
  unfold residual
  rw [show t-z^s*conj t=(z^S-z^s)*conj t by rw [sub_mul,←phase],norm_mul,Complex.norm_conj]

/-- An absolute-error disk of radius smaller than 1/(4B) about the supplied reading
selects precisely the true sum in the balanced interval by a residual comparison. -/
theorem noisy_iff {p q B s : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (bp : 0<B) (low : B≤p) (high : q<2*B) {w : ℂ} {ε : ℝ}
    (close : ‖w-reading (p*q) (canonical (4*B))‖≤ε) (precision : ε<1/(4*(B:ℝ)))
    (sl : 2*B≤s) (sh : s<4*B) :
    residual (canonical (4*B)) w s ≤ 2*ε ↔ s=p+q := by
  let z := canonical (4*B)
  let t := reading (p*q) z
  have unit : ‖z‖=1 := (primitive (by omega : 0<4*B)).norm'_eq_one (by omega)
  have phase : t=z^(p+q)*conj t := phase_identity pp qp ord unit
  have lip (j : ℕ) : |residual z w j-residual z t j| ≤ 2*ε :=
    (sensitivity unit w t j).trans (by linarith only [close] : 2*‖w-t‖≤2*ε)
  have gap : 4*ε < 1/(B:ℝ) := by
    calc 4*ε < 4*(1/(4*(B:ℝ))) := by linarith only [precision]
         _ = _ := by ring
  constructor
  · intro accept
    by_contra h
    have length := magnitude pp qp ord bp low high
    have sep := separation bp (a:=p+q) (by omega) (by omega) sl sh (Ne.symm h)
    have bound : 1/(B:ℝ)≤residual z t s := by
      rw [exact_residual phase]
      simpa using mul_le_mul sep length (by norm_num : (0:ℝ)≤1) (norm_nonneg _)
    have dist := (abs_le.mp (lip s)).1
    change residual z w s ≤ 2*ε at accept
    linarith only [dist,gap,bound,accept]
  · rintro rfl
    have dist := (abs_le.mp (lip (p+q))).2
    rw [exact_residual phase,sub_self,norm_zero,zero_mul,sub_zero] at dist
    exact dist

end PrimeFactors.CyclotomicRootPhase
