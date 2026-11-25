import PrimeFactors.PairedDivisorWindows
import PrimeFactors.ChebyshevDivisorWindow
import PrimeFactors.GapPolynomialScale
import Mathlib.Data.Real.Sqrt

/-! Degree-by-degree choice of integer monic coordinates for the union of two windows.
The reflected Chebyshev construction is a polynomial inverse image of an interval.
The finite arithmetic application chooses between that construction and the enclosing
interval in every degree independently. -/

namespace PrimeFactors.PairedChebyshevWindows

open Finset Polynomial
open PairedDivisorWindows (Near)

noncomputable def paired (A W i : ℕ) : ℤ[X] :=
  X^(i%2) * (ChebyshevDivisorWindow.basis (A*W) (i/2)).comp (X^2-C ((A:ℤ)^2+(W:ℤ)^2))

def pairedWeight (A W i : ℕ) := ChebyshevDivisorWindow.weight (A*W) (i/2)*(A+W)^(i%2)

theorem paired_degree (A W i : ℕ) : (paired A W i).natDegree=i ∧ (paired A W i).Monic := by
  let Q : ℤ[X] := X^2-C ((A:ℤ)^2+(W:ℤ)^2)
  have qm : Q.Monic := monic_X_pow_sub_C _ (by decide)
  have qd : Q.natDegree=2 := natDegree_X_pow_sub_C
  obtain ⟨bd,bm⟩ := ChebyshevDivisorWindow.degree_basis (A*W) (i/2)
  have cm := bm.comp qm (by omega)
  refine ⟨?_,(monic_X.pow _).mul cm⟩
  change (X^(i%2)*(_ : ℤ[X]).comp Q).natDegree=i
  rw [natDegree_mul (pow_ne_zero _ X_ne_zero) cm.ne_zero,natDegree_X_pow,natDegree_comp,bd,qd]
  omega

theorem paired_bound (A W i : ℕ) (ord : W≤A) (x : ℤ) (near : Near A W x) :
    |(paired A W i).eval x|≤(pairedWeight A W i:ℤ) := by
  have hx := (PairedDivisorWindows.band_abs (Int.natCast_nonneg W) (by exact_mod_cast ord) near).2
  have hq := PairedDivisorWindows.quadratic_bound (Int.natCast_nonneg W) (by exact_mod_cast ord) near
  have dp := ChebyshevDivisorWindow.eval_bound (A*W) (i/2) (x^2-((A:ℤ)^2+(W:ℤ)^2)) (by
    push_cast; nlinarith only [hq])
  simp only [paired,eval_mul,eval_pow,eval_X,eval_comp,eval_sub,eval_C,abs_mul,abs_pow,
    pairedWeight,Nat.cast_mul,Nat.cast_pow,Nat.cast_add]
  rw [mul_comm (|x|^_)]
  exact mul_le_mul dp (pow_le_pow_left₀ (abs_nonneg _) hx _) (by positivity)
    (Int.natCast_nonneg _)

/-- Exact product of all coordinate scales in the pure paired basis. -/
theorem paired_product (A W h : ℕ) :
    (∏ i ∈ range (2*(h+1)+1), pairedWeight A W i) =
      2^(2*h+1)*(A+W)^(h+1)*(A*W)^((h+1)^2) := by
  rw [←GapPolynomialScale.weight_product]
  have aux (k : ℕ) : (∏ i ∈ range (2*k+1), pairedWeight A W i) =
      ∏ j ∈ range k, GapPolynomialScale.weight (A*W) (j+1)*((A+W)*GapPolynomialScale.weight (A*W) j) := by
    induction k with
    | zero => simp [pairedWeight,ChebyshevDivisorWindow.weight,GapPolynomialScale.weight]
    | succ k ih =>
      rw [show 2*(k+1)+1=(2*k+1+1)+1 by omega,prod_range_succ,prod_range_succ,ih,prod_range_succ]
      simp only [pairedWeight,ChebyshevDivisorWindow.weight,show (2*k+1)/2=k by omega,show (2*k+1)%2=1 by omega,
        show (2*k+1+1)/2=k+1 by omega,show (2*k+1+1)%2=0 by omega,pow_one,pow_zero,mul_one]
      ring
  exact aux _

/-- Round the hull half-radius up only when A+W is odd. -/
def hullRadius (A W : ℕ) := (A+W+1)/2

def weight (A W i : ℕ) := min (pairedWeight A W i) (ChebyshevDivisorWindow.weight (hullRadius A W) i)

noncomputable def basis (A W i : ℕ) : ℤ[X] :=
  if pairedWeight A W i ≤ ChebyshevDivisorWindow.weight (hullRadius A W) i
  then paired A W i else ChebyshevDivisorWindow.basis (hullRadius A W) i

theorem degree_basis (A W i : ℕ) : (basis A W i).natDegree=i ∧ (basis A W i).Monic := by
  unfold basis
  split
  · exact paired_degree ..
  · exact ChebyshevDivisorWindow.degree_basis ..

theorem basis_bound (A W i : ℕ) (ord : W≤A) (x : ℤ) (near : Near A W x) :
    |(basis A W i).eval x| ≤ (weight A W i:ℤ) := by
  unfold basis weight
  split <;> rename_i h
  · rw [min_eq_left h]
    exact paired_bound A W i ord x near
  · rw [min_eq_right (le_of_not_ge h)]
    apply ChebyshevDivisorWindow.eval_bound
    have hx := (PairedDivisorWindows.band_abs (Int.natCast_nonneg W) (by exact_mod_cast ord) near).2
    exact hx.trans (by exact_mod_cast (show A+W≤2*hullRadius A W by unfold hullRadius; omega))

noncomputable def coefficients (k A W : ℕ) : PowerJetContent.Rows k :=
  fun i j => (basis A W i.val).coeff j.val

theorem unimodular (k A W : ℕ) : (coefficients k A W).det=1 := by
  rw [Matrix.det_of_lowerTriangular]
  · have diag (i : Fin (k+1)) : coefficients k A W i i=1 := by
      simpa only [coefficients,Monic,leadingCoeff,(degree_basis A W i.val).1] using
        (degree_basis A W i.val).2
    simp only [diag,prod_const_one]
  · intro i j lt
    exact coeff_eq_zero_of_natDegree_lt ((degree_basis A W i.val).1.trans_lt lt)

/-- Even when adjacent degrees come from different bases the jet covolume
changes only by the diagonal product. -/
theorem scaled_det (k m A W : ℕ) (mk : m≤k) (n t : ℤ) :
    ((HigherDivisorWindow.scaledBasis k m n 1 t * (coefficients k A W)⁻¹) *
      Matrix.diagonal (fun i : Fin (k+1) => (weight A W i.val:ℤ))).det =
      n^(m+m.choose 2)*(∏ i : Fin (k+1), (weight A W i.val:ℤ)) := by
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_nonsing_inv,unimodular,
    HigherDivisorWindow.scaled_det _ _ mk,Matrix.det_diagonal]
  simp

private theorem positive_weight (A W i : ℕ) (hw : 0<W) (ord : W≤A) : 0<weight A W i := by
  have pos (p j : ℕ) (hp : 0<p) : 0<ChebyshevDivisorWindow.weight p j := by
    cases j <;> simp [ChebyshevDivisorWindow.weight,GapPolynomialScale.weight,hp]
  exact lt_min (Nat.mul_pos (pos _ _ (Nat.mul_pos (hw.trans_le ord) hw)) (pow_pos (by omega) _))
    (pos _ _ (by unfold hullRadius; omega))

/-- A positive gap already gives strict improvement in coordinate two. Every
other coordinate is bounded by its enclosing-interval counterpart. -/
theorem strict_hull {k A W : ℕ} (degree : 2≤k) (hw : 0<W) (gap : W<A) :
    (∏ i : Fin (k+1), weight A W i.val) <
    ∏ i : Fin (k+1), ChebyshevDivisorWindow.weight (hullRadius A W) i.val := by
  apply Finset.prod_lt_prod (fun i _ => positive_weight A W i.val hw gap.le)
    (fun i _ => min_le_right ..)
  refine ⟨⟨2,by omega⟩,mem_univ _,(min_le_left ..).trans_lt ?_⟩
  change pairedWeight A W 2 < ChebyshevDivisorWindow.weight (hullRadius A W) 2
  norm_num [pairedWeight,ChebyshevDivisorWindow.weight,GapPolynomialScale.weight]
  have r : A+W≤2*hullRadius A W := by unfold hullRadius; omega
  have d := pow_le_pow_left₀ (Nat.zero_le _) r 2
  have pos : (0:ℤ)<(A:ℤ)-W := by omega
  have z := sq_pos_of_pos pos
  exact_mod_cast (show (A:ℤ)*W<(hullRadius A W:ℤ)^2 by
    have dc : ((A:ℤ)+W)^2≤(2*(hullRadius A W:ℤ))^2 := by exact_mod_cast d
    nlinarith only [dc,z])

/-- One public relation covers every divisor in either window when these mixed
coordinates pass the box comparison. -/
theorem common_roots {k m n A W D : ℕ} (hn : 0<n) (hw : 0<W) (ord : W≤A) (hd : 0<D)
    (room : n^(m+m.choose 2)*((k+1)^(k+1)* ∏ i : Fin (k+1), weight A W i.val)<(D^m)^(k+1))
    {c s t : ℤ} (unit : IsCoprime s (n:ℤ)) (anchor : (n:ℤ) ∣ c+s*t) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤k ∧ ∀ x d : ℤ, d∣(n:ℤ) →
      d=c+s*x → (D:ℤ)≤d → Near A W x → x∈F.roots.toFinset := by
  classical
  let H (v : Fin (k+1) → ℤ) := ∑ i, C (v i)*basis A W i.val
  let seq : Polynomial.Sequence ℤ := ⟨basis A W,fun i => by
    rw [Polynomial.degree_eq_natDegree (degree_basis A W i).2.ne_zero,(degree_basis A W i).1]⟩
  have li : LinearIndependent ℤ (fun i : Fin (k+1) => basis A W i.val) :=
    seq.linearIndependent.comp (fun i : Fin (k+1) => i.val) Fin.val_injective
  letI (i : Fin m) : NeZero (n^(m-i.val)) := ⟨(pow_pos hn _).ne'⟩
  let L := (i : Fin m) → ZMod (n^(m-i.val))
  let tag (u : Fin (k+1) → ℤ) : L := fun i => ((taylor t (H u)).coeff i.val:ℤ)
  have size : Fintype.card L * ((k+1)^(k+1) * ∏ i : Fin (k+1), weight A W i.val) <
      (D^m)^(k+1) := by
    simpa only [L,Fintype.card_pi,ZMod.card,prod_pow_eq_pow_sum,HigherDivisorWindow.tag_sum] using room
  obtain ⟨u,v,ne,eq,short⟩ := HigherDivisorWindow.finite_collision (by omega : 0<k+1) (pow_pos hd m)
    (fun i : Fin (k+1) => weight A W i.val) (fun i => positive_weight A W i.val hw ord) size tag
  let F := H (u-v)
  have nz : F≠0 := by
    intro zero
    apply sub_ne_zero.mpr ne
    apply _root_.funext
    apply (Fintype.linearIndependent_iff.mp li) (u-v)
    simpa only [F,H,Polynomial.smul_eq_C_mul] using zero
  refine ⟨F,nz,?_,?_⟩
  · apply (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact (natDegree_C_mul_le _ _).trans ((degree_basis A W i.val).1.trans_le (by omega))
  · have jets : HigherDivisorWindow.Jets m n t F := by
      have sub : F=H u-H v := by simp [F,H,sub_mul,sum_sub_distrib]
      intro i
      rw [sub,map_sub,coeff_sub,← Nat.cast_pow,← ZMod.intCast_zmod_eq_zero_iff_dvd,
        Int.cast_sub,sub_eq_zero]
      exact congrFun eq i
    intro x d factor position lower near
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots nz).mpr
    have div := HigherDivisorWindow.dvd_eval_of_jets jets factor
      (QuarticDivisorWindow.progression_offset unit anchor factor position)
    apply Int.eq_zero_of_abs_lt_dvd div
    have bound : |F.eval x| ≤ ∑ i, |u i - v i| * (weight A W i.val:ℤ) := by
      simp only [F,H,eval_finset_sum,eval_mul,eval_C,Pi.sub_apply]
      refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (basis_bound A W _ ord x near) (abs_nonneg _)
    exact (bound.trans_lt (by simpa using short : _ < (D:ℤ)^m)).trans_le
      (pow_le_pow_left₀ (Int.natCast_nonneg _) lower _)

/-- A finite difference between the sufficient tests on a balanced semiprime. -/
theorem quartic_comparison :
    (∏ i : Fin 5, weight 3 1 i.val)=6912 ∧
    (∏ i : Fin 5, pairedWeight 3 1 i.val)=10368 ∧
    (∏ i : Fin 5, ChebyshevDivisorWindow.weight 2 i.val)=16384 ∧
    (11227:ℕ)^3*(5^5*6912)<89^10 ∧ 89^10≤11227^3*(5^5*10368) := by
  decide +kernel

theorem quartic_example : ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤4 ∧
    (3:ℤ)∈F.roots.toFinset ∧ ∀ x d : ℤ, d∣11227 → d=97+2*x → 89≤d →
    Near 3 1 x → x∈F.roots.toFinset := by
  have unit : IsCoprime (2:ℤ) 11227 := ⟨-5613,1,by decide⟩
  obtain ⟨F,nz,count,all⟩ := common_roots (k:=4) (m:=2) (D:=89) (A:=3) (W:=1)
    (by decide : 0<11227) (by decide) (by decide) (by decide) (by decide +kernel)
    unit (by decide : (11227:ℤ) ∣ 97+2*5565)
  exact ⟨F,nz,count,all 3 103 (by decide) (by decide) (by decide) (Or.inl (by decide)),all⟩

/-- Symmetrization transfers every uniform bound to the single compressed
interval. For a monic polynomial of even degree the function G is monic of
half that degree. The odd part x*L never improves its supremum. -/
theorem reflected_lower (A W H : ℝ) (G L : ℝ → ℝ) (hw : 0≤W) (ord : W≤A)
    (bound : ∀ x : ℝ, A-W≤|x| → |x|≤A+W →
      |G (x^2-(A^2+W^2)) + x*L (x^2-(A^2+W^2))|≤H) :
    ∀ y : ℝ, |y|≤2*(A*W) → |G y|≤H := by
  intro y hy
  obtain ⟨yl,yu⟩ := abs_le.mp hy
  let z := Real.sqrt (A^2+W^2+y)
  have z0 : 0≤z := Real.sqrt_nonneg _
  have z2 : z^2=A^2+W^2+y := Real.sq_sqrt (by nlinarith only [yl,sq_nonneg (A-W)])
  have left : A-W≤z := (sq_le_sq₀ (sub_nonneg.mpr ord) z0).mp (by nlinarith only [yl,z2])
  have right : z≤A+W := (sq_le_sq₀ z0 (by linarith)).mp (by nlinarith only [yu,z2])
  have p := abs_le.mp (bound z (by rwa [abs_of_nonneg z0]) (by rwa [abs_of_nonneg z0]))
  have q := abs_le.mp (bound (-z) (by rwa [abs_neg,abs_of_nonneg z0])
    (by rwa [abs_neg,abs_of_nonneg z0]))
  have eq : z^2-(A^2+W^2)=y := by linarith only [z2]
  rw [eq] at p
  rw [neg_sq,eq] at q
  exact abs_le.mpr ⟨by linarith only [p.1,q.1],by linarith only [p.2,q.2]⟩

/-- The quartic Dickson bound is the exact continuous minimax even allowing odd
coefficients. Use the two endpoints on each side and ±sqrt(A²+W²). -/
theorem quartic_minimax (A W b c d e H : ℝ) (hw : 0≤W) (ord : W≤A)
    (bound : ∀ x : ℝ, A-W≤|x| → |x|≤A+W → |x^4+b*x^3+c*x^2+d*x+e|≤H) :
    2*(A*W)^2≤H := by
  let z := Real.sqrt (A^2+W^2)
  have z0 : 0≤z := Real.sqrt_nonneg _
  have z2 : z^2=A^2+W^2 := Real.sq_sqrt (by positivity)
  have zero : 0≤A-W := by linarith
  have plus : 0≤A+W := by linarith
  have cross : 0≤A*W := mul_nonneg (hw.trans ord) hw
  have zl : A-W≤z := (sq_le_sq₀ zero z0).mp (by nlinarith only [cross,z2])
  have zu : z≤A+W := (sq_le_sq₀ z0 plus).mp (by nlinarith only [cross,z2])
  have ends (y : ℝ) (lo : A-W≤y) (hi : y≤A+W) :
      -(2*H)≤2*(y^4+c*y^2+e) ∧ 2*(y^4+c*y^2+e)≤2*H := by
    have ab : |y|=y := abs_of_nonneg (zero.trans lo)
    have h1 := abs_le.mp (bound y (by rwa [ab]) (by rwa [ab]))
    have h2 := abs_le.mp (bound (-y) (by rwa [abs_neg,ab]) (by rwa [abs_neg,ab]))
    constructor <;> linarith only [h1.1,h1.2,h2.1,h2.2]
  have z4 : z^4=(A^2+W^2)^2 := by rw [show z^4=(z^2)^2 by ring,z2]
  have mid := (ends z zl zu).1
  rw [z4,z2] at mid
  nlinarith only [(ends (A-W) le_rfl (by linarith)).2,(ends (A+W) (by linarith) le_rfl).2,mid]

theorem quartic_attains (A W x : ℝ) (hw : 0≤W) (ord : W≤A)
    (near : A-W≤|x| ∧ |x|≤A+W) :
    |(x^2-(A^2+W^2))^2-2*(A*W)^2|≤2*(A*W)^2 := by
  have lo := (sq_le_sq₀ (sub_nonneg.mpr ord) (abs_nonneg x)).mpr near.1
  have hi := (sq_le_sq₀ (abs_nonneg x) (add_nonneg (hw.trans ord) hw)).mpr near.2
  rw [sq_abs] at lo hi
  have a : |x^2-(A^2+W^2)|≤2*(A*W) := abs_le.mpr ⟨by linarith only [lo],by linarith only [hi]⟩
  have b := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num : (0:ℝ)≤2)
    (mul_nonneg (hw.trans ord) hw))).mpr a
  rw [sq_abs] at b
  exact abs_le.mpr ⟨by nlinarith only [sq_nonneg (x^2-(A^2+W^2))],by nlinarith only [b]⟩

end PrimeFactors.PairedChebyshevWindows
