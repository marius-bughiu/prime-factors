import PrimeFactors.HigherDivisorWindow
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Tactic.IntervalCases

namespace PrimeFactors.PairedDivisorWindows

open Finset Polynomial

/-- Two candidate windows in the same odd-progression coordinate. The candidate
divisor at offset x is c+2x. For W<A these windows are disjoint. -/
def Near (A W x : ℤ) : Prop := |x-A|≤W ∨ |x+A|≤W

theorem band_abs {A W x : ℤ} (_nonneg : 0≤W) (ord : W≤A) (near : Near A W x) :
    A-W≤|x| ∧ |x|≤A+W := by
  rcases near with pos|neg
  · obtain ⟨_,_⟩ := abs_le.mp pos
    rw [abs_of_nonneg (show 0≤x by omega)]
    omega
  · obtain ⟨_,_⟩ := abs_le.mp neg
    rw [abs_of_nonpos (show x≤0 by omega)]
    omega

/-- The centered monic quadratic is small throughout both windows. -/
theorem quadratic_bound {A W x : ℤ} (nonneg : 0≤W) (ord : W≤A)
    (near : Near A W x) : |x^2-(A^2+W^2)|≤2*A*W := by
  obtain ⟨lo,hi⟩ := band_abs nonneg ord near
  have l := pow_le_pow_left₀ (sub_nonneg.mpr ord) lo 2
  have h := pow_le_pow_left₀ (abs_nonneg x) hi 2
  rw [sq_abs] at l h
  exact abs_le.mpr ⟨by nlinarith only [l],by nlinarith only [h]⟩

/-- No linear or constant shift of a monic quadratic improves the common
supremum, even on the four integer endpoints alone. -/
theorem monic_lower (A W b c H : ℤ) (nonneg : 0≤W)
    (bound : ∀ x, Near A W x → |x^2+b*x+c|≤H) : 2*A*W≤H := by
  have p₁ := (abs_le.mp (bound (A+W) (Or.inl (abs_le.mpr (by omega))))).2
  have p₂ := (abs_le.mp (bound (-(A+W)) (Or.inr (abs_le.mpr (by omega))))).2
  have p₃ := (abs_le.mp (bound (A-W) (Or.inl (abs_le.mpr (by omega))))).1
  have p₄ := (abs_le.mp (bound (-(A-W)) (Or.inr (abs_le.mpr (by omega))))).1
  nlinarith only [p₁,p₂,p₃,p₄]

/-- The same real length in a contiguous window has exact monic quadratic
supremum 2W²; positive separation A>W strictly increases the paired optimum. -/
theorem contiguous (W : ℤ) (hw : 0≤W) :
    (∀ x : ℤ, |x|≤2*W → |x^2-2*W^2|≤2*W^2) ∧
    ∀ b c H : ℤ, (∀ x : ℤ, |x|≤2*W → |x^2+b*x+c|≤H) → 2*W^2≤H := by
  constructor
  · intro x hx
    have h := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rw [sq_abs] at h
    exact abs_le.mpr ⟨by nlinarith only [sq_nonneg x],by nlinarith only [h]⟩
  · intro b c H bound
    have h := monic_lower W W b c H hw (fun x near =>
      bound x (by have z := (band_abs hw le_rfl near).2; omega))
    nlinarith only [h]

/-- Rewrite the monomial X^i in powers of P=X²−K and XP^j. -/
theorem monomial_expansion (i : ℕ) (x K : ℤ) :
    x^i = ∑ j ∈ range (i/2+1),
      (i/2).choose j * K^(i/2-j)*(x^2-K)^j*x^(i%2) := by
  calc
    x^i = (x^2)^(i/2)*x^(i%2) := by rw [←pow_mul,←pow_add,Nat.div_add_mod]
    _ = ((x^2-K)+K)^(i/2)*x^(i%2) := by rw [sub_add_cancel]
    _ = _ := by
      rw [add_pow,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The high-degree coordinates form an integral triangular matrix with diagonal one. -/
noncomputable def change (k : ℕ) (K : ℤ) : PowerJetContent.Rows k := fun i j =>
  if i.val%2=j.val%2 then ((i.val/2).choose (j.val/2):ℤ)* K^(i.val/2-j.val/2) else 0

theorem change_det (k : ℕ) (K : ℤ) : (change k K).det=1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [change]
  · intro i j lt
    change i.val<j.val at lt
    by_cases h : i.val%2=j.val%2
    · simp [change,h,Nat.choose_eq_zero_of_lt (show i.val/2<j.val/2 by omega)]
    · simp [change,h]

def weight (A W i : ℕ) := (2*A*W)^(i/2)*(A+W)^(i%2)

theorem weight_product (A W t : ℕ) :
    ∏ i ∈ range (2*t+1), weight A W i = (2*A*W)^(t^2)*(A+W)^t := by
  induction t with
  | zero => simp [weight]
  | succ t ih =>
    rw [show 2*(t+1)+1=(2*t+1+1)+1 by omega,
      Finset.prod_range_succ,Finset.prod_range_succ,ih]
    simp only [weight,show (2*t+1)/2=t by omega,show (2*t+1)%2=1 by omega,
      show (2*t+1+1)/2=t+1 by omega,show (2*t+1+1)%2=0 by omega,pow_one,pow_zero,mul_one]
    rw [show (t+1)^2=t^2+t+(t+1) by ring,pow_add,pow_add,pow_succ (A+W)]
    ring

noncomputable def scaled (k m : ℕ) (n t : ℤ) (A W : ℕ) : PowerJetContent.Rows k :=
  HigherDivisorWindow.scaledBasis k m n 1 t * change k ((A:ℤ)^2+(W:ℤ)^2) *
    Matrix.diagonal (fun i => (weight A W i.val : ℤ))

/-- One ordinary integer lattice, at total polynomial degree 2h. The separation
affects the determinant via the coordinate weights, without doubling the degree. -/
theorem scaled_det (h m : ℕ) (mk : m≤2*h) (n t : ℤ) (A W : ℕ) :
    (scaled (2*h) m n t A W).det =
      n^(m+m.choose 2)*((((2*A*W)^(h^2)*(A+W)^h:ℕ):ℤ)) := by
  rw [scaled,Matrix.det_mul,Matrix.det_mul,HigherDivisorWindow.scaled_det _ _ mk n 1 t,
    change_det,one_pow,mul_one,mul_one,Matrix.det_diagonal]
  congr 1
  rw [←Nat.cast_prod]
  exact_mod_cast (Fin.prod_univ_eq_prod_range (weight A W) (2*h+1)).trans (weight_product A W h)

/-- A polynomial only in the compressed coordinate has one common congruence
for both components; the sharp scalar radius is 2AW. -/
theorem scalar_congruence (x t K d : ℤ) (offset : d∣x-t) :
    d ∣ (x^2-K)-(t^2-K) := by
  rw [show (x^2-K)-(t^2-K)=(x-t)*(x+t) by ring]
  exact dvd_mul_of_dvd_left offset _

noncomputable def basis (K : ℤ) (i : ℕ) : ℤ[X] :=
  X^(i%2)*(X^2-C K)^(i/2)

theorem basis_degree (K : ℤ) (i : ℕ) : (basis K i).natDegree=i ∧ (basis K i).Monic := by
  have top : ((X:ℤ[X])^2-C K).Monic := monic_X_pow_sub_C K (by decide)
  refine ⟨?_,(monic_X.pow _).mul (top.pow _)⟩
  rw [basis,natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ top.ne_zero),
    natDegree_X_pow,natDegree_pow,natDegree_X_pow_sub_C]
  omega

theorem basis_bound (A W i : ℕ) (ord : W≤A) (x : ℤ) (near : Near A W x) :
    |(basis ((A:ℤ)^2+(W:ℤ)^2) i).eval x| ≤ (weight A W i:ℤ) := by
  have hx := (band_abs (Int.natCast_nonneg W) (by exact_mod_cast ord) near).2
  have hp := quadratic_bound (Int.natCast_nonneg W) (by exact_mod_cast ord) near
  simp only [basis,eval_mul,eval_pow,eval_X,eval_sub,eval_C,abs_mul,abs_pow,weight,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add]
  rw [mul_comm (|x|^_)]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hp _) (pow_le_pow_left₀ (abs_nonneg _) hx _)
    (pow_nonneg (abs_nonneg _) _) (pow_nonneg (by positivity) _)

noncomputable def combine {r : ℕ} (v : Fin r → ℤ) (K : ℤ) : ℤ[X] :=
  ∑ i, C (v i)*basis K i.val

theorem eval_bound {r : ℕ} (v : Fin r → ℤ) (A W : ℕ) (ord : W≤A) (x : ℤ)
    (near : Near A W x) :
    |(combine v ((A:ℤ)^2+(W:ℤ)^2)).eval x| ≤ ∑ i, |v i| *(weight A W i.val:ℤ) := by
  simp only [combine,eval_finset_sum,eval_mul,eval_C]
  refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (basis_bound A W i.val ord x near) (abs_nonneg _)

/-- The same row forces one ordinary root at any divisor in either component. -/
theorem root_of_divisor {m r n A W : ℕ} {v : Fin r → ℤ} {x d t : ℤ} (ord : W≤A)
    (jets : HigherDivisorWindow.Jets m n t (combine v ((A:ℤ)^2+(W:ℤ)^2)))
    (hd : d∣(n:ℤ)) (offset : d∣x-t) (near : Near A W x)
    (short : (∑ i, |v i| *(weight A W i.val:ℤ)) < d^m) :
    (combine v ((A:ℤ)^2+(W:ℤ)^2)).eval x=0 :=
  Int.eq_zero_of_abs_lt_dvd (HigherDivisorWindow.dvd_eval_of_jets jets hd offset)
    ((eval_bound v A W ord x near).trans_lt short)

theorem root_count {k : ℕ} (v : Fin (k+1) → ℤ) (K : ℤ) :
    (combine v K).roots.toFinset.card≤k := by
  apply (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_le _ _).trans ((basis_degree K i.val).1.trans_le (by omega))

theorem combine_nonzero {r : ℕ} {v : Fin r → ℤ} (nz : v≠0) (K : ℤ) : combine v K≠0 := by
  let seq : Polynomial.Sequence ℤ := ⟨basis K,fun i => by
    rw [Polynomial.degree_eq_natDegree (basis_degree K i).2.ne_zero,(basis_degree K i).1]⟩
  have li : LinearIndependent ℤ (fun i : Fin r => basis K i.val) :=
    seq.linearIndependent.comp (fun i : Fin r => i.val) Fin.val_injective
  intro zero
  apply nz
  apply _root_.funext
  apply (Fintype.linearIndependent_iff.mp li) v
  simpa only [combine,Polynomial.smul_eq_C_mul] using zero

/-- The finite public box contains a single nonzero polynomial serving both windows.
This sufficient criterion does not depend on an LLL implementation. -/
theorem relation_exists {m h n A W D : ℕ} (hn : 0<n) (hw : 0<W) (ord : W≤A) (hd : 0<D)
    (room : n^(m+m.choose 2)*((2*h+1)^(2*h+1)*((2*A*W)^(h^2)*(A+W)^h))<(D^m)^(2*h+1))
    (t : ℤ) : ∃ v : Fin (2*h+1) → ℤ, combine v ((A:ℤ)^2+(W:ℤ)^2) ≠ 0 ∧
      HigherDivisorWindow.Jets m n t (combine v ((A:ℤ)^2+(W:ℤ)^2)) ∧
      (∑ i, |v i| * (weight A W i.val:ℤ)) < (D:ℤ)^m := by
  classical
  let K : ℤ := (A:ℤ)^2+(W:ℤ)^2
  letI (i : Fin m) : NeZero (n^(m-i.val)) := ⟨(pow_pos hn _).ne'⟩
  let L := (i : Fin m) → ZMod (n^(m-i.val))
  let tag (u : Fin (2*h+1) → ℤ) : L := fun i => ((taylor t (combine u K)).coeff i.val:ℤ)
  have weights : ∏ i : Fin (2*h+1), weight A W i.val = (2*A*W)^(h^2)*(A+W)^h :=
    (Fin.prod_univ_eq_prod_range (weight A W) (2*h+1)).trans (weight_product A W h)
  have size : Fintype.card L * ((2*h+1)^(2*h+1) * ∏ i : Fin (2*h+1), weight A W i.val) <
      (D^m)^(2*h+1) := by
    simpa only [L,Fintype.card_pi,ZMod.card,prod_pow_eq_pow_sum,HigherDivisorWindow.tag_sum,
      weights] using room
  have ha : 0<A := hw.trans_le ord
  obtain ⟨u,v,ne,eq,short⟩ := HigherDivisorWindow.finite_collision (by omega : 0<2*h+1)
    (pow_pos hd m) (fun i : Fin (2*h+1) => weight A W i.val) (fun _ => by
      unfold weight; positivity) size tag
  refine ⟨u-v,combine_nonzero (sub_ne_zero.mpr ne) K,?_,?_⟩
  · intro i
    have sub : combine (u-v) K=combine u K-combine v K := by
      simp [combine,sub_mul,sum_sub_distrib]
    change (n:ℤ)^(m-i.val) ∣ (taylor t (combine (u-v) K)).coeff i.val
    rw [sub,map_sub,coeff_sub,← Nat.cast_pow,← ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.cast_sub,sub_eq_zero]
    exact congrFun eq i
  · simpa only [Pi.sub_apply,Nat.cast_pow] using short

/-- All inputs selecting F are public. Each eligible divisor in either window is
among at most 2h roots of that same polynomial. -/
theorem common_roots {m h n A W D : ℕ} (hn : 0<n) (hw : 0<W) (ord : W≤A) (hd : 0<D)
    (room : n^(m+m.choose 2)*((2*h+1)^(2*h+1)*((2*A*W)^(h^2)*(A+W)^h))<(D^m)^(2*h+1))
    {c s t : ℤ} (unit : IsCoprime s (n:ℤ)) (anchor : (n:ℤ) ∣ c+s*t) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤2*h ∧ ∀ x d : ℤ, d∣(n:ℤ) →
      d=c+s*x → (D:ℤ)≤d → Near A W x → x∈F.roots.toFinset := by
  obtain ⟨v,nz,jets,short⟩ := relation_exists hn hw ord hd room t
  refine ⟨_,nz,root_count v _,?_⟩
  intro x d factor pos lower near
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots nz).mpr
  exact root_of_divisor ord jets factor
    (QuarticDivisorWindow.progression_offset unit anchor factor pos) near
    (short.trans_le (pow_le_pow_left₀ (by positivity) lower _))

namespace Example

/-- One public quartic for both disjoint three-position windows for 9009. -/
def row : Fin 5 → ℤ := ![-156,-21,-64,5,14]
def ordinary : Fin 5 → ℤ := ![1884,-71,-344,5,14]

theorem eval_row (x : ℤ) :
    (combine row 10).eval x=1884-71*x-344*x^2+5*x^3+14*x^4 := by
  simp only [combine,eval_finset_sum,eval_mul,eval_C,basis,eval_pow,eval_X,eval_sub,eval_add,
    Fin.sum_univ_five]
  change (-156)*(x^0*(x^2-10)^0)+(-21)*(x^1*(x^2-10)^0)+
    (-64)*(x^0*(x^2-10)^1)+5*(x^1*(x^2-10)^1)+14*(x^0*(x^2-10)^2)=_
  ring

theorem row_eq : combine row 10=ofFn 5 ordinary := by
  apply Polynomial.funext
  intro x
  rw [eval_row,HigherDivisorWindow.eval_coeff,Fin.sum_univ_five]
  change _=1884*x^0+(-71)*x^1+(-344)*x^2+5*x^3+14*x^4
  ring

theorem jets : HigherDivisorWindow.Jets 2 9009 4463 (combine row 10) := by
  rw [row_eq]
  intro i
  rw [HigherDivisorWindow.jet_coeff,Fin.sum_univ_five]
  fin_cases i <;> decide +kernel

theorem height : (∑ i : Fin 5, |row i| * (weight 3 1 i.val:ℤ))=1248 := by
  rw [Fin.sum_univ_five]
  decide +kernel

theorem candidates (x : ℤ) (near : Near 3 1 x) :
    (83+2*x) ∣ 9009 ↔ x= -3 ∨ x=4 := by
  constructor
  · intro factor
    obtain ⟨lo,hi⟩ := abs_le.mp (band_abs (by decide : 0≤(1:ℤ)) (by decide : 1≤(3:ℤ)) near).2
    have unit : IsCoprime (2:ℤ) 9009 := ⟨-4504,1,by decide⟩
    have offset := QuarticDivisorWindow.progression_offset (x:=x) unit
      (by decide : (9009:ℤ) ∣ 83+2*4463) factor rfl
    have sq := pow_le_pow_left₀ (by decide : 0≤(75:ℤ)) (by omega : 75≤83+2*x) 2
    have short : (∑ i : Fin 5, |row i| * (weight 3 1 i.val:ℤ))<(83+2*x)^2 := by
      rw [height]; omega
    have root := root_of_divisor (m:=2) (n:=9009) (A:=3) (W:=1) (by decide) jets
      factor offset near short
    rw [show ((3:ℕ):ℤ)^2+((1:ℕ):ℤ)^2=10 by decide,eval_row] at root
    interval_cases x <;> norm_num at *
  · rintro (rfl|rfl) <;> decide +kernel

theorem splits : (9009:ℕ)=77*117 ∧ (9009:ℕ)=91*99 := by decide +kernel

end Example
end PrimeFactors.PairedDivisorWindows
