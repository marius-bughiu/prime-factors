import PrimeFactors.QuarticDivisorWindow
import PrimeFactors.PowerJetContent
import Mathlib.Algebra.Polynomial.ofFn
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.BigOperators.Intervals

/-!
The finite box argument below is independent of lattice reduction. For construction,
the univariate unknown-divisor method is described in Alexander May's thesis, Theorems
6–7 (https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38), following
Coppersmith (https://doi.org/10.1007/s001459900030). The first-vector estimate used for
the separate numerical comparison is Proposition 1.6 of Lenstra, Lenstra and Lovász
(https://doi.org/10.1007/BF01457454). These publications are referenced for their
mathematics. The LLL algorithm and its first-vector theorem are not formalized here.
-/

namespace PrimeFactors.HigherDivisorWindow

open Finset Polynomial

/-- Coefficients in ascending powers of the centered progression index X. -/
noncomputable def height {r : ℕ} (v : Fin r → ℤ) (W : ℕ) : ℤ :=
  ∑ i, |v i| * (W:ℤ)^i.val

/-- Residue conditions on F(t+Y) in Y, down to modulus N for degree m−1. -/
def Jets (m n : ℕ) (t : ℤ) (F : ℤ[X]) : Prop :=
  ∀ i : Fin m, (n:ℤ)^(m-i.val) ∣ (taylor t F).coeff i.val

private theorem finite_collision {L : Type*} [Fintype L] {r M : ℕ} (hr : 0<r) (hm : 0<M)
    (w : Fin r → ℕ) (hw : ∀ i, 0<w i)
    (room : Fintype.card L * (r^r * ∏ i, w i) < M^r) (label : (Fin r → ℤ) → L) :
    ∃ u v : Fin r → ℤ, u≠v ∧ label u=label v ∧
      (∑ i, |u i-v i| *(w i:ℤ)) < (M:ℤ) := by
  classical
  let side (i : Fin r) := (M-1)/(r*w i)+1
  let Box := (i : Fin r) → Fin (side i)
  let lift (b : Box) := fun i => ((b i).val:ℤ)
  have cover (i : Fin r) : M ≤ (r*w i)*side i := by
    have h := Nat.lt_mul_div_succ (M-1) (Nat.mul_pos hr (hw i))
    dsimp [side]; omega
  have all : M^r ≤ (r^r * ∏ i, w i)* ∏ i, side i := by
    have h := Finset.prod_le_prod' (s:=univ) (fun i _ => cover i)
    simpa only [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin] using h
  have more : Fintype.card L < Fintype.card Box := by
    apply Nat.lt_of_mul_lt_mul_right (a:=r^r * ∏ i, w i)
    simpa only [Box,Fintype.card_pi,Fintype.card_fin,Nat.mul_comm] using room.trans_le all
  obtain ⟨a,b,ne,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun p => label (lift p)) more
  refine ⟨lift a,lift b,?_,eq,?_⟩
  · intro e
    apply ne
    funext i
    apply Fin.ext
    have h : ((a i).val:ℤ) = (b i).val := congrFun e i
    exact_mod_cast h
  · have term (i : Fin r) : (r:ℤ)*(|(lift a) i-(lift b) i| *(w i:ℤ)) ≤ ((M-1:ℕ):ℤ) := by
      have ha := (a i).isLt
      have hb := (b i).isLt
      change (a i).val < (M-1)/(r*w i)+1 at ha
      change (b i).val < (M-1)/(r*w i)+1 at hb
      have diff : |(lift a) i-(lift b) i| ≤ (((M-1)/(r*w i):ℕ):ℤ) := by
        apply abs_le.mpr
        dsimp [lift]; omega
      have prod := mul_le_mul_of_nonneg_right diff (show 0≤(r:ℤ)*(w i:ℤ) by positivity)
      have cap : ((r*w i:ℕ):ℤ)*(((M-1)/(r*w i):ℕ):ℤ) ≤ ((M-1:ℕ):ℤ) := by
        exact_mod_cast Nat.mul_div_le (M-1) (r*w i)
      simp only [Nat.cast_mul] at cap
      linarith only [prod,cap]
    have summed := Finset.sum_le_sum (s:=univ) (fun i _ => term i)
    simp only [← Finset.mul_sum,Finset.sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at summed
    have bound := le_of_mul_le_mul_left summed (by exact_mod_cast hr : (0:ℤ)<r)
    omega

private theorem tag_sum (m : ℕ) : (∑ i : Fin m, (m-i.val)) = m+m.choose 2 := by
  rw [Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i ∈ range (m+1), (m-i) := by rw [sum_range_succ]; simp
    _ = ∑ i ∈ range (m+1), i := by simpa using sum_range_reflect id (m+1)
    _ = (m+1).choose 2 := by rw [sum_range_id,Nat.choose_two_right]
    _ = _ := by rw [Nat.choose_succ_succ,Nat.choose_one_right]

private theorem weight_sum (r : ℕ) : (∑ i : Fin r, i.val) = r.choose 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i),sum_range_id,Nat.choose_two_right]

/-- The actual coefficient-scaled matrix, with one row per translated power and
one column per ordinary coefficient. Powers with exponent i>m have unit row multiplier. -/
noncomputable def scaledBasis (k m : ℕ) (n W t : ℤ) : PowerJetContent.Rows k :=
  fun i j => n^(m-i.val) * ((X + C (-t))^i.val : ℤ[X]).coeff j.val * W^j.val

theorem scaled_det (k m : ℕ) (mk : m≤k) (n W t : ℤ) :
    (scaledBasis k m n W t).det = n^(m+m.choose 2)*W^((k+1).choose 2) := by
  rw [Matrix.det_of_lowerTriangular]
  · have raw := PowerJetContent.det_basis n m k mk
    rw [PowerJetContent.basis,Matrix.det_diagonal] at raw
    simp only [scaledBasis,coeff_X_add_C_pow,Nat.sub_self,pow_zero,Nat.choose_self,Nat.cast_one,
      mul_one,prod_mul_distrib,raw,Finset.prod_pow_eq_pow_sum,weight_sum]
  · intro i j lt
    change i < j at lt
    simp only [scaledBasis,coeff_X_add_C_pow,Nat.choose_eq_zero_of_lt (show i.val<j.val from lt),
      Nat.cast_zero,mul_zero,zero_mul]

/-- Pigeonholing the translated Taylor coefficients gives a short polynomial at every center. -/
theorem relation_exists {m r n W D : ℕ} (hr : 0<r) (hn : 0<n) (hw : 0<W) (hd : 0<D)
    (room : n^(m+m.choose 2) * (r^r * W^(r.choose 2)) < (D^m)^r) (t : ℤ) :
    ∃ v : Fin r → ℤ, ofFn r v≠0 ∧ Jets m n t (ofFn r v) ∧ height v W < (D:ℤ)^m := by
  classical
  letI (i : Fin m) : NeZero (n^(m-i.val)) := ⟨(pow_pos hn _).ne'⟩
  let L := (i : Fin m) → ZMod (n^(m-i.val))
  let tag (p : Fin r → ℤ) : L := fun i => ((taylor t (ofFn r p)).coeff i.val:ℤ)
  have size : Fintype.card L * (r^r * ∏ i : Fin r, W^i.val) < (D^m)^r := by
    simpa only [L,Fintype.card_pi,ZMod.card,Finset.prod_pow_eq_pow_sum,tag_sum,weight_sum] using room
  obtain ⟨u,v,ne,eq,short⟩ := finite_collision hr (pow_pos hd m) (fun i : Fin r => W^i.val)
    (fun _ => pow_pos hw _) size tag
  refine ⟨u-v,?_,?_,?_⟩
  · intro zero
    apply ne
    apply sub_eq_zero.mp
    apply injective_ofFn r
    simpa using zero
  · intro i
    rw [map_sub,map_sub,coeff_sub,← Nat.cast_pow,← ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.cast_sub,sub_eq_zero]
    exact congrFun eq i
  · simpa only [height,Pi.sub_apply,Nat.cast_pow] using short

/-- The ordinary coefficient witnesses used by the bounded executable checker. -/
theorem jet_coeff {r : ℕ} (v : Fin r → ℤ) (t : ℤ) (j : ℕ) :
    (taylor t (ofFn r v)).coeff j = ∑ i, v i*(i.val.choose j:ℤ)*t^(i.val-j) := by
  rw [taylor_coeff,ofFn_eq_sum_monomial,map_sum,eval_finset_sum]
  simp [hasseDeriv_monomial,eval_monomial,mul_comm]

theorem eval_coeff {r : ℕ} (v : Fin r → ℤ) (x : ℤ) :
    (ofFn r v).eval x = ∑ i, v i*x^i.val := by
  rw [ofFn_eq_sum_monomial,eval_finset_sum]
  simp [eval_monomial,mul_comm]

/-- A sufficiently small auxiliary polynomial vanishes at every divisor in its window. -/
theorem root_of_divisor {m r n W : ℕ} {t x d : ℤ} {v : Fin r → ℤ}
    (jets : Jets m n t (ofFn r v)) (factor : d∣(n:ℤ)) (offset : d∣x-t)
    (near : |x|≤(W:ℤ)) (small : height v W<d^m) :
    (ofFn r v).eval x=0 := by
  have divides : d^m ∣ (ofFn r v).eval x := by
    rw [← taylor_eval_sub t _ x,eval_eq_sum_range]
    apply dvd_sum
    intro i _
    by_cases im : i<m
    · have first := (pow_dvd_pow_of_dvd factor (m-i)).trans (jets ⟨i,im⟩)
      have second := pow_dvd_pow_of_dvd offset i
      simpa only [← pow_add,Nat.sub_add_cancel im.le] using mul_dvd_mul first second
    · exact dvd_mul_of_dvd_right ((pow_dvd_pow d (by omega : m ≤ i)).trans
        (pow_dvd_pow_of_dvd offset i)) _
  apply Int.eq_zero_of_abs_lt_dvd divides
  rw [eval_coeff]
  refine ((abs_sum_le_sum_abs ..).trans ?_).trans_lt small
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul,abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) near _) (abs_nonneg _)

/-- A scalar bit budget proves the full-volume inequality without building enormous integers. -/
theorem binary_room {n m r w h : ℕ} (size : n≤2^2048) (dim : r≤2^h)
    (gap : 2048*(m+m.choose 2) + h*r + w*r.choose 2 < 1023*m*r) :
    n^(m+m.choose 2) * (r^r * ((2:ℕ)^w)^(r.choose 2)) < (((2:ℕ)^1023)^m)^r := by
  calc
    _ ≤ ((2:ℕ)^2048)^(m+m.choose 2) * (((2:ℕ)^h)^r * ((2:ℕ)^w)^(r.choose 2)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left size _)
        (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left dim _))
    _ = 2^(2048*(m+m.choose 2)+h*r+w*r.choose 2) := by simp only [← pow_mul,← pow_add]; rw [Nat.add_assoc]
    _ < 2^(1023*m*r) := Nat.pow_lt_pow_right (by decide) gap
    _ = _ := by rw [pow_mul,pow_mul]

/-- Public centers for equally wide blocks of consecutive odd-divisor indices. -/
def center (w i : ℕ) := 2^1023 + 1 + 2*(i*2^(w+1)+2^w)

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 4096 in
theorem odd_address {d w : ℕ} (width : w≤1021) (odd : Odd d) (lo : 2^1023≤d) (hi : d<2^1024) :
    ∃ i : Fin (2^(1021-w)), ∃ x : ℤ, (d:ℤ)=center w i+2*x ∧ |x|≤(2:ℤ)^w := by
  obtain ⟨k,hk⟩ := odd
  let j := k-2^1022
  have l : 2*(2^1022:ℕ)=2^1023 := by decide
  have u : 2*(2^1023:ℕ)=2^1024 := by decide
  have cap : j<2^1022 := by dsimp [j]; omega
  have blocks : (2:ℕ)^(1021-w)*2^(w+1)=2^1022 := by rw [← pow_add]; congr 1; omega
  have ib : j/2^(w+1)<2^(1021-w) := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (blocks ▸ cap)
  let i : Fin (2^(1021-w)) := ⟨j/2^(w+1),ib⟩
  let b := 2^(w+1)
  let r := j%b
  have hr : r<b := Nat.mod_lt _ (by dsimp [b]; positivity)
  have add : r+i.val*b=j := by simpa only [r,i,b,Nat.mul_comm] using Nat.mod_add_div j b
  have step : b=2*2^w := by dsimp [b]; rw [pow_succ,Nat.mul_comm]
  refine ⟨i,(r:ℤ)-(2:ℕ)^w,?_,abs_le.mpr ?_⟩
  · have split : k=2^1022+j := by dsimp [j]; omega
    change (d:ℤ)=((2^1023+1+2*(i.val*b+2^w):ℕ):ℤ)+2*((r:ℤ)-((2:ℕ)^w:ℤ))
    omega
  · have cast : ((2:ℕ)^w:ℤ) = (2:ℤ)^w := by push_cast; rfl
    rw [← cast]
    omega

private theorem anchor (n w i : ℕ) (odd : Odd n) :
    (n:ℤ) ∣ (center w i:ℤ)+2*QuarticDivisorWindow.oddAnchor n (center w i) := by
  obtain ⟨k,hk⟩ := odd
  refine ⟨1,?_⟩
  simp only [QuarticDivisorWindow.oddAnchor,center,Nat.cast_add,Nat.cast_one,Nat.cast_mul,
    Nat.cast_pow,Nat.cast_ofNat,mul_one]
  have ev : (2:ℤ)^1023 = 2*2^1022 := by rw [pow_succ]; ring
  omega

/-- Each address has a polynomial chosen from public parameters. Its checked integer roots
contain every possible divisor in that block. -/
theorem schedule {n m r w h : ℕ} (hn : 0<n) (size : n<2^2048) (parity : Odd n)
    (hr : 0<r) (dim : r≤2^h)
    (gap : 2048*(m+m.choose 2)+h*r+w*r.choose 2<1023*m*r) (i : Fin (2^(1021-w))) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card<r ∧ ∀ x d : ℤ, d ∣ (n:ℤ) →
      d=(center w i:ℤ)+2*x → (2:ℤ)^1023≤d → |x|≤(2:ℤ)^w → F.eval x=0 := by
  let t := QuarticDivisorWindow.oddAnchor n (center w i)
  obtain ⟨v,nz,jets,short⟩ := relation_exists hr hn (by positivity) (by positivity)
    (binary_room size.le dim gap) t
  refine ⟨ofFn r v,nz,?_,?_⟩
  · exact (Multiset.toFinset_card_le _).trans_lt ((Polynomial.card_roots' _).trans_lt
      (ofFn_natDegree_lt hr v))
  · intro x d hd pos lower near
    have unit : IsCoprime (2:ℤ) (n:ℤ) := by exact_mod_cast (Nat.coprime_two_left.mpr parity).isCoprime
    apply root_of_divisor jets hd (QuarticDivisorWindow.progression_offset unit (anchor n w i parity) hd pos)
    · exact_mod_cast near
    · apply short.trans_le
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast lower) m

/-- One choice of polynomial family, based only on public data, covers the entire band. -/
def Cover (n r w : ℕ) : Prop :=
  ∃ F : Fin (2^(1021-w)) → ℤ[X],
    (∀ i, F i ≠ 0 ∧ (F i).roots.toFinset.card<r) ∧
    ∀ d : ℕ, Odd d → 2^1023≤d → d<2^1024 → d∣n →
      ∃ i : Fin (2^(1021-w)), ∃ x : ℤ,
        (d:ℤ)=center w i+2*x ∧ |x|≤(2:ℤ)^w ∧ x∈(F i).roots.toFinset

/-- The first budget is for the finite box proof. In the second budget, j bounds
twice the binary logarithm of the dimension. The inequality is non-strict because
r² is strictly below 2^j. This budget pays for the published LLL first-vector bound. -/
def Scale (m r w h j : ℕ) : Prop :=
  0<r ∧ w≤1021 ∧ r≤2^h ∧ 2048*(m+m.choose 2)+h*r+w*r.choose 2<1023*m*r ∧
    r^2<2^j ∧ j*r+(r-1)*r+4*2048*(m+m.choose 2)+4*w*r.choose 2≤4*1023*m*r

/-- Raise the published bound √r·2^((r−1)/4)·det^(1/r) to the power 4r.
This is the exact integer comparison for the coefficient-scaled lattice determinant.
Only the external first-vector theorem is needed to turn it into an LLL cost guarantee. -/
theorem lll_integer_room {n m r w h j : ℕ} (size : n≤2^2048) (scale : Scale m r w h j) :
    r^(2*r) * (2:ℕ)^((r-1)*r) * (n^(m+m.choose 2) * ((2:ℕ)^w)^(r.choose 2))^4
    < (((2:ℕ)^1023)^m)^(4*r) := by
  obtain ⟨hr,_,_,_,rankBound,budget⟩ := scale
  let T := m+m.choose 2
  let B := r.choose 2
  have first : r^(2*r) < ((2:ℕ)^j)^r := by
    rw [pow_mul]
    exact Nat.pow_lt_pow_left rankBound hr.ne'
  have major : n^T*((2:ℕ)^w)^B ≤ ((2:ℕ)^2048)^T*((2:ℕ)^w)^B :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left size _)
  calc
    _ ≤ r^(2*r) * (2:ℕ)^((r-1)*r) * (((2:ℕ)^2048)^T*((2:ℕ)^w)^B)^4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left major _)
    _ < ((2:ℕ)^j)^r * (2:ℕ)^((r-1)*r) * (((2:ℕ)^2048)^T*((2:ℕ)^w)^B)^4 :=
      Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right first (by positivity)) (by positivity)
    _ = 2^(j*r+(r-1)*r+4*2048*T+4*w*B) := by
      simp only [mul_pow,← pow_mul,← pow_add]
      congr 1
      ring
    _ ≤ 2^(4*1023*m*r) := Nat.pow_le_pow_right (by decide) budget
    _ = _ := by simp only [← pow_mul]; congr 1; ring

theorem public_cover {n m r w h j : ℕ} (hn : 0<n) (size : n<2^2048) (parity : Odd n)
    (scale : Scale m r w h j) : Cover n r w := by
  classical
  obtain ⟨hr,width,dim,gap,_⟩ := scale
  choose F nz count works using schedule hn size parity hr dim gap
  refine ⟨F,fun i => ⟨nz i,count i⟩,?_⟩
  intro d odd lo hi hd
  obtain ⟨i,x,pos,near⟩ := odd_address width odd lo hi
  refine ⟨i,x,pos,near,Multiset.mem_toFinset.mpr ((mem_roots (nz i)).mpr ?_)⟩
  exact works i x d (by exact_mod_cast hd) pos (by exact_mod_cast lo) near

/-- Kernel checks of finite exponents. The last value of the second inequality is an equality. -/
theorem target_scales : Scale 4 9 453 4 7 ∧ Scale 8 17 480 5 9 ∧
    Scale 25 51 500 6 12 ∧ Scale 521 1044 510 11 21 := by
  simp only [Scale,Nat.choose_two_right]
  decide +kernel

theorem target_covers {n : ℕ} (hn : 0<n) (size : n<2^2048) (parity : Odd n) :
    Cover n 9 453 ∧ Cover n 17 480 ∧ Cover n 51 500 ∧ Cover n 1044 510 :=
  ⟨public_cover hn size parity target_scales.1, public_cover hn size parity target_scales.2.1,
    public_cover hn size parity target_scales.2.2.1, public_cover hn size parity target_scales.2.2.2⟩

/-- At radius 2^511 the LLL sufficient exponent fails even before the square-root
dimension factor. This concerns the independent bounds N≤2^2048 and D≥2^1023. -/
theorem radius_511_barrier (m r : ℤ) (hm : 0≤m) :
    4092*m*r ≤ 4096*m*(m+1) + 1023*r*(r-1) := by
  let u := r-2*m
  have consecutive : 0≤u*(u-1) := by
    by_cases h : u≤0
    · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
    · exact mul_nonneg (by omega) (by omega)
  dsimp [u] at consecutive
  nlinarith [sq_nonneg m]

end PrimeFactors.HigherDivisorWindow
