import PrimeFactors.OffsetTangentCover
import PrimeFactors.GroupedOffsetRowExamples
import Mathlib.Data.Nat.Log

set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

namespace PrimeFactors.OffsetGlobalArcs
open Finset

/-- The coordinate bin starts at 2^a, and the offset-index epoch at 2^b.
A chunk has 2^w *positions*, so width zero also has a place in the partition. -/
def chunkExp (a b : ℕ) := min b (min (4*a-1) (a+b/2-174))

theorem dyadic_bin {i cutoff : ℕ} (pos : 0 < i) (limit : i < 2^cutoff) :
    ∃ a < cutoff, 2^a ≤ i ∧ i < 2^(a+1) := by
  let a := Nat.log 2 i
  have le : 2^a ≤ i := Nat.pow_log_le_self 2 (by omega)
  have lt := Nat.lt_pow_succ_log_self (by decide : 1 < 2) i
  exact ⟨a,by
    by_contra! h
    exact (Nat.not_le_of_gt limit) ((Nat.pow_le_pow_right (by decide) h).trans le),le,lt⟩

/-- Address any index in an epoch by its chunk and its position inside that chunk. -/
theorem partition {a b i : ℕ} (left : 2^b ≤ i) (right : i < 2^(b+1)) :
    ∃ c < 2^(b-chunkExp a b), ∃ r < 2^(chunkExp a b),
      i=2^b+c*2^(chunkExp a b)+r := by
  let w := chunkExp a b
  have wle : w ≤ b := min_le_left ..
  have pw : 0 < 2^w := by positivity
  have identity : 2^(b-w)*2^w=2^b := by rw [←pow_add,Nat.sub_add_cancel wle]
  have short : i-2^b < 2^b := by rw [pow_succ] at right; omega
  refine ⟨(i-2^b)/2^w,(Nat.div_lt_iff_lt_mul pw).mpr (identity.symm ▸ short),
    (i-2^b)%2^w,Nat.mod_lt _ pw,?_⟩
  have div := Nat.mod_add_div (i-2^b) (2^w)
  change i=2^b+(i-2^b)/2^w*2^w+(i-2^b)%2^w
  rw [Nat.mul_comm ((i-2^b)/2^w)]
  omega

/-- At an index inside this epoch the first nonnegative discriminant supplies a
lower bound for the floor root, without locating either factor. -/
theorem height {a b T k A P i : ℕ} (large : 2^1022 ≤ T) (scale : 2^(2*a) ≤ k)
    (base : P ≤ A^2) (initial : T*k ≤ A) (epoch : 2^b ≤ i) :
    2^(511+a+b/2) ≤ ((A+2*i)^2-P).sqrt := by
  apply Nat.le_sqrt'.mpr
  have expo : 2*(511+a+b/2) ≤ 1022+2*a+b := by omega
  have prod : 2^1022*2^(2*a)*2^b ≤ T*k*i := Nat.mul_le_mul (Nat.mul_le_mul large scale) epoch
  have mid : (2^(511+a+b/2))^2 ≤ A*i := by
    calc (2^(511+a+b/2))^2 = 2^(2*(511+a+b/2)) := by rw [←pow_mul,Nat.mul_comm]
         _ ≤ 2^(1022+2*a+b) := Nat.pow_le_pow_right (by decide) expo
         _ = 2^1022*2^(2*a)*2^b := by rw [pow_add,pow_add]
         _ ≤ A*i := prod.trans (Nat.mul_le_mul_right _ initial)
  apply Nat.le_sub_of_add_le
  nlinarith only [mid,base]

/-- One power-of-two bound absorbs the dependence on k² in the curvature test. -/
theorem curvature_budget {N k u : ℕ} (n : N ≤ 2^2048) (kp : 0 < k) (up : u ≤ 2^1026*k) :
    4*N*k^2+2*u ≤ 2^2051*k^2 := by
  have kk : k ≤ k^2 := by nlinarith only [Nat.mul_le_mul_left k (show 1 ≤ k by omega)]
  have ucap := up.trans (Nat.mul_le_mul_left (2^1026) kk)
  calc 4*N*k^2+2*u ≤ (4*2^2048+2*2^1026)*k^2 := by
         nlinarith only [Nat.mul_le_mul_right (k^2) n,ucap]
       _ ≤ 2^2051*k^2 := Nat.mul_le_mul_right _ (by decide +kernel)

/-- Every chunk satisfies the rounding and curvature hypotheses on the basic parity chart. -/
theorem chunk_thin {a b W k u P : ℕ} (width : W < 2^(chunkExp a b))
    (scale : 2^(2*a) ≤ k) (height : 2^(511+a+b/2) ≤ u) (product : P+2*u ≤ 2^2051*k^2) :
    8*W ≤ 4*k^2 ∧ 4*(P+2*u)*2^2*W^3 ≤ 4*k^2*u^3 := by
  let w := chunkExp a b
  by_cases z : w=0
  · change W < 2^w at width
    have : W=0 := by simpa [z] using width
    simp [this]
  · have nonz : 0 < chunkExp a b := by omega
    have sep : w+1 ≤ 4*a ∧ 685+w ≤ 511+a+b/2 := by
      dsimp [w,chunkExp] at *
      omega
    have ra : 2*W ≤ k^2 := by
      calc 2*W ≤ 2*2^w := Nat.mul_le_mul_left _ width.le
           _ = 2^(w+1) := by rw [pow_succ,Nat.mul_comm]
           _ ≤ 2^(4*a) := Nat.pow_le_pow_right (by decide) sep.1
           _ = (2^(2*a))^2 := by rw [←pow_mul]; congr 1; omega
           _ ≤ k^2 := Nat.pow_le_pow_left scale _
    have cv : 2^685*W ≤ u := by
      calc 2^685*W ≤ 2^685*2^w := Nat.mul_le_mul_left _ width.le
           _ = 2^(685+w) := (pow_add ..).symm
           _ ≤ 2^(511+a+b/2) := Nat.pow_le_pow_right (by decide) sep.2
           _ ≤ u := height
    refine ⟨by omega,?_⟩
    calc 4*(P+2*u)*2^2*W^3 ≤ 4*k^2*((2^685*W)^3) := by
           have h := Nat.mul_le_mul_right (W^3) product
           have h' := Nat.mul_le_mul_left (k^2*W^3) (show 4*2^2051 ≤ (2^685)^3 by decide +kernel)
           nlinarith only [h,h']
         _ ≤ 4*k^2*u^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left cv _)

/-- The v and s indices fit a rectangle of 2^(2a+2) addresses. -/
theorem coordinate_bin {a s v : ℕ} (left : 2^a ≤ v) (right : v < 2^(a+1)) (smax : s ≤ 2*v+1)
    (le : v ≤ s) : v-2^a < 2^a ∧ s < 2^(a+2) ∧ 2^(2*a) ≤ s*v := by
  have scale : 2^(2*a) ≤ s*v := by
    rw [show 2*a=a+a by omega,pow_add]
    exact Nat.mul_le_mul (left.trans le) left
  rw [pow_succ] at right
  rw [show a+2=a+1+1 by omega,pow_succ,pow_succ]
  exact ⟨by omega,by omega,scale⟩

/-- The public rectangular enumeration includes all actual coordinates in a bin. -/
noncomputable def coordinateBox (a : ℕ) : Finset (ℕ × ℕ) :=
  (Ico (2^a) (2^(a+1))) ×ˢ range (2^(a+2))

theorem coordinateBox_card (a : ℕ) : (coordinateBox a).card=2^(2*a+2) := by
  simp only [coordinateBox,card_product,Nat.card_Ico,card_range]
  have diff : 2^(a+1)-2^a=2^a := by rw [pow_succ]; omega
  rw [diff,←pow_add]
  congr 1
  omega

theorem coordinateBox_mem {a s v : ℕ} (left : 2^a ≤ v) (right : v < 2^(a+1))
    (smax : s≤2*v+1) (le : v≤s) : (v,s)∈coordinateBox a := by
  exact mem_product.mpr ⟨mem_Ico.mpr ⟨left,right⟩,mem_range.mpr
    (coordinate_bin left right smax le).2.1⟩

/-- A deliberately rectangular envelope for the total number of line equations.
The initial single index is included per coordinate bin, and both signs count. -/
noncomputable def total (na nb : ℕ) : ℕ :=
  2 * ∑ a ∈ range na, (2^(2*a+2) + ∑ b ∈ range nb, 2^(2*a+2+(b-chunkExp a b)))

private theorem width_exponent {a b : ℕ} (va : a ≤ 257) (vb : b ≤ 514) :
    2*a+2+(b-chunkExp a b) ≤ 690 := by
  unfold chunkExp
  omega

/-- A uniform count when v < 2^258 and the positive parity index is below 2^515. -/
theorem total_bound {na nb : ℕ} (ha : na ≤ 258) (hb : nb ≤ 515) : total na nb < 2^710 := by
  unfold total
  have row (a : ℕ) (va : a < na) :
      2^(2*a+2)+(∑ b ∈ range nb, 2^(2*a+2+(b-chunkExp a b))) ≤ 2^516+515*2^690 := by
    have h := sum_le_sum (s:=range nb) (g:=fun _ => 2^690)
      (fun b (mem : b∈range nb) =>
        Nat.pow_le_pow_right (by decide : 0 < 2) (width_exponent (by omega : a ≤ 257)
          (by have := mem_range.mp mem; omega : b ≤ 514)))
    simpa using Nat.add_le_add (Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 2*a+2 ≤ 516 by omega)) (h.trans (by simpa only [Finset.sum_const,card_range,smul_eq_mul] using Nat.mul_le_mul_right (2^690) hb))
  have h := sum_le_sum (s:=range na) (g:=fun _ => 2^516+515*2^690)
    (fun a (mem : a∈range na) => row a (mem_range.mp mem))
  have lim : (∑ a ∈ range na, (2^(2*a+2)+(∑ b ∈ range nb, 2^(2*a+2+(b-chunkExp a b))))) ≤ 258*(2^516+515*2^690) := h.trans (by simpa only [Finset.sum_const,card_range,smul_eq_mul] using Nat.mul_le_mul_right (2^516+515*2^690) ha)
  exact (Nat.mul_le_mul_left 2 lim).trans_lt (by decide +kernel)


/-- The floor root at an actual trace is no larger than that trace. -/
theorem upper_height {S P T j k : ℕ} (eqn : S=2*T*k+j) (tp : T≤2^1024)
    (jp : j≤2^515) (kp : 0<k) : (S^2-P).sqrt≤2^1026*k := by
  have small : (S^2-P).sqrt ≤ S := by
    apply Nat.le_of_lt_succ
    apply Nat.sqrt_lt'.mpr
    exact (Nat.sub_le _ _).trans_lt (by nlinarith only [Nat.zero_le S] : S^2<(S+1)^2)
  have growth := Nat.mul_le_mul_right k tp
  have bound : j≤2^515*k := jp.trans (Nat.le_mul_of_pos_right _ kp)
  have C := Nat.mul_le_mul_right k (show 2*2^1024+2^515≤2^1026 by decide +kernel)
  apply small.trans
  rw [eqn]
  nlinarith only [growth,bound,C]

/-- These product-only conditions suffice for the two sharper coordinate cutoffs. -/
def FixtureBounds (N T : ℕ) : Prop :=
  2^1022≤T ∧ T<2^1024 ∧ N<2^2048 ∧ T<2*(N-T^2) ∧ 4*(N-T^2)<3*(2^512)^2

theorem fresh_parameters : FixtureBounds ChebyshevQuarticScale.fresh ChebyshevQuarticScale.fresh.sqrt := by
  rw [show ChebyshevQuarticScale.fresh.sqrt=GroupedOffsetRowExamples.fresh.T from
    GroupedOffsetRowExamples.fresh_row.1]
  unfold FixtureBounds
  decide +kernel

theorem crossed_parameters : FixtureBounds ChebyshevQuarticScale.crossed ChebyshevQuarticScale.crossed.sqrt := by
  rw [show ChebyshevQuarticScale.crossed.sqrt=GroupedOffsetRowExamples.crossed.T from
    GroupedOffsetRowExamples.crossed_row.1]
  unfold FixtureBounds
  decide +kernel

theorem fixture_caps {N T J : ℕ} (par : FixtureBounds N T) (sharp : 3*J^2≤4*(N-T^2)) :
    J<2^512 ∧ T*J/(N-T^2)+1<2^513 := by
  obtain ⟨large,_,_,ratio,cap⟩ := par
  have jlim : J<2^512 := by
    by_contra! big
    have sq := Nat.pow_le_pow_left big 2
    nlinarith only [sharp,cap,sq]
  have hp : 0<N-T^2 := by omega
  have bound : T*J/(N-T^2)≤2*J := by
    apply Nat.div_le_of_le_mul
    calc T*J ≤ 2*(N-T^2)*J := Nat.mul_le_mul_right J ratio.le
         _ = _ := by ring
  exact ⟨jlim,by omega⟩

/-- Every admissible coordinate satisfies the stated aspect bound. -/
theorem aspect {s v T L : ℕ} (top : T≤2*L) (window : L*(s-1)<T*v) : s≤2*v := by
  by_contra! bad
  have h := Nat.mul_le_mul_left L (show 2*v≤s-1 by omega)
  nlinarith only [h,window,Nat.mul_le_mul_right v top]

theorem v_limit {v s e : ℕ} (ord : v≤s) (cap : s*v<2^(2*e)) : v<2^e := by
  by_contra! h
  have big := Nat.mul_le_mul (h.trans ord) h
  rw [show 2*e=e+e by omega,pow_add] at cap
  omega

/-- Substitution of the dyadic widths into the rounded tangent theorem on a full parity
chart. A width-zero chunk consists of one trace, tested directly. -/
theorem chunk_line {a b i W k A T N j : ℕ} (r β : ℤ)
    (large : 2^1022≤T) (top : T≤2^1024) (nmax : N≤2^2048) (jp : j≤2^515)
    (scale : 2^(2*a)≤k) (initial : T*k≤A) (base : 4*N*k^2≤A^2)
    (trace : A+2*i=2*T*k+j) (epoch : 2^b ≤ i) (wp : 0<W) (width : W<2^(chunkExp a b)) :
    ∃ (q : ℕ) (p t : ℤ), 1≤q ∧ q≤2*W ∧ ∀ x y w : ℤ, 0 ≤ x → x ≤ W → 0 ≤ w →
      w=r+β*x+((4*k^2:ℕ):ℤ)*y →
      w^2=(((A+2*i:ℕ):ℤ)+2*x)^2-((4*N*k^2:ℕ):ℤ) → (q:ℤ)*y-p*x=t := by
  let P := 4*N*k^2
  let S := A+2*i
  let u := (S^2-P).sqrt
  have kp : 0<k := lt_of_lt_of_le (by positivity : 0<(2:ℕ)^(2*a)) scale
  have lower : 2^(511+a+b/2)≤u := height large scale base initial epoch
  have up : 0<u := lt_of_lt_of_le (by positivity : 0<(2:ℕ)^(511+a+b/2)) lower
  have hcut := chunk_thin width scale lower (curvature_budget nmax kp (upper_height trace top jp kp))
  have base' : P≤S^2 := base.trans (Nat.pow_le_pow_left (Nat.le_add_right A _) 2)
  have hsq : u^2≤S^2-P := Nat.sqrt_le' _
  have hnext : S^2-P<(u+1)^2 := Nat.lt_succ_sqrt' _
  let e := S^2-P-u^2
  have eid : S^2=P+u^2+e := by dsimp [e]; omega
  have esize : e≤2*u := by
    have eq : S^2-P=u^2+e := by omega
    nlinarith only [eq,hnext]
  have h : (S:ℤ)^2-(P:ℤ)=(u:ℤ)^2+e := by
    have he : (S:ℤ)^2=(P:ℤ)+(u:ℤ)^2+e := by exact_mod_cast eid
    linarith only [he]
  apply OffsetTangentCover.one_line (e:=(e:ℤ)) (u:=(u:ℤ)) (by positivity) (by exact_mod_cast up)
    (by positivity) (by exact_mod_cast esize) (by positivity) (by decide) (by positivity) wp h
  · exact_mod_cast hcut.1
  · exact_mod_cast hcut.2

private theorem powers (n : ℕ) : (∑ i ∈ range n, 2^i)+1=2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,pow_succ]
    omega

private theorem half_powers (n : ℕ) :
    (∑ b ∈ range (2*n), 2^((b+1)/2))+3=3*2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,sum_range_succ,sum_range_succ,
      show (2*n+1+1)/2=n+1 by omega,show (2*n+1)/2=n by omega,pow_succ]
    omega

/-- Summing the dependence on both bin indices gives the sharper finite majorant. -/
theorem geometric_total {na nb m : ℕ} (ha : na≤258) (hb : nb≤515) (half : nb≤2*m) :
    total na nb ≤ 2*(na*(2^516+nb*2^516)+(2^176*(3*2^m))*2^na) := by
  have per {a b : ℕ} (av : a<na) (bv : b<nb) :
      2^(2*a+2+(b-chunkExp a b)) ≤ 2^516+(2^176*2^a)*2^((b+1)/2) := by
    rw [←pow_add,←pow_add]
    have ex : 2*a+2+(b-chunkExp a b) ≤ max 516 (176+a+(b+1)/2) := by
      unfold chunkExp
      omega
    rcases le_max_iff.mp ex with h|h
    · exact (Nat.pow_le_pow_right (by decide : 0<2) h).trans (Nat.le_add_right ..)
    · exact (Nat.pow_le_pow_right (by decide : 0<2) h).trans (Nat.le_add_left ..)
  have sumB : (∑ b ∈ range nb, 2^((b+1)/2)) ≤ 3*2^m := by
    have big := half_powers m
    exact (sum_le_sum_of_subset (f:=fun b => 2^((b+1)/2)) (range_mono half)).trans (by omega)
  have row {a : ℕ} (av : a<na) :
      2^(2*a+2)+(∑ b ∈ range nb, 2^(2*a+2+(b-chunkExp a b))) ≤
      (2^516+nb*2^516)+(2^176*(3*2^m))*2^a := by
    have bd := sum_le_sum (s:=range nb) (fun b mem => per av (mem_range.mp mem))
    rw [sum_add_distrib,←mul_sum] at bd
    simp only [sum_const,card_range,smul_eq_mul] at bd
    have first := Nat.pow_le_pow_right (by decide : 0<2) (show 2*a+2≤516 by omega)
    have replace := Nat.mul_le_mul_left (2^176*2^a) sumB
    linarith only [bd,first,replace]
  have bd := sum_le_sum (s:=range na) (fun a mem => row (a:=a) (mem_range.mp mem))
  conv_rhs at bd => rw [sum_add_distrib,←mul_sum]
  simp only [sum_const,card_range,smul_eq_mul] at bd
  have sumA : (∑ a ∈ range na, 2^a) ≤ 2^na := by have h := powers na; omega
  exact Nat.mul_le_mul_left 2 (bd.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ sumA) _))

theorem standard_grid : total 258 515 < 2^695 :=
  (geometric_total (m:=258) (by decide) (by decide) (by decide)).trans_lt (by decide +kernel)

theorem control_grid : total 257 512 < 2^692 :=
  (geometric_total (m:=256) (by decide) (by decide) (by decide)).trans_lt (by decide +kernel)

end PrimeFactors.OffsetGlobalArcs
