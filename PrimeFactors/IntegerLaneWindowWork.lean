import PrimeFactors.BinomialWindowWork
import Mathlib.Algebra.Group.ForwardDiff

/-! Finite-difference obstruction to dense determinant-certified covers of one
allowed arithmetic progression. Polynomials and their coefficients may vary
freely between windows. -/

namespace PrimeFactors.IntegerLaneWindowWork

open Polynomial Finset Function fwdDiff

private theorem next_coeff {P : ℚ[X]} {i : ℕ} (hd : P.natDegree ≤ i+1) (h : ℚ) :
    (taylor h P-P).coeff i = (i+1:ℕ)*h*P.coeff (i+1) := by
  have small : (hasseDeriv i P).natDegree<2 := by
    have := natDegree_hasseDeriv_le P i
    omega
  rw [coeff_sub,taylor_coeff,eval_eq_sum_range' small]
  simp [sum_range_succ,hasseDeriv_coeff,Nat.add_comm,Nat.choose_succ_self_right]
  ring

private theorem next_degree {P : ℚ[X]} {i : ℕ} (hd : P.natDegree ≤ i+1) (h : ℚ) :
    (taylor h P-P).natDegree ≤ i := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [next_coeff (by omega : P.natDegree≤j+1), coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree<j+1),mul_zero]

/-- The top difference measures precisely the leading coefficient at the
chosen stride. The bound on the degree also permits lower-degree polynomials. -/
theorem top_difference {P : ℚ[X]} {i : ℕ} (hd : P.natDegree ≤ i) (a h : ℚ) :
    (fwdDiff h)^[i] (fun x => P.eval x) a = i.factorial*h^i*P.coeff i := by
  induction i generalizing P with
  | zero =>
    have c : P=C (P.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    simpa only [iterate_zero,id_eq,Nat.factorial_zero,Nat.cast_one,pow_zero,mul_one,one_mul]
      using (show P.eval a=P.coeff 0 by conv_lhs => rw [c,eval_C])
  | succ i ih =>
    rw [iterate_succ_apply]
    have e : fwdDiff h (fun x => P.eval x) = fun x => (taylor h P-P).eval x := by
      funext x
      rw [eval_sub,taylor_eval]; rfl
    rw [e,ih (next_degree hd h),next_coeff hd, Nat.factorial_succ, pow_succ]
    push_cast
    ring

private theorem integer_diff (i : ℕ) (a h : ℚ) (F : ℚ → ℚ)
    (integers : ∀ j ≤ i, ∃ z : ℤ, F (a+j*h)=z) :
    ∃ z : ℤ, (fwdDiff h)^[i] F a=z := by
  choose z hz using integers
  classical
  let Z (j : ℕ) := if hj : j ≤ i then z j hj else 0
  refine ⟨∑ j ∈ range (i+1), ((-1:ℤ)^(i-j)*i.choose j)*Z j,?_⟩
  rw [fwdDiff_iter_eq_sum_shift]
  push_cast
  apply sum_congr rfl
  intro j hj
  have le : j ≤ i := by simpa only [mem_range,Nat.lt_succ_iff] using hj
  simp only [nsmul_eq_mul,zsmul_eq_mul,hz j le,Z,dif_pos le,Int.cast_mul,Int.cast_pow,Int.cast_neg,
    Int.cast_one,Int.cast_natCast]

private theorem bound_diff (i : ℕ) (a h W : ℚ) (F : ℚ → ℚ)
    (small : ∀ j ≤ i, |F (a+j*h)|≤W) :
    |(fwdDiff h)^[i] F a|≤2^i*W := by
  rw [fwdDiff_iter_eq_sum_shift]
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ j ∈ range (i+1), (i.choose j:ℚ)*W := by
      apply sum_le_sum
      intro j hj
      simp only [zsmul_eq_mul,nsmul_eq_mul,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,
        Int.cast_natCast,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_of_nonneg (show 0 ≤ (i.choose j : ℚ) from Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (small j (by simpa only [mem_range,Nat.lt_succ_iff] using hj)) (Nat.cast_nonneg _)
    _ = _ := by rw [←sum_mul]; norm_cast; rw [Nat.sum_range_choose]

/-- Only i+1 small-stride samples need to be integers and i+1 large-stride
samples need a height bound. No restrictions on their common initial offset. -/
theorem column {P : ℚ[X]} {i b W : ℕ} (nz : P≠0) (deg : P.natDegree=i)
    {a h : ℚ} (stride : 0<h)
    (integers : ∀ j ≤ i, ∃ z : ℤ, P.eval (a+j*h)=z)
    (small : ∀ j ≤ i, |P.eval (a+j*((b:ℚ)*h))|≤(W:ℚ)) :
    b^i ≤ 2^i*W := by
  obtain ⟨z,ze⟩ := integer_diff i a h (fun x => P.eval x) integers
  rw [top_difference deg.le] at ze
  have lc : P.coeff i ≠ 0 := by rw [←deg,coeff_natDegree]; exact leadingCoeff_ne_zero.mpr nz
  have zn : z≠0 := by
    intro e
    rw [e,Int.cast_zero] at ze
    exact (mul_ne_zero (mul_ne_zero (by exact_mod_cast i.factorial_ne_zero) (pow_ne_zero i stride.ne')) lc) ze
  have oneZ : (1:ℤ)≤|z| := by
    rcases lt_or_gt_of_ne zn with h|h
    · rw [abs_of_neg h]; omega
    · rw [abs_of_pos h]; omega
  have one : (1:ℚ)≤|(z:ℚ)| := by exact_mod_cast oneZ
  have lifted : (fwdDiff ((b:ℚ)*h))^[i] (fun x => P.eval x) a = (b:ℚ)^i*z := by
    rw [top_difference deg.le,←ze,mul_pow]; ring
  have bound := bound_diff i a ((b:ℚ)*h) (W:ℚ) (fun x => P.eval x) small
  rw [lifted,abs_mul,abs_of_nonneg (by positivity : 0≤(b:ℚ)^i)] at bound
  have lb : (b:ℚ)^i≤(b:ℚ)^i*|((z:ℤ):ℚ)| := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left one (by positivity : 0≤(b:ℚ)^i)
  exact_mod_cast lb.trans bound

/-- The window contains consecutive points in one allowed progression. Only
these finite positions must be integral and satisfy the assigned column heights. -/
structure Lane (k len : ℕ) where
  first : ℚ
  step : ℚ
  positive : 0<step
  poly : Fin (k+1) → ℚ[X]
  nonzero : ∀ i, poly i≠0
  degree : ∀ i, (poly i).natDegree=i.val
  weight : Fin (k+1) → ℕ
  integers : ∀ i (j : ℕ), j<len → ∃ z : ℤ, (poly i).eval (first+j*step)=z
  bounded : ∀ i (j : ℕ), j<len → |(poly i).eval (first+j*step)|≤(weight i:ℚ)

private theorem twice_triangle (k : ℕ) : 2*(k+1).choose 2=k*(k+1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.choose_succ_succ,Nat.choose_one_right]
    nlinarith only [ih]

/-- Retaining the depth in the sufficient determinant inequality gives a
strict budget for the product of arbitrary column weights. -/
theorem fourth_budget {n D m k V : ℕ} (floor : D^2≤n) (depth : m≤k)
    (pass : n^(m+m.choose 2)*V < D^(m*(k+1))) : V^4 < n^(2*m*(k-m)) := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le depth
  rw [Nat.add_sub_cancel_left]
  have T : 2*(m+m.choose 2)=m*(m+1) := by
    simpa only [Nat.choose_succ_succ,Nat.choose_one_right] using twice_triangle m
  have big := (Nat.pow_lt_pow_left pass (by decide : 4≠0)).trans_le
      (show (D^(m*(m+l+1)))^4 ≤ n^(2*m*(m+l+1)) by
        rw [←pow_mul,show m*(m+l+1)*4=2*(2*m*(m+l+1)) by ring,pow_mul]
        exact Nat.pow_le_pow_left floor _)
  have E : 2*m*(m+l+1)=4*(m+m.choose 2)+2*m*l := by nlinarith only [T]
  rw [mul_pow,←pow_mul,E,pow_add, Nat.mul_comm (m+m.choose 2) 4] at big
  exact Nat.lt_of_mul_lt_mul_left big

/-- The fourth root suffices at every degree and depth. -/
theorem fourth_root {n J m k : ℕ} (hn : 0<n) (root : n≤J^4) (depth : m≤k) :
    n^(2*m*(k-m)) ≤ (J^((k+1).choose 2))^4 := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le depth
  rw [Nat.add_sub_cancel_left]
  have bound : 2*m*l ≤ (m+l+1).choose 2 := by
    have z := sq_nonneg ((m:ℤ)-l)
    have T : (2:ℤ)*(((m+l+1).choose 2:ℕ):ℤ)=(m+l:ℕ)*((m+l:ℕ)+1) := by
      exact_mod_cast twice_triangle (m+l)
    push_cast at T
    exact_mod_cast (show (2:ℤ)*m*l≤(((m+l+1).choose 2:ℕ):ℤ) by
      nlinarith only [T,z,Int.natCast_nonneg m,Int.natCast_nonneg l])
  calc
    _ ≤ n^((m+l+1).choose 2) := Nat.pow_le_pow_right hn bound
    _ ≤ (J^4)^((m+l+1).choose 2) := Nat.pow_le_pow_left root _
    _ = _ := by rw [←pow_mul,←pow_mul,Nat.mul_comm 4]

/-- Every admitted window has at most 2Jk positions on one allowed lane. This
also handles windows with fewer than k+1 positions in the lane. -/
theorem lane_count {n D k m len J : ℕ} (w : Lane k len) (hj : 0<J)
    (floor : D^2≤n) (depth : m≤k)
    (pass : n^(m+m.choose 2)*(∏ i,w.weight i)< D^(m*(k+1)))
    (budget : n^(2*m*(k-m)) ≤ (J^((k+1).choose 2))^4) : len ≤ 2*J*k := by
  by_contra! wide
  have each (i : Fin (k+1)) : J^i.val≤w.weight i := by
    have ideg : i.val≤k := by omega
    have jpos : 0<2*J := by omega
    have cap : k<len := (Nat.le_mul_of_pos_left _ jpos).trans_lt wide
    have big := column (b:=2*J) (W:=w.weight i) (w.nonzero i) (w.degree i) w.positive
      (fun j hj => w.integers i j (hj.trans_lt (ideg.trans_lt cap))) (by
        intro j hj
        have inside := (Nat.mul_le_mul_left (2*J) (hj.trans ideg)).trans_lt wide
        have v := w.bounded i ((2*J)*j) inside
        convert v using 3
        push_cast
        ring)
    rw [mul_pow] at big
    exact (Nat.mul_le_mul_left_iff (by positivity)).mp big
  have V := prod_le_prod' (s:=univ) (fun i _ => each i)
  rw [prod_pow_eq_pow_sum,HigherDivisorWindow.weight_sum] at V
  exact (Nat.not_lt_of_ge ((Nat.pow_le_pow_left V 4))).elim
    ((fourth_budget floor depth pass).trans_le budget)

/-- Number of positions on a lane with the first matching residue at offset
off in a block of width consecutive integers. -/
def laneLength (width off stride : ℕ) :=
  if off<width then (width-1-off)/stride+1 else 0

theorem block_width {width off stride : ℕ} (aligned : off<stride) :
    width < stride*(laneLength width off stride+1) := by
  unfold laneLength
  split_ifs with inside
  · have pos : 0<stride := by omega
    have next := Nat.lt_mul_div_succ (width-1-off) pos
    rw [Nat.mul_add,Nat.mul_one]
    omega
  · simpa using (by omega : width<stride)

/-- For any residue class and any placement of both window endpoints, the
total number of consecutive index positions is strictly below this bound. -/
theorem span_bound {n D k m width off stride J : ℕ} (aligned : off<stride)
    (w : Lane k (laneLength width off stride)) (hn : 0<n) (hj : 0<J)
    (floor : D^2≤n) (depth : m≤k) (root : n≤J^4)
    (pass : n^(m+m.choose 2)*(∏ i,w.weight i)<D^(m*(k+1))) :
    width < stride*(2*J*k+1) := by
  have count := lane_count w hj floor depth pass (fourth_root hn root depth)
  exact (block_width aligned).trans_le (Nat.mul_le_mul_left _ (Nat.add_le_add_right count 1))

/-- A dense charge for a family of arbitrary qualifying bases and windows;
each Ico is the block of progression indices covered by that window. -/
theorem cover {ι : Type*} [DecidableEq ι] {n J : ℕ} (hj : 0<J)
    (domain : Finset ℕ) (runs : Finset ι) (start len k m D : ι → ℕ)
    (w : ∀ i, Lane (k i) (len i))
    (full : domain ⊆ runs.biUnion (fun i => Ico (start i) (start i+len i)))
    (passes : ∀ i∈runs, D i^2≤n ∧ m i≤k i ∧
      n^(m i+(m i).choose 2)*(∏ j,(w i).weight j)<D i^(m i*(k i+1)) ∧
      n^(2*m i*(k i-m i))≤(J^((k i+1).choose 2))^4) :
    domain.card ≤ (2*J)*(∑ i ∈ runs,k i) := by
  calc
    _ ≤ _ := (card_le_card full).trans card_biUnion_le
    _ ≤ ∑ i ∈ runs,(2*J)*k i := by
      apply sum_le_sum
      intro i hi
      obtain ⟨floor,depth,pass,budget⟩ := passes i hi
      simpa only [Nat.card_Ico,Nat.add_sub_cancel_left] using lane_count (w i) hj floor depth pass budget
    _ = _ := (mul_sum ..).symm


/-- The public lane d=1+2*s*z in [ceil(N/(2^1024-1)), upper]. -/
noncomputable def domain (n s upper : ℕ) : Finset ℕ :=
  let low := (n+2^1024-2)/(2^1024-1)
  Ico ((low+2*s-2)/(2*s)) ((upper-1)/(2*s)+1)

set_option exponentiation.threshold 65536

/-- Every proposed divisor on this public lane passes the wheel's unit check. -/
theorem candidate_unit (s z : ℕ) : (1+2*s*z).Coprime s := by
  rw [show 2*s*z=s*(2*z) by ring,Nat.coprime_add_mul_left_left]
  exact Nat.coprime_one_left s

/-- The receipt domain is exactly the stated lane of odd divisor candidates. -/
theorem mem_domain {n s upper z : ℕ} (hs : 0<s) (hi : 0<upper) (large : 2^1024≤n) :
    z∈domain n s upper ↔ (n+2^1024-2)/(2^1024-1)≤1+2*s*z ∧ 1+2*s*z≤upper := by
  let low := (n+2^1024-2)/(2^1024-1)
  have pos : 0<2*s := by omega
  have lp : 1≤low := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  change z∈Ico ((low+2*s-2)/(2*s)) ((upper-1)/(2*s)+1) ↔ low≤1+2*s*z ∧ 1+2*s*z≤upper
  rw [mem_Ico,←Nat.lt_succ_iff,Nat.div_lt_iff_lt_mul pos,Nat.lt_succ_iff,Nat.le_div_iff_mul_le pos]
  rw [Nat.succ_mul z (2*s), Nat.mul_comm z (2*s)]
  omega

/-- Uniform degree-six threshold, retaining depth three's exponent of eighteen. -/
theorem seven_budget {n : ℕ} (small : n≤2^2048) :
    n^(2*3*(6-3)) ≤ (((2:ℕ)^439)^((6+1).choose 2))^4 := by
  apply (Nat.pow_le_pow_left small _).trans
  rw [←pow_mul,←pow_mul,←pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by decide)

/-- A seven-row, depth-three invocation accounts for at most 12·2^439
integer positions on any one lane, uniformly across 2,048-bit inputs. -/
theorem seven_cover {ι : Type*} [DecidableEq ι] {n : ℕ} (size : n≤2^2048)
    (positions : Finset ℕ) (runs : Finset ι) (start len D : ι → ℕ)
    (w : ∀ i, Lane 6 (len i))
    (full : positions ⊆ runs.biUnion (fun i => Ico (start i) (start i+len i)))
    (passes : ∀ i∈runs, D i^2≤n ∧ n^6*(∏ j,(w i).weight j)<D i^21) :
    positions.card ≤ (12*2^439)*runs.card := by
  have h := cover (n:=n) (J:=2^439) (by positivity) positions runs start len (fun _ => 6)
    (fun _ => 3) D w full (fun i hi => ⟨(passes i hi).1,(by decide : 3≤6),(passes i hi).2,seven_budget size⟩)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at h
  calc
    _ ≤ _ := h
    _ = _ := by ring

structure Control where
  n : ℕ
  stride : ℕ
  fourth : ℕ
  degreeBits : ℕ
  windowBits : ℕ

def control (fresh smallWheel : Bool) : Control where
  n := if fresh then ChebyshevQuarticScale.fresh else ChebyshevQuarticScale.crossed
  stride := if smallWheel then 3 else 105
  fourth := (if fresh then 3844 else 3551)*2^500
  degreeBits := (if smallWheel then 505 else 500)+(if fresh then 0 else 1)
  windowBits := (if smallWheel then 575 else 570)+(if fresh then 0 else 1)

set_option exponentiation.threshold 12000 in
/-- Public numerical sizes of a common complete lane. The first price measures
degree slots at arbitrary rank. The second measures windows of degree six
and depth three, using J=2^439. -/
theorem control_receipts (fresh smallWheel : Bool) :
    let c := control fresh smallWheel
    2^1024≤c.n ∧ c.n≤2^2048 ∧ c.n≤c.fourth^4 ∧ 0<c.fourth ∧
      (2*c.fourth)*2^c.degreeBits < (domain c.n c.stride c.n.sqrt).card ∧
      (12*2^439)*2^c.windowBits < (domain c.n c.stride c.n.sqrt).card := by
  let n := if fresh then ChebyshevQuarticScale.fresh else ChebyshevQuarticScale.crossed
  let small : ℕ := (if fresh then 57719 else 49228)*2^1008
  have rad : small^2≤n := by cases fresh <;> decide +kernel
  have le : small≤n.sqrt := Nat.le_sqrt.mpr (by simpa only [pow_two] using rad)
  have more (s : ℕ) : (domain n s small).card≤(domain n s n.sqrt).card := by
    simp only [domain,Nat.card_Ico]
    apply Nat.sub_le_sub_right
    exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le_sub_right le 1)) _
  have prices :
      let s : ℕ := if smallWheel then 3 else 105
      let J : ℕ := (if fresh then 3844 else 3551)*2^500
      let e : ℕ := (if smallWheel then 505 else 500)+(if fresh then 0 else 1)
      let ne : ℕ := (if smallWheel then 575 else 570)+(if fresh then 0 else 1)
      2^1024≤n ∧ n≤2^2048 ∧ n≤J^4 ∧ 0<J ∧
        (2*J)*2^e < (domain n s small).card ∧ (12*2^439)*2^ne < (domain n s small).card := by
    dsimp only
    simp only [domain,Nat.card_Ico]
    cases fresh <;> cases smallWheel <;> decide +kernel
  dsimp only [control] at prices ⊢
  exact ⟨prices.1,prices.2.1,prices.2.2.1,prices.2.2.2.1,prices.2.2.2.2.1.trans_le (more _),
    prices.2.2.2.2.2.trans_le (more _)⟩


/-- Final cost of a geometric cover on the two public products. Degrees,
depths, floors, polynomial bases and placements can change at every window. -/
theorem control_degree_work {ι : Type*} [DecidableEq ι] (fresh smallWheel : Bool)
    (runs : Finset ι) (start len k m D : ι → ℕ) (w : ∀ i, Lane (k i) (len i)) :
    let c := control fresh smallWheel
    (domain c.n c.stride c.n.sqrt ⊆ runs.biUnion (fun i => Ico (start i) (start i+len i))) →
    (∀ i∈runs, D i^2≤c.n ∧ m i≤k i ∧
      c.n^(m i+(m i).choose 2)*(∏ j,(w i).weight j)<D i^(m i*(k i+1))) →
    2^c.degreeBits < ∑ i ∈ runs, k i := by
  intro c full passes
  obtain ⟨big,_,root,pos,price,_⟩ := control_receipts fresh smallWheel
  have hn : 0<c.n := (by positivity : 0<(2:ℕ)^1024).trans_le big
  have counts := cover (n:=c.n) pos _ runs start len k m D w full (fun i hi => by
    obtain ⟨floor,depth,pass⟩ := passes i hi
    exact ⟨floor,depth,pass,fourth_root hn root depth⟩)
  exact Nat.lt_of_mul_lt_mul_left (price.trans_le counts)

/-- The number of whole windows needed if every polynomial uses seven rows
and depth three. The comparison counts only the lane d=1+2s*z. -/
theorem control_seven_work {ι : Type*} [DecidableEq ι] (fresh smallWheel : Bool)
    (runs : Finset ι) (start len D : ι → ℕ) (w : ∀ i, Lane 6 (len i)) :
    let c := control fresh smallWheel
    (domain c.n c.stride c.n.sqrt ⊆ runs.biUnion (fun i => Ico (start i) (start i+len i))) →
    (∀ i∈runs, D i^2≤c.n ∧ c.n^6*(∏ j,(w i).weight j)<D i^21) →
    2^c.windowBits < runs.card := by
  intro c full passes
  obtain ⟨_,size,_,_,_,price⟩ := control_receipts fresh smallWheel
  exact Nat.lt_of_mul_lt_mul_left (price.trans_le (seven_cover size _ runs start len D w full passes))

end PrimeFactors.IntegerLaneWindowWork
