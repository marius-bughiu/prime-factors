import PrimeFactors.RectangularRootWindows
import Mathlib.Data.Real.Sqrt

/-! A uniform cost for all positive-index rectangular rows, including empty
rows. Square-root differences telescope the excess over one position per row. -/
namespace PrimeFactors.RectangularRowCost

open Finset

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

/-- All denominator positions on one side of kN, before modular sieves or
testing whether the remaining difference is a square. -/
noncomputable def positions (positive : Bool) (N d B H k : ℕ) : Finset ℕ :=
  (Icc 1 B).filter fun y =>
    if positive then k*N≤d*y^2 ∧ d*y^2≤k*N+H^2 else d*y^2≤k*N ∧ k*N≤d*y^2+H^2

private theorem row_data {positive : Bool} {N d B H k : ℕ}
    (h : (positions positive N d B H k).Nonempty) :
    ∃ u, k*N≤d*u^2+H^2 ∧
      2*d*u*((positions positive N d B H k).card-1)≤H^2 := by
  let s := positions positive N d B H k
  let u := s.min' h
  let v := s.max' h
  have hu := s.min'_mem h
  have hv := s.max'_mem h
  have order : u≤v := s.min'_le _ hv
  have bounds (y : ℕ) (hy : y∈s) := (Finset.mem_filter.mp hy).2
  have atU := bounds u hu
  have atV := bounds v hv
  have lo : k*N≤d*u^2+H^2 := by
    cases positive <;> simp at atU <;> omega
  have width : d*v^2≤d*u^2+H^2 := by
    change (if positive then _ else _) at atU atV
    cases positive <;> simp at atU atV <;> omega
  have sp := RectangularRootWindows.spacing (L:=u) le_rfl order width
  have incl : s ⊆ Icc u v := fun y hy => mem_Icc.mpr ⟨s.min'_le _ hy,s.le_max' _ hy⟩
  have cap := Finset.card_le_card incl
  rw [Nat.card_Icc] at cap
  have ex : s.card-1≤v-u := by omega
  refine ⟨u,lo,?_⟩
  change 2*d*u*(s.card-1)≤_
  calc
    _ ≤ 2*d*u*(v-u) := Nat.mul_le_mul_left _ ex
    _ = d*(2*u)*(v-u) := by ring
    _ ≤ _ := sp

private theorem normalization {N d B H K : ℕ} (np : 0<N) (dp : 0<d)
    (area : H*B≤N) (short : 2*H^2≤N) (last : K*N≤d*B^2+H^2) :
    H^2*K≤2*d*N := by
  apply Nat.le_of_mul_le_mul_right _ np
  calc
    _ = H^2*(K*N) := by ring
    _ ≤ H^2*(d*B^2+H^2) := Nat.mul_le_mul_left _ last
    _ = d*(H*B)^2+(H^2)^2 := by ring
    _ ≤ d*N^2+N^2 := Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left area 2))
      (Nat.pow_le_pow_left (by omega : H^2≤N) 2)
    _ ≤ _ := by nlinarith only [Nat.mul_le_mul_right (N^2) (show 1≤d by omega)]

private theorem weighted {positive : Bool} {N d B H K k : ℕ} (np : 0<N) (dp : 0<d)
    (area : H*B≤N) (short : 2*H^2≤N) (last : K*N≤d*B^2+H^2) (kp : 0<k) :
    Real.sqrt k * Real.sqrt K * (((positions positive N d B H k).card-1:ℕ):ℝ) ≤ H := by
  let s := positions positive N d B H k
  by_cases ne : s.Nonempty
  swap
  · have z : s=∅ := not_nonempty_iff_eq_empty.mp ne
    change _*_*((s.card-1:ℕ):ℝ)≤_
    simp [z]
  obtain ⟨u,low,space⟩ := row_data ne
  have global := normalization np dp area short last
  have lower : k*N≤2*d*u^2 := by
    have kn : N≤k*N := Nat.le_mul_of_pos_left N kp
    nlinarith only [kn,low,short]
  have geometry : H^2*k*K≤(2*d*u)^2 := calc
    _ = (H^2*K)*k := by ring
    _ ≤ (2*d*N)*k := Nat.mul_le_mul_right k global
    _ = (2*d)*(k*N) := by ring
    _ ≤ (2*d)*(2*d*u^2) := Nat.mul_le_mul_left _ lower
    _ = _ := by ring
  have rk := Real.sq_sqrt (show (0:ℝ)≤k by positivity)
  have rK := Real.sq_sqrt (show (0:ℝ)≤K by positivity)
  have scale : (H:ℝ)*Real.sqrt k*Real.sqrt K≤2*d*u := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,mul_pow,rk,rK]
    exact_mod_cast geometry
  let e := (s.card-1:ℕ)
  have sp : (2:ℝ)*d*u*e≤(H:ℝ)^2 := by exact_mod_cast space
  change _*_*((e:ℕ):ℝ)≤_
  by_cases hz : H=0
  · subst H
    have : 0<2*d*u := by
      by_contra! z
      have uz : u=0 := by by_contra! nz; exact (Nat.not_lt_of_ge z) (by positivity)
      simp [uz] at lower
      omega
    have ez : e=0 := by
      change 2*d*u*e≤0^2 at space
      simpa [this.ne'] using space
    simp [ez]
  · apply (mul_le_mul_left (show (0:ℝ)<H by exact_mod_cast Nat.pos_of_ne_zero hz)).mp
    nlinarith only [mul_le_mul_of_nonneg_right scale (show (0:ℝ)≤e by positivity),sp]

private theorem telescope (K H : ℕ) (e : ℕ → ℕ)
    (w : ∀ i∈range K, Real.sqrt (i+1:ℕ)*Real.sqrt K*e (i+1)≤H) :
    (∑ i∈range K, e (i+1))≤2*H := by
  let S (j : ℕ) := Real.sqrt (j:ℝ)
  have diff (i : ℕ) : (S (i+1)+S i)*(S (i+1)-S i)=1 := by
    dsimp [S]
    have a := Real.sq_sqrt (show (0:ℝ)≤(i+1:ℕ) by positivity)
    have b := Real.sq_sqrt (show (0:ℝ)≤ i by positivity)
    push_cast at a ⊢
    nlinarith only [a,b]
  have step (i : ℕ) (hi : i∈range K) :
      S K * e (i+1)≤2*(H:ℝ)*(S (i+1)-S i) := by
    have order : S i≤S (i+1) := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ i)
    have weight := w i hi
    change S (i+1)*S K*e (i+1)≤H at weight
    have nz : 0≤S K*(e (i+1):ℝ) := by dsimp [S]; positivity
    have sum : (S K*e (i+1))*(S (i+1)+S i)≤2*H := by
      nlinarith only [weight,mul_le_mul_of_nonneg_left order nz]
    calc
      _ = ((S K*e (i+1))*(S (i+1)+S i))*(S (i+1)-S i) := by rw [mul_assoc,diff,mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right sum (sub_nonneg.mpr order)
  by_cases kz : K=0
  · simp [kz]
  have pos : 0<S K := Real.sqrt_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero kz)
  have result : ((∑ i∈range K,e (i+1):ℕ):ℝ)≤2*(H:ℝ) := by
    apply (mul_le_mul_left pos).mp
    calc
      _ = ∑ i∈range K, S K*(e (i+1):ℝ) := by push_cast; rw [mul_sum]
      _ ≤ ∑ i∈range K, 2*(H:ℝ)*(S (i+1)-S i) := sum_le_sum step
      _ = _ := by rw [←mul_sum,sum_range_sub]; simp [S,mul_comm]
  exact_mod_cast result

/-- Unsieved coordinate tests over all rows, for either target sign. -/
theorem all_rows (positive : Bool) {N d B H K : ℕ} (np : 0<N) (dp : 0<d)
    (area : H*B≤N) (short : 2*H^2≤N) (last : K*N≤d*B^2+H^2) :
    (∑ i∈range K,(positions positive N d B H (i+1)).card) ≤ K+2*H := by
  let e (k : ℕ) := (positions positive N d B H k).card-1
  have cap := telescope K H e (fun _ _ => weighted np dp area short last (Nat.succ_pos _))
  calc
    _ ≤ ∑ i∈range K, (1+e (i+1)) :=
      sum_le_sum (fun _ _ => by dsimp [e]; omega)
    _ = K + ∑ i∈range K, e (i+1) := by simp [sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_left cap _

/-- Taking B=floor(N/T) and H=floor(N/(B+1)), with T³≥dN, bounds
the row visits by T and the tested positions by 3T. -/
theorem cubic (positive : Bool) {N d B H K T : ℕ} (np : 0<N) (dp : 0<d) (tp : 0<T)
    (box : B=N/T) (height : H=N/(B+1)) (short : 2*H^2≤N)
    (cube : d*N≤T^3) (last : K*N≤d*B^2+H^2) :
    K≤T ∧ (∑ i∈range K,(positions positive N d B H (i+1)).card) ≤ 3*T := by
  have area : H*B≤N := by
    have a := Nat.div_mul_le_self N (B+1)
    rw [←height] at a
    nlinarith only [a,Nat.zero_le H]
  have bt : B*T≤N := by rw [box]; exact Nat.div_mul_le_self ..
  have low : N<(B+1)*T := by
    rw [box,add_mul,one_mul]
    exact Nat.lt_div_mul_add tp
  have ht : H≤T := by
    rw [height]
    apply Nat.le_of_lt
    apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr
    simpa [Nat.mul_comm] using low
  have bd : d*B^2≤T*N := by
    apply Nat.le_of_mul_le_mul_right _ (Nat.pow_pos tp (n:=2))
    calc
      d*B^2*T^2 = d*(B*T)^2 := by ring
      _ ≤ d*N^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left bt 2)
      _ = (d*N)*N := by ring
      _ ≤ T^3*N := Nat.mul_le_mul_right N cube
      _ = T*N*T^2 := by ring
  have strict : H^2<N := by omega
  have kt : K≤T := by
    by_contra! bigger
    have cap := Nat.mul_le_mul_right N (show T+1≤K from bigger)
    nlinarith only [cap,last,bd,strict]
  exact ⟨kt,(all_rows positive np dp area short last).trans (by omega)⟩

/-- At full size the max in the actual B rule always chooses floor(N/T).
The operative index cutoff charges every row of the given sign. -/
theorem full_size (positive : Bool) {N d T : ℕ} (lo : 2^2047≤N) (hi : N<2^2048)
    (dp : 0<d) (ds : d≤6) (lower : (T-1)^3<d*N) (cube : d*N≤T^3) :
    let B := max (N/T) (N.sqrt+1)
    let H := N/(B+1)
    let K := (d*B^2+(if positive then 0 else H^2))/N
    T≤2^684 ∧ K≤T ∧ (∑ i∈range K, (positions positive N d B H (i+1)).card)≤3*T := by
  have np : 0<N := (by positivity : 0<(2:ℕ)^2047).trans_le lo
  have tp : 0<T := by
    by_contra! z
    have tz : T=0 := by omega
    simp [tz] at cube
    omega
  have tcap : T≤2^684 := by
    by_contra! bad
    have past := Nat.pow_le_pow_left (show 2^684≤T-1 by omega) 3
    have maxCube : d*N≤(2^684)^3 := (Nat.mul_le_mul ds hi.le).trans (by decide +kernel)
    omega
  have ns : N.sqrt < 2^1024 := Nat.sqrt_lt.mpr (by simpa only [←pow_add] using hi)
  have enough : (N.sqrt+1)*T≤N :=
    (Nat.mul_le_mul (show N.sqrt+1≤2^1024 from ns) tcap).trans ((by decide +kernel :
      (2:ℕ)^1024*2^684≤2^2047).trans lo)
  have maxEq := max_eq_left ((Nat.le_div_iff_mul_le tp).mpr enough)
  dsimp only
  rw [maxEq]
  let B := N/T
  let H := N/(B+1)
  let K := (d*B^2+(if positive then 0 else H^2))/N
  have ht : H<T := (Nat.div_lt_iff_lt_mul (Nat.succ_pos B)).mpr (Nat.lt_mul_div_succ N tp)
  have short : 2*H^2≤N := (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (ht.le.trans tcap) 2)).trans
    ((by decide +kernel : (2:ℕ)*(2^684)^2≤2^2047).trans lo)
  have last : K*N≤d*B^2+H^2 := (Nat.div_mul_le_self ..).trans
    (by change d*B^2+(if positive then 0 else H^2)≤_; cases positive <;> simp)
  exact ⟨tcap,cubic positive np dp tp (B:=B) (H:=H) (K:=K) rfl rfl short cube last⟩


/-- Every row with j additional positions satisfies k*j² ≤ level. -/
def level (N d H : ℕ) := H^4/(4*d*(N-H^2))

private theorem row_level {positive : Bool} {N d B H k : ℕ} (dp : 0<d) (short : H^2<N)
    (kp : 0<k) :
    k*((positions positive N d B H k).card-1)^2≤level N d H := by
  let s := positions positive N d B H k
  by_cases h : s.Nonempty
  swap
  · have z := not_nonempty_iff_eq_empty.mp h
    change k*(s.card-1)^2≤_
    simp [z]
  obtain ⟨u,lo,sp⟩ := row_data h
  have nk : k*(N-H^2)≤d*u^2 := by
    have eq : k*(N-H^2)+k*H^2=k*N := by rw [←Nat.mul_add,Nat.sub_add_cancel short.le]
    have kh := Nat.le_mul_of_pos_left (H^2) kp
    omega
  let e := s.card-1
  change k*e^2≤level N d H
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.mul_pos (by decide) dp) (Nat.sub_pos_of_lt short))).mpr
  calc
    _ = (4*d*e^2)*(k*(N-H^2)) := by ring
    _ ≤ (4*d*e^2)*(d*u^2) := Nat.mul_le_mul_left _ nk
    _ = (2*d*u*e)^2 := by ring
    _ ≤ (H^2)^2 := Nat.pow_le_pow_left sp 2
    _ = H^4 := by ring

/-- The finite reciprocal-square sum is bounded by 5/3. From j=6 onward
each term is at most 1/(j−1)−1/j. -/
private theorem reciprocal_squares (M : ℕ) :
    (∑ j∈range M, (1:ℚ)/(j+1:ℕ)^2) ≤ 5/3 := by
  let f (j : ℕ) : ℚ := 1/(j+1:ℕ)^2
  change (∑ j∈range M, f j)≤5/3
  rcases lt_or_ge M 5 with small|large
  · interval_cases M <;> norm_num [f,sum_range_succ]
  have bound (m : ℕ) (hm : 5≤m) : (∑ j∈range m, f j)+1/(m:ℚ)≤5/3 := by
    induction m, hm using Nat.le_induction with
    | base => norm_num [f,sum_range_succ]
    | succ n hn ih =>
      have n0 : (0:ℚ)<n := by exact_mod_cast (show 0<n by omega)
      have n1 : (0:ℚ)<n+1 := by positivity
      have tail : f n+1/(n+1:ℕ)≤1/(n:ℚ) := by
        calc
          _ = ((n:ℚ)+2)/((n:ℚ)+1)^2 := by
            dsimp [f]; push_cast; field_simp [n1.ne']; ring
          _ ≤ _ := (div_le_div_iff₀ (by positivity) n0).mpr (by nlinarith)
      rw [sum_range_succ]
      linarith only [ih,tail]
  have pos : 0≤1/(M:ℚ) := by positivity
  linarith only [bound M large,pos]

private theorem level_count {K S : ℕ} (e : ℕ → ℕ) (w : ∀ i∈range K, (i+1)*e i^2≤S) :
    (∑ i∈range K,e i)≤5*S/3 := by
  have height (i : ℕ) (hi : i∈range K) : e i≤S := calc
    _ ≤ e i^2 := Nat.le_self_pow (by decide) _
    _ ≤ (i+1)*e i^2 := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    _ ≤ _ := w i hi
  have below (i : ℕ) (hi : i∈range K) :
      e i = ∑ j∈range S, if j<e i then (1:ℕ) else 0 := by
    rw [sum_boole]
    have eq : (range S).filter (fun j => j<e i)=range (e i) := by
      ext j
      simpa only [mem_filter,mem_range,and_iff_right_iff_imp] using
        (show j<e i → j<S from fun h => h.trans_le (height i hi))
    simp [eq]
  have columns (j : ℕ) :
      (∑ i∈range K, if j<e i then (1:ℕ) else 0)≤S/(j+1)^2 := by
    rw [sum_boole]
    have incl : ((range K).filter (fun i => j<e i)) ⊆ range (S/(j+1)^2) := by
      intro i hi
      obtain ⟨ik,je⟩ := mem_filter.mp hi
      apply mem_range.mpr
      apply (Nat.le_div_iff_mul_le (Nat.pow_pos (Nat.succ_pos j) (n:=2))).mpr
      exact (Nat.mul_le_mul_left (i+1) (Nat.pow_le_pow_left je 2)).trans (w i ik)
    simpa using card_le_card incl
  have sumBound : (∑ i∈range K,e i)≤∑ j∈range S,S/(j+1)^2 := calc
    _ = ∑ i∈range K, ∑ j∈range S, if j<e i then (1:ℕ) else 0 := sum_congr rfl below
    _ = ∑ j∈range S, ∑ i∈range K, if j<e i then (1:ℕ) else 0 := sum_comm
    _ ≤ _ := sum_le_sum fun j _ => columns j
  have term (j : ℕ) : ((S/(j+1)^2:ℕ):ℚ) ≤ (S:ℚ)*(1/(j+1:ℕ)^2) := by
    rw [←mul_div_assoc,mul_one]
    apply (le_div_iff₀ (by positivity)).mpr
    exact_mod_cast Nat.div_mul_le_self S ((j+1)^2)
  have rational : ((∑ j∈range S,S/(j+1)^2:ℕ):ℚ) ≤ (S:ℚ)*(5/3) := by
    push_cast
    calc
      _ ≤ ∑ j∈range S, (S:ℚ)*(1/(j+1:ℕ)^2) := sum_le_sum fun j _ => term j
      _ ≤ _ := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (reciprocal_squares _) (by positivity)
  apply (Nat.le_div_iff_mul_le (by decide)).mpr
  have h : ((∑ j∈range S,S/(j+1)^2:ℕ):ℚ)*3≤5*(S:ℚ) := by linarith only [rational]
  exact (Nat.mul_le_mul_right 3 sumBound).trans (by exact_mod_cast h)

/-- Charging nonempty levels of the row widths gives a tighter numerical
cap. It also applies when the computed level is zero. -/
theorem by_levels (positive : Bool) {N d B H K : ℕ} (dp : 0<d) (short : H^2<N) :
    (∑ i∈range K,(positions positive N d B H (i+1)).card) ≤ K+5*level N d H/3 := by
  let e (i : ℕ) := (positions positive N d B H (i+1)).card-1
  have bound := level_count (K:=K) e (fun i _ => row_level dp short (Nat.succ_pos i))
  calc
    _ ≤ ∑ i∈range K, (1+e i) := sum_le_sum (fun i _ => by dsimp [e]; omega)
    _ = K+∑ i∈range K,e i := by simp [sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_left bound _

end PrimeFactors.RectangularRowCost
