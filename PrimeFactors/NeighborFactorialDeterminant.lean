import PrimeFactors.Fermat
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Nat.Factorial.Cast
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-! Consecutive starting positions in a determinant of interval products.
A column has width j+hⱼ, where the nondecreasing slack h parametrizes
all strictly increasing lists of nonnegative widths. -/
namespace PrimeFactors.NeighborFactorialDeterminant
open Finset Matrix

def width {r : ℕ} (h : Fin r → ℕ) (j : Fin r) := j.val + h j

noncomputable def table {r : ℕ} (x : ℕ) (h : Fin r → ℕ) : Matrix (Fin r) (Fin r) ℤ :=
  fun i j => ((x+i.val).ascFactorial (width h j) : ℤ)

noncomputable def gaps {r : ℕ} (h : Fin r → ℕ) : ℕ :=
  ∏ i, ∏ j ∈ Ioi i, (width h j - width h i)

private theorem gap_cast {r : ℕ} {h : Fin r → ℕ} (sorted : Monotone h) :
    (gaps h : ℤ) = ∏ i, ∏ j ∈ Ioi i, ((width h j : ℤ) - width h i) := by
  unfold gaps
  push_cast
  apply prod_congr rfl
  intro i _
  apply prod_congr rfl
  intro j hij
  have le := (mem_Ioi.mp hij).le
  exact Nat.cast_sub (Nat.add_le_add le (sorted le))

/-- The neighboring factorial determinant is a product of width differences
and ordinary shorter interval products. The equality holds in the integers,
so no assumption about invertibility modulo the factoring input is needed. -/
theorem determinant {r : ℕ} {x : ℕ} (xp : 0<x) (h : Fin r → ℕ) (sorted : Monotone h) :
    (table x h).det = ((gaps h * ∏ j, (x+j.val).ascFactorial (h j) : ℕ) : ℤ) := by
  classical
  let A := table x h
  let pref (i : Fin r) : ℤ := x.ascFactorial i.val
  let col (j : Fin r) : ℤ := x.ascFactorial (width h j)
  let rest (j : Fin r) : ℤ := (x+j.val).ascFactorial (h j)
  let node (j : Fin r) : ℤ := (x + width h j : ℕ)
  let V : Matrix (Fin r) (Fin r) ℤ := fun i j => ((x+width h j).ascFactorial i.val : ℤ)
  have scaled : Matrix.of (fun i j => pref i*A i j) = Matrix.of (fun i j => col j*V i j) := by
    ext i j
    change (x.ascFactorial i.val : ℤ)*((x+i.val).ascFactorial (width h j) : ℤ) =
      (x.ascFactorial (width h j) : ℤ)*((x+width h j).ascFactorial i.val : ℤ)
    norm_cast
    rw [Nat.ascFactorial_mul_ascFactorial,Nat.ascFactorial_mul_ascFactorial,Nat.add_comm i.val]
  have form : V.det = gaps h := by
    let p (i : Fin r) := ascPochhammer ℤ i.val
    have ev : V.transpose = Matrix.of (fun i j => (p j).eval (node i)) := by
      ext i j
      exact Nat.cast_ascFactorial ℤ _ _
    rw [←Matrix.det_transpose,ev,←Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde node p
      (fun i => ascPochhammer_natDegree ℤ i.val) (fun _ => monic_ascPochhammer ..),Matrix.det_vandermonde,gap_cast sorted]
    simp only [node,Nat.cast_add,add_sub_add_left_eq_sub]
  have c (j : Fin r) : col j=pref j*rest j := by
    dsimp [col,pref,rest,width]
    exact_mod_cast (Nat.ascFactorial_mul_ascFactorial x j.val (h j)).symm
  have cp : ∏ j, col j = (∏ i, pref i)*∏ j,rest j := by simp [c,prod_mul_distrib]
  have pos (i : Fin r) : pref i≠0 := by
    obtain ⟨z,rfl⟩ := Nat.exists_eq_succ_of_ne_zero xp.ne'
    dsimp [pref]
    exact_mod_cast (Nat.ascFactorial_pos z i.val).ne'
  have nz : (∏ i, pref i) ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => pos i)
  have scaled_det := congrArg Matrix.det scaled
  rw [Matrix.det_mul_column,Matrix.det_mul_row,cp,form] at scaled_det
  apply mul_left_cancel₀ nz
  push_cast
  exact scaled_det.trans (by dsimp [rest]; ring)

private theorem divides_rising {p : ℕ} (prime : p.Prime) (x n : ℕ) :
    p ∣ x.ascFactorial n ↔ ∃ k < n, p ∣ x+k := by
  rw [Nat.ascFactorial_eq_prod_range,prime.prime.dvd_finset_prod_iff]
  simp

/-- After the first nonzero slack s, the union of all residual intervals has
no holes. This includes repeated visits to the same candidate position. -/
theorem offsets {r : ℕ} (h : Fin (r+1) → ℕ) (sorted : Monotone h) (s : Fin (r+1))
    (before : ∀ j < s, h j=0) (first : 0 < h s) (k : ℕ) :
    (∃ j : Fin (r+1), j.val ≤ k ∧ k < width h j) ↔
      s.val ≤ k ∧ k < width h (Fin.last r) := by
  constructor
  · rintro ⟨j,lo,hi⟩
    have sj : s ≤ j := by
      by_contra! early
      simp [width,before j early] at hi
      omega
    exact ⟨le_trans (show s.val ≤ j.val from sj) lo,
      hi.trans_le (Nat.add_le_add (Fin.le_last j) (sorted (Fin.le_last j)))⟩
  · rintro ⟨lo,hi⟩
    by_cases small : k ≤ r
    · let j : Fin (r+1) := ⟨k,by omega⟩
      have hj : 0 < h j := first.trans_le (sorted (show s ≤ j from lo))
      exact ⟨j,le_rfl,Nat.lt_add_of_pos_right hj⟩
    · exact ⟨Fin.last r,by simpa only [Fin.val_last] using le_of_not_ge small,hi⟩

/-- Divisibility by each prime agrees with a single ordinary interval product
times the public product of width differences. -/
theorem prime_support {r x p : ℕ} (prime : p.Prime) (xp : 0<x) (h : Fin (r+1) → ℕ)
    (sorted : Monotone h) (s : Fin (r+1)) (before : ∀ j < s, h j=0) (first : 0<h s) :
    p ∣ (table x h).det.natAbs ↔ p ∣ gaps h * (x+s.val).ascFactorial (width h (Fin.last r)-s.val) := by
  rw [determinant xp h sorted,Int.natAbs_ofNat,prime.dvd_mul,prime.dvd_mul]
  apply or_congr_right
  rw [prime.prime.dvd_finset_prod_iff,divides_rising prime]
  constructor
  · rintro ⟨j,_,hj⟩
    obtain ⟨i,within,div⟩ := (divides_rising prime _ _).mp hj
    let k := j.val+i
    obtain ⟨lo,hi⟩ := (offsets h sorted s before first k).mp
      ⟨j,Nat.le_add_right _ _,Nat.add_lt_add_left within _⟩
    exact ⟨k-s.val,by omega,by simpa only [show x+s.val+(k-s.val)=x+j.val+i by dsimp [k] at *; omega] using div⟩
  · rintro ⟨i,within,div⟩
    let k := s.val+i
    obtain ⟨j,lo,hi⟩ := (offsets h sorted s before first k).mpr
      ⟨Nat.le_add_right _ _,by dsimp [k]; omega⟩
    refine ⟨j,mem_univ _,(divides_rising prime _ _).mpr ⟨k-j.val,?_,?_⟩⟩
    · unfold width at hi
      omega
    · simpa only [show x+j.val+(k-j.val)=x+s.val+i by dsimp [k] at *; omega] using div

/-- The gcd agrees exactly, including saturation at both distinct primes. -/
theorem semiprime_gcd {r x p q : ℕ} (pp : p.Prime) (qp : q.Prime) (diff : p≠q)
    (xp : 0<x) (h : Fin (r+1) → ℕ) (sorted : Monotone h) (s : Fin (r+1))
    (before : ∀ j < s, h j=0) (first : 0<h s) :
    (table x h).det.natAbs.gcd (p*q) =
      (gaps h * (x+s.val).ascFactorial (width h (Fin.last r)-s.val)).gcd (p*q) := by
  let a := (table x h).det.natAbs
  let b := gaps h * (x+s.val).ascFactorial (width h (Fin.last r)-s.val)
  have eq {l : ℕ} (prime : l.Prime) : a.gcd l=b.gcd l := by
    have iff : l∣a ↔ l∣b := prime_support prime xp h sorted s before first
    by_cases yes : l∣a
    · rw [Nat.gcd_eq_right yes,Nat.gcd_eq_right (iff.mp yes)]
    · rw [(prime.coprime_iff_not_dvd.mpr yes).symm.gcd_eq_one,
        (prime.coprime_iff_not_dvd.mpr (mt iff.mpr yes)).symm.gcd_eq_one]
  have cop := (Nat.coprime_primes pp qp).mpr diff
  change a.gcd (p*q)=b.gcd (p*q)
  rw [cop.gcd_mul,cop.gcd_mul,eq pp,eq qp]

/-- Three rows with offsets 0,1,3 and column widths 0,1,w. -/
noncomputable def skipped (x w : ℕ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1,(x:ℤ),(x.ascFactorial w:ℤ);
     1,((x+1:ℕ):ℤ),((x+1).ascFactorial w:ℤ);
     1,((x+3:ℕ):ℤ),((x+3).ascFactorial w:ℤ)]

/-- Skipping exactly one start in this three-row test adds one affine
candidate outside the common interval. Here w=v+3. -/
theorem skipped_det (x v : ℕ) : (skipped x (v+3)).det =
    (((v+3)*(v+2)*(x+3).ascFactorial v*(3*x+v+7) : ℕ) : ℤ) := by
  have first : x.ascFactorial (v+3)=x.ascFactorial 3*(x+3).ascFactorial v := by
    rw [Nat.ascFactorial_mul_ascFactorial,Nat.add_comm]
  have second : (x+1).ascFactorial (v+3) =
      (x+1).ascFactorial 2*((x+3+v)*(x+3).ascFactorial v) := by
    rw [←Nat.ascFactorial_succ,show x+3=x+1+2 by omega,Nat.ascFactorial_mul_ascFactorial]
    congr 1; omega
  have last : (x+3).ascFactorial (v+3) =
      (x+3).ascFactorial v*(x+3+v).ascFactorial 3 := (Nat.ascFactorial_mul_ascFactorial ..).symm
  rw [Matrix.det_fin_three]
  change 1*((x+1:ℕ):ℤ)*((x+3).ascFactorial (v+3):ℤ) -
    1*((x+1).ascFactorial (v+3):ℤ)*((x+3:ℕ):ℤ) - (x:ℤ)*1*((x+3).ascFactorial (v+3):ℤ) +
    (x:ℤ)*((x+1).ascFactorial (v+3):ℤ)*1 + (x.ascFactorial (v+3):ℤ)*1*((x+3:ℕ):ℤ) -
    (x.ascFactorial (v+3):ℤ)*((x+1:ℕ):ℤ)*1 = _
  simp only [first,second,last,Nat.ascFactorial_succ,Nat.ascFactorial_zero,Nat.mul_one,Nat.add_zero]
  push_cast
  ring

set_option maxRecDepth 8192 in
/-- The whole union of the three original width-six rows is coprime to 2183.
The extra affine value 148 reveals 37, the same divisor as the skipped-row determinant. -/
theorem example_2183 :
    Nat.sqrt 2183 = 46 ∧ ((46:ℕ).ascFactorial 9).gcd 2183 = 1 ∧
    (3*46+6+4).gcd 2183 = 37 ∧ (skipped 46 6).det.natAbs.gcd 2183 = 37 ∧
    37*59 = 2183 ∧ Nat.Prime 37 ∧ Nat.Prime 59 := by
  have root : Nat.sqrt 2183=46 := le_antisymm
    (Nat.lt_succ_iff.mp (Nat.sqrt_lt'.mpr (by decide : 2183<47^2))) (Nat.le_sqrt'.mpr (by decide))
  refine ⟨root,?_,by decide,?_,by decide,by norm_num1,by norm_num1⟩
  · norm_num [Nat.ascFactorial_succ,Nat.ascFactorial_zero]
  · rw [show 6=3+3 by decide,skipped_det]
    norm_num [Nat.ascFactorial_succ,Nat.ascFactorial_zero]

/-- Throughout a short affine sweep a target multiple has just two possible
cofactors, even though both prime factors and the successful offset are unknown. -/
theorem affine_multiples {p q c : ℕ} (qp : q.Prime)
    (order : p < q) (bal : q ≤ 2*p) (low : 3 ≤ c) (high : 2*c ≤ p) :
    (p ∣ 3*(p*q).sqrt+c ↔ 3*(p*q).sqrt+c=4*p) ∧
    (q ∣ 3*(p*q).sqrt+c ↔ 3*(p*q).sqrt+c=3*q) := by
  let x := (p*q).sqrt
  have bounds : x^2 ≤ p*q ∧ p*q < (x+1)^2 := ⟨Nat.sqrt_le' _,Nat.lt_succ_sqrt' _⟩
  have px : p ≤ x := Nat.le_sqrt.mpr (Nat.mul_le_mul_left _ order.le)
  have xq : x < q := Nat.sqrt_lt.mpr (Nat.mul_lt_mul_of_pos_right order qp.pos)
  have lx : 2*x < 3*p := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    nlinarith [Nat.mul_le_mul_left p bal]
  have lq : 2*q < 3*(x+1) := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    nlinarith [Nat.mul_le_mul_right q bal]
  change (p∣3*x+c ↔ _) ∧ (q∣3*x+c ↔ _)
  constructor <;> constructor
  · rintro ⟨j,hj⟩
    have lo : 3 < j := Nat.lt_of_mul_lt_mul_left (show p*3 < p*j by omega)
    have hi : j < 5 := Nat.lt_of_mul_lt_mul_left (show p*j < p*5 by omega)
    have : j=4 := by omega
    simpa [this,mul_comm] using hj
  · rintro h; exact ⟨4,by simpa only [mul_comm p 4] using h⟩
  · rintro ⟨j,hj⟩
    have lo : 2 < j := Nat.lt_of_mul_lt_mul_left (show q*2 < q*j by omega)
    have hi : j < 4 := Nat.lt_of_mul_lt_mul_left (show q*j < q*4 by omega)
    have : j=3 := by omega
    simpa [this,mul_comm] using hj
  · rintro h; exact ⟨3,by simpa only [mul_comm q 3] using h⟩

/-- Fixed modulus for one pass over a menu of skipped-row widths. -/
def allowed (v : ℕ) : Bool :=
  (v%4 == 0 && v/4%2 == 1 && v/4%3 != 0) || (v%3 == 0 && v/3%2 == 1 && v/3%3 != 0)

theorem allowed_period (v : ℕ) : allowed (v%72) = allowed v := by
  apply Bool.eq_iff_iff.mpr
  simp only [allowed,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne]
  omega

theorem allowed_count : ((range 72).filter fun v => allowed v).card = 14 := by decide +kernel

/-- Every offset rejected by the 14-residue test gives gcd one. -/
theorem rejected_gcd {p q c : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p < q)
    (bal : q≤2*p) (low : 3≤c) (high : 2*c≤p)
    (reject : allowed ((3*(p*q).sqrt+c)%72)=false) : (3*(p*q).sqrt+c).gcd (p*q)=1 := by
  rw [allowed_period] at reject
  have base {z : ℕ} (hz : z.Prime) (big : 3 < z) : z%2=1 ∧ z%3≠0 := by
    refine ⟨Nat.odd_iff.mp (hz.odd_of_ne_two (by omega)),?_⟩
    intro divides
    have eq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hz).mp (Nat.dvd_of_mod_eq_zero divides)
    omega
  have b₁ := base pp (by omega)
  have b₂ := base qp (by omega)
  obtain ⟨first,second⟩ := affine_multiples qp order bal low high
  have unit₁ : ¬p ∣ 3*(p*q).sqrt+c := by
    intro yes
    rw [first.mp yes] at reject
    simp [allowed,b₁] at reject
  have unit₂ : ¬q ∣ 3*(p*q).sqrt+c := by
    intro yes
    rw [second.mp yes] at reject
    simp [allowed,b₂] at reject
  exact ((pp.coprime_iff_not_dvd.mpr unit₁).symm.mul_right (qp.coprime_iff_not_dvd.mpr unit₂).symm).gcd_eq_one

/-- Dropping all rejected widths from a product preserves its exact gcd.
Only the gcd matters, so the products may be reduced modulo N as they accumulate. -/
theorem batch_gcd {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p<q) (bal : q≤2*p)
    (C : Finset ℕ) (fits : ∀ c∈C, 3≤c ∧ 2*c≤p) :
    (∏ c ∈ C.filter (fun c => allowed ((3*(p*q).sqrt+c)%72)), (3*(p*q).sqrt+c)).gcd (p*q) =
      (∏ c ∈ C, (3*(p*q).sqrt+c)).gcd (p*q) := by
  let f (c : ℕ) := 3*(p*q).sqrt+c
  let keep (c : ℕ) := allowed (f c%72) = true
  classical
  have cop : (∏ c ∈ C.filter (fun c => ¬keep c), f c).Coprime (p*q) := by
    apply Nat.coprime_prod_left_iff.mpr
    intro c hc
    obtain ⟨here,no⟩ := mem_filter.mp hc
    obtain ⟨lo,hi⟩ := fits _ here
    exact rejected_gcd pp qp order bal lo hi (Bool.eq_false_iff.mpr no)
  change (∏ c ∈ C.filter keep, f c).gcd (p*q) = (∏ c ∈ C, f c).gcd (p*q)
  rw [←prod_filter_not_mul_prod_filter C keep f,cop.gcd_mul_left_cancel]

/-- Different widths cannot hit the two prime coordinates in the same short menu.
The raw batch and its filtered version therefore cannot saturate. -/
theorem no_saturation {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p<q) (bal : q≤2*p)
    (C : Finset ℕ) (fits : ∀ c∈C, 3≤c ∧ 2*c≤p) :
    ¬ p*q ∣ ∏ c ∈ C, (3*(p*q).sqrt+c) := by
  intro hit
  obtain ⟨a,ha,pa⟩ := (pp.prime.dvd_finset_prod_iff _).mp ((dvd_mul_right p q).trans hit)
  obtain ⟨b,hb,qb⟩ := (qp.prime.dvd_finset_prod_iff _).mp ((dvd_mul_left q p).trans hit)
  obtain ⟨la,ua⟩ := fits a ha
  obtain ⟨lb,ub⟩ := fits b hb
  have ea := (affine_multiples qp order bal la ua).1.mp pa
  have eb := (affine_multiples qp order bal lb ub).2.mp qb
  have gap : 2*(p*q).sqrt < p+q := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    obtain ⟨d,e⟩ := Nat.exists_eq_add_of_le order.le
    have pos : 0<d := by omega
    rw [e]
    nlinarith [Nat.sqrt_le' (p*(p+d)),sq_pos_of_pos pos]
  omega

private theorem first_trace {n s : ℕ} {v : ℝ} (sq : v^2 = n) (upper : n ≤ s^2)
    (near : (s:ℝ) < v+1) : ceilSqrt n = s := by
  apply le_antisymm (ceilSqrt_le_iff.mpr upper)
  by_contra! smaller
  have below : (ceilSqrt n:ℝ)+1 ≤ s := by exact_mod_cast (Nat.succ_le_of_lt smaller)
  have ge : v ≤ (ceilSqrt n:ℝ) := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [sq]
    exact_mod_cast (ceilSqrt_le_iff.mp (le_refl (ceilSqrt n)))
  linarith

/-- If the largest offset has square smaller than the smaller prime, every affine
hit already appears at the first ordinary or (16,9)-weighted Fermat trace. -/
theorem covered_by_two_traces {p q c : ℕ} (qp : q.Prime) (order : p<q) (bal : q≤2*p)
    (lo : 3≤c) (hi : 2*c≤p) (short : c^2<p)
    (hit : p∣3*(p*q).sqrt+c ∨ q∣3*(p*q).sqrt+c) :
    ceilSqrt (576*(p*q)) = 16*p+9*q ∨ ceilSqrt (4*(p*q)) = p+q := by
  let x := (p*q).sqrt
  let y := Real.sqrt ((p:ℝ)*q)
  have ysq : y^2 = (p:ℝ)*q := Real.sq_sqrt (by positivity)
  have floor₁ : (x:ℝ) ≤ y := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    exact_mod_cast (Nat.sqrt_le' (p*q))
  have floor₂ : y < (x:ℝ)+1 := by
    apply (Real.sqrt_lt' (by positivity)).mpr
    exact_mod_cast (Nat.lt_succ_sqrt' (p*q))
  have small : (c:ℝ)^2 < p := by exact_mod_cast short
  have lower : (3:ℝ)≤c := by exact_mod_cast lo
  have ppos : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have qpos : (0:ℝ)<q := by exact_mod_cast qp.pos
  have grow : (p:ℝ)<q := by exact_mod_cast order
  obtain ⟨leftHit,rightHit⟩ := affine_multiples qp order bal lo hi
  rcases hit with h | h
  · left
    have eq : 3*(x:ℝ)+c=4*p := by exact_mod_cast (leftHit.mp h)
    have e₀ : 0≤4*(p:ℝ)-3*y := by linarith
    have e₁ : 4*(p:ℝ)-3*y≤c := by linarith
    have smallError := (sq_le_sq₀ e₀ (by positivity)).mpr e₁
    apply first_trace (v:=24*y) (by push_cast; nlinarith only [ysq])
    · zify; nlinarith only [sq_nonneg (16*(p:ℤ)-9*q)]
    · push_cast
      have identity : (4*(p:ℝ)-3*y)^2 = p*(16*p+9*q-24*y) := by
        calc _ = 16*(p:ℝ)^2-24*p*y+9*y^2 := by ring
             _ = _ := by rw [ysq]; ring
      rw [identity] at smallError
      have bound : (p:ℝ)*(16*p+9*q-24*y)<p*1 := by simpa using smallError.trans_lt small
      have gap := lt_of_mul_lt_mul_left bound ppos.le
      linarith
  · right
    have eq : 3*(x:ℝ)+c=3*q := by exact_mod_cast (rightHit.mp h)
    have e₀ : 0≤(q:ℝ)-y := by linarith
    have e₁ : (q:ℝ)-y≤c := by linarith
    have smallError := (sq_le_sq₀ e₀ (by positivity)).mpr e₁
    apply first_trace (v:=2*y) (by push_cast; nlinarith only [ysq])
    · zify; nlinarith only [sq_nonneg ((p:ℤ)-q)]
    · push_cast
      have identity : ((q:ℝ)-y)^2 = q*(p+q-2*y) := by
        calc _ = (q:ℝ)^2-2*q*y+y^2 := by ring
             _ = _ := by rw [ysq]; ring
      rw [identity] at smallError
      have bound : (q:ℝ)*(p+q-2*y)<q*1 := by simpa using (smallError.trans_lt small).trans grow
      have gap := lt_of_mul_lt_mul_left bound qpos.le
      linarith

/-- At width six the affine value can only be four times the smaller prime. -/
theorem affine_six {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (big : 101 ≤ p)
    (order : p < q) (bal : q ≤ 2*p) :
    (3*(p*q).sqrt+10).gcd (p*q) = if 3*(p*q).sqrt+10=4*p then p else 1 := by
  obtain ⟨first,second⟩ := affine_multiples (c:=10) qp order bal (by decide) (by omega)
  have qmiss : ¬q ∣ 3*(p*q).sqrt+10 := fun yes => by have := second.mp yes; omega
  rw [((Nat.coprime_primes pp qp).mpr order.ne).gcd_mul,
    (qp.coprime_iff_not_dvd.mpr qmiss).symm.gcd_eq_one,mul_one]
  split_ifs with yes
  · exact Nat.gcd_eq_right (first.mpr yes)
  · exact (pp.coprime_iff_not_dvd.mpr (mt first.mp yes)).symm.gcd_eq_one

/-- These four integer lines are the complete success condition at width six. -/
theorem four_lines {p q : ℕ} (big : 101 ≤ p) (odd : Odd q) :
    3*(p*q).sqrt+10=4*p ↔
      16*p = 9*q+61 ∨ 16*p = 9*q+67 ∨ 16*p = 9*q+73 ∨ 16*p = 9*q+79 := by
  rcases odd with ⟨v,hv⟩
  constructor
  · intro h
    let x := (p*q).sqrt
    change 3*x+10=4*p at h
    have squared := congrArg (fun z : ℕ => z^2) h
    have a : x^2 ≤ p*q := Nat.sqrt_le' _
    have b : p*q < (x+1)^2 := Nat.lt_succ_sqrt' _
    have lo : 9*q+56 ≤ 16*p := by
      by_contra! bad
      nlinarith [Nat.mul_le_mul_left p (show 16*p ≤ 9*q+55 by omega)]
    have hi : 16*p ≤ 9*q+79 := by
      by_contra! bad
      nlinarith [Nat.mul_le_mul_left p (show 9*q+80 ≤ 16*p by omega)]
    omega
  · intro lines
    let x := (4*p-10)/3
    have eq : 3*x+10=4*p := by dsimp [x]; omega
    have squared := congrArg (fun z : ℕ => z^2) eq
    have lo : 9*q+56 ≤ 16*p := by omega
    have hi : 16*p ≤ 9*q+79 := by omega
    have a : x^2 ≤ p*q := by nlinarith [Nat.mul_le_mul_left p hi]
    have b : p*q < (x+1)^2 := by nlinarith [Nat.mul_le_mul_left p lo]
    have root : (p*q).sqrt=x := le_antisymm (Nat.lt_succ_iff.mp (Nat.sqrt_lt'.mpr b)) (Nat.le_sqrt'.mpr a)
    rwa [root]

/-- For a fixed smaller prime there are at most two eligible odd partners
for the affine width-six probe. -/
theorem two_partners {p : ℕ} (big : 101 ≤ p) (Q : Finset ℕ)
    (hit : ∀ q ∈ Q, Odd q ∧ 3*(p*q).sqrt+10=4*p) : Q.card≤2 := by
  classical
  by_cases existsQ : Q.Nonempty
  · let a := Q.min' existsQ
    have ha : a ∈ Q := min'_mem _ _
    obtain ⟨ova,ea⟩ := hit a ha
    have la := (four_lines big ova).mp ea
    have sub : Q ⊆ {a,a+2} := by
      intro q hq
      have aq : a ≤ q := min'_le _ _ hq
      obtain ⟨ovq,eq⟩ := hit q hq
      have lq := (four_lines big ovq).mp eq
      rcases ova with ⟨u,hu⟩; rcases ovq with ⟨w,hw⟩
      simp only [mem_insert,mem_singleton]
      omega
    exact (card_le_card sub).trans (by simp)
  · simp [Finset.not_nonempty_iff_eq_empty.mp existsQ]

end PrimeFactors.NeighborFactorialDeterminant
