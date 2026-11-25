import PrimeFactors.IntegerLaneWindowWork
import PrimeFactors.FactorSum

/-! A divisor prefix as a weighted difference of two reciprocal-floor sums.
Piecewise sums of affine floors cannot compress all the individual quotient
values on a large balanced prefix into a few low-weight pieces. -/

namespace PrimeFactors.ReciprocalFloorPrefixes

open Finset

def jump (n x : ℕ) := n/x-(n-1)/x

theorem jump_eq {n : ℕ} (pos : 0<n) (x : ℕ) :
    jump n x = if x∣n then 1 else 0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  unfold jump
  rw [Nat.succ_sub_one,Nat.succ_div,Nat.add_sub_cancel_left]

/-- For all cutoffs up to the square root, the prefix returns the factor
itself as soon as that factor has entered the prefix. -/
theorem weighted_prefix {p q H : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p≤q)
    (cut : H≤(p*q).sqrt) :
    ∑ x ∈ Icc 2 H, x*jump (p*q) x = if p≤H then p else 0 := by
  have primeOnly {x : ℕ} (hx : x∈Icc 2 H) : x∣p*q ↔ x=p := by
    constructor
    · rintro ⟨y,hy⟩
      obtain ⟨lo,hi⟩ := mem_Icc.mp hx
      have pos : 0<x := by omega
      have bound := Nat.le_sqrt.mp (hi.trans cut)
      rw [hy] at bound
      exact (ordered_semiprime_pair_unique hp hq ord ((Nat.mul_le_mul_left_iff pos).mp bound)
        (by omega) hy.symm).1
    · rintro rfl; exact dvd_mul_right ..
  calc
    _ = ∑ x ∈ Icc 2 H, if x=p then x else 0 := by
      apply sum_congr rfl
      intro x hx
      simp only [jump_eq (Nat.mul_pos hp.pos hq.pos),primeOnly hx]
      split_ifs <;> simp
    _ = _ := by simp [sum_ite_eq',Finset.mem_Icc,hp.two_le]

/-- Real slopes and intercepts are allowed. Each integer coefficient charges
its absolute value, so this includes every sum and difference of unweighted floor terms. -/
structure Formula (m : ℕ) where
  slope : ℝ
  intercept : ℝ
  a : Fin m → ℝ
  b : Fin m → ℝ
  c : Fin m → ℤ

noncomputable def Formula.value {m : ℕ} (F : Formula m) (x : ℝ) : ℝ :=
  F.slope*x+F.intercept+∑ i,(F.c i:ℝ)*(⌊F.a i*x+F.b i⌋:ℤ)

noncomputable def Formula.mass {m : ℕ} (F : Formula m) := ∑ i,(F.c i).natAbs

/-- Rounding three equally spaced real values produces an integer second
difference of at most one in absolute value. -/
theorem affine_floor_step {x y z : ℝ} (mid : x+z=2*y) :
    |⌊x⌋-2*⌊y⌋+⌊z⌋|≤1 := by
  have lower : (-2:ℝ)<(⌊x⌋:ℝ)-2*(⌊y⌋:ℝ)+(⌊z⌋:ℝ) := by
    linarith [Int.lt_floor_add_one x,Int.lt_floor_add_one z,Int.floor_le y]
  have upper : (⌊x⌋:ℝ)-2*(⌊y⌋:ℝ)+(⌊z⌋:ℝ)<2 := by
    linarith [Int.floor_le x,Int.floor_le z,Int.lt_floor_add_one y]
  have l : (-2:ℤ)<⌊x⌋-2*⌊y⌋+⌊z⌋ := by exact_mod_cast lower
  have u : ⌊x⌋-2*⌊y⌋+⌊z⌋<(2:ℤ) := by exact_mod_cast upper
  exact abs_le.mpr ⟨by omega,by omega⟩

theorem formula_step {m : ℕ} (F : Formula m) (a h : ℝ) :
    |F.value a-2*F.value (a+h)+F.value (a+2*h)| ≤ (F.mass:ℝ) := by
  let v (i : Fin m) (x : ℝ) : ℤ := ⌊F.a i*x+F.b i⌋
  let d (i : Fin m) := v i a-2*v i (a+h)+v i (a+2*h)
  have one (i : Fin m) : |d i|≤1 := affine_floor_step (by ring)
  have twice : F.value a-2*F.value (a+h)+F.value (a+2*h) =
      ∑ i,(F.c i:ℝ)*(d i:ℝ) := by
    dsimp only [Formula.value,d,v]
    push_cast
    simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,mul_sum]
    ring
  rw [twice]
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ i, |(F.c i:ℝ)| := by
      apply sum_le_sum
      intro i _
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (show |(d i:ℝ)|≤1 by exact_mod_cast one i) (abs_nonneg (F.c i:ℝ))
    _ = _ := by simp [Formula.mass,Int.cast_natAbs]

/-- Strict necessary curvature condition on any single three-point fit. -/
theorem curvature {n a h : ℝ} (ha : 0<a) (hh : 0≤h) {m : ℕ} (F : Formula m)
    (first : F.value a=⌊n/a⌋) (mid : F.value (a+h)=⌊n/(a+h)⌋)
    (last : F.value (a+2*h)=⌊n/(a+2*h)⌋) :
    2*n*h^2 < (F.mass+2)*a*(a+h)*(a+2*h) := by
  have p1 : 0<a+h := by linarith
  have p2 : 0<a+2*h := by linarith
  have second := (le_abs_self _).trans (formula_step F a h)
  rw [first,mid,last] at second
  have bound : n/a-2*(n/(a+h))+n/(a+2*h) < F.mass+2 := by
    linarith only [second,Int.lt_floor_add_one (n/a),Int.floor_le (n/(a+h)),Int.lt_floor_add_one (n/(a+2*h))]
  have id : n/a-2*(n/(a+h))+n/(a+2*h) = (2*n*h^2)/(a*(a+h)*(a+2*h)) := by
    field_simp
    ring
  rw [id] at bound
  convert (div_lt_iff₀ (mul_pos (mul_pos ha p1) p2)).mp bound using 1
  ring

/-- On odd indices within the square-root range, h denotes the number of
odd steps between consecutive samples. The square-root bound uses no factors. -/
theorem odd_step {n x h J : ℕ} (pos : 0<x) (top : (x+4*h)^2≤n)
    (root : n≤J^4) {m : ℕ} (F : Formula m)
    (fits : ∀ j : ℕ, j≤2*h → F.value (x+2*j:ℕ)=⌊(n:ℝ)/(x+2*j:ℕ)⌋) :
    8*h^2 < (F.mass+2)*J^2 := by
  have h0 := fits 0 (by omega)
  have h1 := fits h (by omega)
  have h2 := fits (2*h) (by omega)
  simp only [Nat.mul_zero,Nat.add_zero] at h0
  push_cast at h0 h1 h2
  have ht := curvature (by exact_mod_cast pos : 0<(x:ℝ)) (by positivity : 0≤2*(h:ℝ)) F h0 h1 h2
  have zz : 2*n*(2*h)^2 < (F.mass+2)*x*(x+2*h)*(x+2*(2*h)) := by exact_mod_cast ht
  let y := x+4*h
  have yj : y≤J^2 := by
    have lim : y^2≤(J^2)^2 := by simpa only [←pow_mul] using top.trans root
    exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp lim
  have upper : (F.mass+2)*x*(x+2*h)*(x+2*(2*h)) ≤ ((F.mass+2)*J^2)*n := calc
    _ ≤ (F.mass+2)*y*y*y := by
      apply Nat.mul_le_mul
      · apply Nat.mul_le_mul
        · exact Nat.mul_le_mul_left _ (by dsimp [y]; omega)
        · dsimp [y]; omega
      · dsimp [y]; omega
    _ = ((F.mass+2)*y)*y^2 := by ring
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ yj) top
  apply Nat.lt_of_mul_lt_mul_right (a:=n)
  exact (by simpa only [show 2*n*(2*h)^2=8*h^2*n by ring] using zz.trans_le upper)


/-- A contiguous run in the odd index z, where the trial divisor is 2z+1.
All endpoint and interpolation data may depend on the entire public input. -/
structure Block (n : ℕ) where
  start : ℕ
  len : ℕ
  terms : ℕ
  F : Formula terms
  inside : ∀ j<len, (2*start+1+2*j)^2≤n
  fits : ∀ j<len, F.value (2*start+1+2*j:ℕ)=⌊(n:ℝ)/(2*start+1+2*j:ℕ)⌋

private theorem diameter {n J : ℕ} (root : n≤J^4) (B : Block n) (pos : 0<B.len) :
    let h := (B.len-1)/2
    8*h^2 < (B.F.mass+2)*J^2 := by
  let h := (B.len-1)/2
  have last : 2*h<B.len := by dsimp [h]; omega
  have top : (2*B.start+1+4*h)^2≤n := by
    simpa only [show 4*h=2*(2*h) by ring] using B.inside (2*h) last
  exact odd_step (x:=2*B.start+1) (h:=h) (by omega) top root B.F
    (fun j le => B.fits j (le.trans_lt last))

/-- Each block charges one unit plus the absolute sum of its integer multipliers. -/
theorem block_bound {n J : ℕ} (root : n≤J^4) (B : Block n) :
    B.len ≤ (J+1)*(B.F.mass+1) := by
  by_cases pos : 0<B.len
  · let h := (B.len-1)/2
    have strict := diameter root B pos
    change 8*h^2<(B.F.mass+2)*J^2 at strict
    have upper : B.F.mass+2≤2*(B.F.mass+1)^2 := by nlinarith [Nat.zero_le B.F.mass]
    have sq : (2*h)^2 < (J*(B.F.mass+1))^2 := by
      nlinarith only [strict,Nat.mul_le_mul_right (J^2) upper]
    have length := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp sq
    have edge : B.len≤2*h+2 := by dsimp [h]; omega
    rw [Nat.add_mul,one_mul]
    omega
  · omega

/-- Sharper estimate when the only nonlinear term is one affine floor of unit weight. -/
theorem single_block {n J : ℕ} (root : n≤J^4) (B : Block n) (one : B.F.mass=1) :
    4*B.len ≤ 5*J+8 := by
  by_cases pos : 0<B.len
  · let h := (B.len-1)/2
    have strict := diameter root B pos
    change 8*h^2<(B.F.mass+2)*J^2 at strict
    rw [one] at strict
    have sq : (8*h)^2 < (5*J)^2 := by nlinarith only [strict,Nat.zero_le (J^2)]
    have length := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp sq
    dsimp [h] at length
    omega
  · omega

/-- Count the represented positions even when blocks overlap. -/
private theorem cover_size {ι : Type*} {n : ℕ} (domain : Finset ℕ) (runs : Finset ι)
    (B : ι → Block n) (full : domain⊆runs.biUnion (fun i => Ico (B i).start ((B i).start+(B i).len))) :
    domain.card≤∑ i ∈ runs,(B i).len := by
  simpa only [Nat.card_Ico,Nat.add_sub_cancel_left] using (card_le_card full).trans card_biUnion_le

theorem cover_budget {ι : Type*} {n J : ℕ} (root : n≤J^4) (domain : Finset ℕ)
    (runs : Finset ι) (B : ι → Block n)
    (full : domain⊆runs.biUnion (fun i => Ico (B i).start ((B i).start+(B i).len))) :
    domain.card≤(J+1)*(∑ i ∈ runs,((B i).F.mass+1)) := by
  rw [mul_sum]
  exact (cover_size domain runs B full).trans (sum_le_sum (fun i _ => block_bound root (B i)))

theorem single_budget {ι : Type*} {n J : ℕ} (root : n≤J^4) (domain : Finset ℕ)
    (runs : Finset ι) (B : ι → Block n)
    (full : domain⊆runs.biUnion (fun i => Ico (B i).start ((B i).start+(B i).len)))
    (one : ∀ i∈runs, (B i).F.mass=1) :
    4*domain.card≤(5*J+8)*runs.card := by
  have sum := Nat.mul_le_mul_left 4 (cover_size domain runs B full)
  rw [mul_sum] at sum
  simpa only [sum_const,nsmul_eq_mul,Nat.cast_id,mul_comm (5*J+8)] using
    sum.trans (sum_le_sum fun i hi => single_block root (B i) (one i hi))

set_option exponentiation.threshold 10000 in
/-- Both controls require exponentially many pieces of one affine floor, and
exponentially much total mass in the model allowing signed sums. -/
theorem controls {ι : Type*} (fresh : Bool) (runs : Finset ι)
    (B : ι → Block (IntegerLaneWindowWork.control fresh true).n) :
    let c := IntegerLaneWindowWork.control fresh true
    let e := if fresh then 507 else 508
    (IntegerLaneWindowWork.domain c.n 1 c.n.sqrt⊆runs.biUnion
      (fun i => Ico (B i).start ((B i).start+(B i).len))) →
    2^e < (∑ i ∈ runs, ((B i).F.mass+1)) ∧
      ((∀ i∈runs, (B i).F.mass=1) → 2^e<runs.card) := by
  intro c e full
  let t : ℕ := (if fresh then 57719 else 49228)*2^1008
  have price : t^2≤c.n ∧ (c.fourth+1)*2^e<(IntegerLaneWindowWork.domain c.n 1 t).card ∧
      (5*c.fourth+8)*2^e<4*(IntegerLaneWindowWork.domain c.n 1 t).card := by
    simp only [IntegerLaneWindowWork.domain,Nat.card_Ico]
    cases fresh <;> decide +kernel
  have le : t≤c.n.sqrt := Nat.le_sqrt'.mpr price.1
  have count : (IntegerLaneWindowWork.domain c.n 1 t).card≤(IntegerLaneWindowWork.domain c.n 1 c.n.sqrt).card := by
    simp only [IntegerLaneWindowWork.domain,Nat.card_Ico]
    apply Nat.sub_le_sub_right
    exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le_sub_right le 1)) _
  have root := (IntegerLaneWindowWork.control_receipts fresh true).2.2.1
  constructor
  · exact Nat.lt_of_mul_lt_mul_left (price.2.1.trans_le (count.trans (cover_budget root _ runs B full)))
  · intro ones
    exact Nat.lt_of_mul_lt_mul_left (price.2.2.trans_le
      ((Nat.mul_le_mul_left 4 count).trans (single_budget root _ runs B full ones)))

open Function Polynomial

/-- Denominator of the r-th forward difference on positive coordinates. -/
noncomputable def denominator : ℕ → ℚ → ℚ → ℚ
  | 0, x, _ => x
  | r+1,x,h => denominator r x h*(x+(r+1:ℕ)*h)

private theorem denominator_shift (r : ℕ) (x h : ℚ) :
    denominator (r+1) x h = x*denominator r (x+h) h := by
  induction r with
  | zero => simp [denominator]
  | succ r ih =>
    rw [denominator,ih]
    conv_rhs => rw [denominator]
    push_cast
    ring

private theorem denominator_pos (r : ℕ) {x h : ℚ} (pos : 0<x) (step : 0≤h) :
    0<denominator r x h := by
  induction r with
  | zero => exact pos
  | succ r ih =>
    rw [denominator]
    positivity

/-- Exact reciprocal difference, independent of any factorization or interval decomposition. -/
theorem reciprocal_difference (r : ℕ) (n : ℚ) {x h : ℚ} (pos : 0<x) (step : 0≤h) :
    (fwdDiff h)^[r] (fun t => n/t) x * denominator r x h = (-1)^r*r.factorial*n*h^r := by
  induction r generalizing x with
  | zero => simp [denominator,pos.ne']
  | succ r ih =>
    rw [iterate_succ_apply',fwdDiff,sub_mul]
    have l := ih (x:=x+h) (by linarith)
    have u := ih (x:=x) pos
    rw [denominator_shift r x h, mul_left_comm _ x _, l]
    rw [←denominator_shift r x h,denominator,←mul_assoc _ (denominator r x h) _,u]
    rw [Nat.factorial_succ,pow_succ (-1:ℚ),pow_succ h]
    push_cast
    ring

open private PrimeFactors.IntegerLaneWindowWork.bound_diff from PrimeFactors.IntegerLaneWindowWork

/-- Degree-r−1 rational polynomials with exactly matching floors must obey
a finite mesh bound. Only the r+1 chosen samples are used. -/
theorem polynomial_floor_width {r : ℕ} {P : ℚ[X]} {n x h : ℚ}
    (pos : 0<x) (step : 0≤h) (hn : 0≤n) (degree : P.natDegree<r)
    (fit : ∀ j ≤ r, ⌊n/(x+j*h)⌋ = ⌊P.eval (x+j*h)⌋) :
    r.factorial*n*h^r ≤ 2^r*denominator r x h := by
  let G := fun y : ℚ => n/y-P.eval y
  have norm (j : ℕ) (hj : j≤r) : |G (x+j*h)|≤1 := by
    let y : ℚ := x+j*h
    have eq : ⌊n/y⌋=⌊P.eval y⌋ := fit j hj
    have a := Int.lt_floor_add_one (n/y)
    have b := Int.floor_le (n/y)
    rw [eq] at a b
    change |n/y-P.eval y|≤1
    exact abs_le.mpr ⟨by linarith [Int.lt_floor_add_one (P.eval y)],by linarith [Int.floor_le (P.eval y)]⟩
  have upper := PrimeFactors.IntegerLaneWindowWork.bound_diff r x h 1 G norm
  have id : (fun y : ℚ => n/y)=G+(fun y => P.eval y) := by funext y; simp [G]
  have z := reciprocal_difference r n pos step
  rw [id,fwdDiff_iter_add,Pi.add_apply,IntegerLaneWindowWork.top_difference degree.le,
    coeff_eq_zero_of_natDegree_lt degree,mul_zero,add_zero] at z
  have v := congrArg abs z
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_of_nonneg hn,abs_of_nonneg step,
    abs_of_nonneg (denominator_pos r pos step).le,abs_of_nonneg (Nat.cast_nonneg r.factorial : (0:ℚ)≤_)] at v
  rw [mul_one] at upper
  exact v ▸ mul_le_mul_of_nonneg_right upper (denominator_pos r pos step).le

private theorem denominator_upper (r : ℕ) {x h : ℚ} (pos : 0<x) (step : 0≤h) :
    denominator r x h ≤ (x+r*h)^(r+1) := by
  induction r with
  | zero => simp [denominator]
  | succ r ih =>
    rw [denominator,pow_succ (x+(r+1:ℕ)*h) (r+1)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply ih.trans
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    linarith

/-- A fixed-degree polynomial cannot fit the reciprocal floor on arbitrarily
long complete grids near the square root. The last positive coordinate is
x+r*h; the proof compares its square with the product. -/
theorem polynomial_scale {r : ℕ} {P : ℚ[X]} {n x h : ℚ}
    (pos : 0<x) (step : 0≤h) (hn : 0<n) (degree : P.natDegree<r)
    (below : (x+r*h)^2 ≤ n) (fit : ∀ j ≤ r, ⌊n/(x+j*h)⌋ = ⌊P.eval (x+j*h)⌋) :
    r.factorial*h^r ≤ 2^r*(x+r*h)^(r-1) := by
  have width := polynomial_floor_width pos step hn.le degree fit
  have upper := mul_le_mul_of_nonneg_left (denominator_upper r pos step) (by positivity : (0:ℚ)≤2^r)
  have eq : r+1=(r-1)+2 := by omega
  rw [eq,pow_add] at upper
  have bound := mul_le_mul_of_nonneg_left below (by positivity : (0:ℚ) ≤ 2^r*(x+r*h)^(r-1))
  apply le_of_mul_le_mul_right (a:=n) _ hn
  calc
    _ = r.factorial*n*h^r := by ring
    _ ≤ _ := width
    _ ≤ _ := upper
    _ ≤ _ := by simpa only [mul_assoc] using bound

end PrimeFactors.ReciprocalFloorPrefixes
