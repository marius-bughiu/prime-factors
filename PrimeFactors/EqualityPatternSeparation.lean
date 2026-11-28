import PrimeFactors.EqualityPatternSampling
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Distinguishing two uniform alphabet sizes from repeated labels in
independent draws. Hellinger affinity bounds every equality-only test. -/
namespace PrimeFactors.EqualityPatternSeparation
open Finset

private noncomputable def affinity (x y : ℝ) :=
  Real.sqrt x*Real.sqrt y + Real.sqrt (1-x)*Real.sqrt (1-y)

private theorem affinity_self {x : ℝ} (h : 0≤x ∧ x≤1) : affinity x x=1 := by
  unfold affinity
  rw [Real.mul_self_sqrt h.1,Real.mul_self_sqrt (sub_nonneg.mpr h.2)]
  ring

/-- The square of the probability difference for a binary test is bounded
by its unnormalized squared Hellinger distance. -/
private theorem bernoulli {x y : ℝ} (hx : 0≤x ∧ x≤1) (hy : 0≤y ∧ y≤1) :
    (x-y)^2≤2-2*affinity x y := by
  let a := Real.sqrt x
  let b := Real.sqrt y
  let c := Real.sqrt (1-x)
  let d := Real.sqrt (1-y)
  have a2 : a^2=x := Real.sq_sqrt hx.1
  have b2 : b^2=y := Real.sq_sqrt hy.1
  have c2 : c^2=1-x := Real.sq_sqrt (sub_nonneg.mpr hx.2)
  have d2 : d^2=1-y := Real.sq_sqrt (sub_nonneg.mpr hy.2)
  have w0 : 0≤a*d+b*c := by dsimp [a,b,c,d]; positivity
  have w1 : a*d+b*c≤1 := by nlinarith only [sq_nonneg (a-d),sq_nonneg (b-c),a2,b2,c2,d2]
  have w2 : (a*d+b*c)^2≤1 := by nlinarith only [mul_nonneg w0 (sub_nonneg.mpr w1),w1]
  have det : (a*d-b*c)*(a*d+b*c)=x-y := by
    calc _ = a^2*d^2-b^2*c^2 := by ring
         _ = _ := by rw [a2,b2,c2,d2]; ring
  have norm : (a*d-b*c)^2+(a*b+c*d)^2=1 := by
    calc _ = (a^2+c^2)*(b^2+d^2) := by ring
         _ = _ := by rw [a2,b2,c2,d2]; ring
  have first := mul_le_mul_of_nonneg_left w2 (sq_nonneg (a*d-b*c))
  rw [←mul_pow,det,mul_one] at first
  change _≤2-2*(a*b+c*d)
  nlinarith only [first,norm,sq_nonneg (1-(a*b+c*d))]

private theorem sqrt_loss {x y : ℝ} (hx : 0≤x) (hy : 0<y) :
    (Real.sqrt x-Real.sqrt y)^2≤(x-y)^2/y := by
  have diff : (Real.sqrt x-Real.sqrt y)*(Real.sqrt x+Real.sqrt y)=x-y := by
    nlinarith only [Real.sq_sqrt hx,Real.sq_sqrt hy.le]
  have cap : y≤(Real.sqrt x+Real.sqrt y)^2 := by
    nlinarith only [hx,Real.sq_sqrt hx,Real.sq_sqrt hy.le,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  apply (le_div_iff₀ hy).mpr
  calc _ ≤ (Real.sqrt x-Real.sqrt y)^2*(Real.sqrt x+Real.sqrt y)^2 :=
         mul_le_mul_of_nonneg_left cap (sq_nonneg _)
       _ = _ := by rw [←mul_pow,diff]

/-- Conditional on k previously seen distinct labels, each has probability
1/m and the new-label probability is (m-k)/m. This bounds the one-step loss. -/
theorem one_step {m M k : ℝ} (mp : 0<m) (sizes : m≤M) (kp : 0≤k) (room : 2*k≤m) :
    k*(Real.sqrt (1/m)-Real.sqrt (1/M))^2+
      (Real.sqrt ((m-k)/m)-Real.sqrt ((M-k)/M))^2 ≤ 2*k*(M-m)^2/m^3 := by
  have Mp := mp.trans_le sizes
  have rest : 0<M-k := by linarith
  have one := sqrt_loss (x:=1/m) (y:=1/M) (by positivity) (by positivity)
  have fresh := sqrt_loss (x:=(m-k)/m) (y:=(M-k)/M)
    (div_nonneg (by linarith) mp.le) (div_pos rest Mp)
  calc
    _ ≤ k*((1/m-1/M)^2/(1/M))+(((m-k)/m-(M-k)/M)^2/((M-k)/M)) :=
        add_le_add (mul_le_mul_of_nonneg_left one kp) fresh
    _ = k*(M-m)^2/(m^2*(M-k)) := by field_simp; ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos mp) rest) (pow_pos mp _)).mpr
      have h := mul_nonneg (mul_nonneg kp (sq_nonneg (M-m)))
        (mul_nonneg (sq_nonneg m) (show 0≤2*(M-k)-m by linarith))
      nlinarith only [h]

private noncomputable def weight (m : ℝ) (k i : ℕ) :=
  if i=k then (m-k)/m else 1/m

private theorem rows (k : ℕ) (f : ℕ→ℝ) (a b : ℝ) (other : ∀ i<k,f i=a) (last : f k=b) :
    ∑ i∈range (k+1),f i=(k:ℝ)*a+b := by
  rw [sum_range_succ,last]
  congr 1
  calc _ = ∑ _i∈range k,a := sum_congr rfl fun i hi => other i (mem_range.mp hi)
       _ = _ := by simp

private theorem weight_pos {m : ℝ} (mp : 0<m) {k : ℕ} (room : (k:ℝ)≤m) (i : ℕ) :
    0≤weight m k i := by
  unfold weight
  split
  · exact div_nonneg (sub_nonneg.mpr room) mp.le
  · positivity

private theorem normalized {m : ℝ} (mp : 0<m) (k : ℕ) :
    ∑ i∈range (k+1),weight m k i=1 := by
  rw [rows k (weight m k) (1/m) ((m-k)/m) (fun i hi => if_neg (by omega : i≠k)) (if_pos rfl)]
  field_simp

private theorem mix {k : ℕ} (A B x y : ℕ→ℝ) (a0 : ∀i,0≤A i) (b0 : ∀i,0≤B i)
    (x0 : ∀ i,0≤x i ∧ x i≤1) (y0 : ∀ i,0≤y i ∧ y i≤1)
    (a1 : ∑ i∈range k,A i=1) (b1 : ∑ i∈range k,B i=1) :
    (∑ i∈range k,Real.sqrt (A i)*Real.sqrt (B i)*affinity (x i) (y i)) ≤
    affinity (∑ i∈range k,A i*x i) (∑ i∈range k,B i*y i) := by
  have half (f g : ℕ→ℝ) (hf : ∀ i,0≤f i) (hg : ∀ i,0≤g i) :
      ∑ i∈range k,Real.sqrt (A i)*Real.sqrt (B i)*(Real.sqrt (f i)*Real.sqrt (g i))
        ≤ Real.sqrt (∑ i∈range k,A i*f i) * Real.sqrt (∑ i∈range k,B i*g i) := by
    apply le_trans _ (Real.sum_sqrt_mul_sqrt_le (range k)
      (fun i => mul_nonneg (a0 i) (hf i)) (fun i => mul_nonneg (b0 i) (hg i)))
    apply le_of_eq
    apply sum_congr rfl
    intro i _
    rw [Real.sqrt_mul (a0 i),Real.sqrt_mul (b0 i)]
    ring
  have comp (a v : ℕ→ℝ) (h : ∑ i∈range k,a i=1) :
      (∑ i∈range k,a i*(1-v i))=1-∑ i∈range k,a i*v i := by
    simp only [mul_sub,mul_one,sum_sub_distrib,h]
  have first := half x y (fun i => (x0 i).1) (fun i => (y0 i).1)
  have next := half (fun i => 1-x i) (fun i => 1-y i)
    (fun i => sub_nonneg.mpr (x0 i).2) (fun i => sub_nonneg.mpr (y0 i).2)
  rw [comp A x a1,comp B y b1] at next
  simpa only [affinity,mul_add,sum_add_distrib] using add_le_add first next

private theorem improve {k : ℕ} {m M E : ℝ} (mp : 0<m) (sizes : m≤M) (room : 2*(k:ℝ)≤m)
    (nonneg : 0≤E) (x y : ℕ→ℝ) (x0 : ∀ i,0≤x i ∧ x i≤1) (y0 : ∀ i,0≤y i ∧ y i≤1)
    (child : ∀ i, 2-2*affinity (x i) (y i)≤E) :
    2-2*affinity (∑ i∈range (k+1),weight m k i*x i) (∑ i∈range (k+1),weight M k i*y i)
      ≤ 2*k*(M-m)^2/m^3+E := by
  let A := weight m k
  let B := weight M k
  let w (i : ℕ) := Real.sqrt (A i)*Real.sqrt (B i)
  have a0 : ∀ i,0≤A i := weight_pos mp (by linarith [Nat.cast_nonneg (α:=ℝ) k])
  have b0 : ∀ i,0≤B i := weight_pos (mp.trans_le sizes) (by linarith [Nat.cast_nonneg (α:=ℝ) k])
  have a1 : ∑ i∈range (k+1),A i=1 := normalized mp k
  have b1 : ∑ i∈range (k+1),B i=1 := normalized (mp.trans_le sizes) k
  have w0 (i : ℕ) : 0≤w i := by dsimp [w]; positivity
  have w1 : ∑ i∈range (k+1),w i≤1 := by
    simpa only [w,a1,b1,Real.sqrt_one,one_mul] using Real.sum_sqrt_mul_sqrt_le (range (k+1)) a0 b0
  have single := one_step mp sizes (Nat.cast_nonneg k) room
  have sumLoss : (∑ i∈range (k+1),(Real.sqrt (A i)-Real.sqrt (B i))^2)≤2*k*(M-m)^2/m^3 := by
    rw [rows k _ ((Real.sqrt (1/m)-Real.sqrt (1/M))^2)
      ((Real.sqrt ((m-k)/m)-Real.sqrt ((M-k)/M))^2) (fun i hi => by simp [A,B,weight,hi.ne])
      (by simp [A,B,weight])]
    exact single
  have equal : (∑ i∈range (k+1),(Real.sqrt (A i)-Real.sqrt (B i))^2)=
      2-2*∑ i∈range (k+1),w i := by
    calc _ = ∑ i∈range (k+1),(A i+B i-2*w i) := by
               apply sum_congr rfl
               intro i _
               dsimp only [w]
               nlinarith only [Real.sq_sqrt (a0 i),Real.sq_sqrt (b0 i)]
         _ = _ := by rw [sum_sub_distrib,sum_add_distrib,a1,b1,←mul_sum]; ring
  rw [equal] at sumLoss
  have hmix := mix A B x y a0 b0 x0 y0 a1 b1
  have step : (∑ i∈range (k+1),w i*(2-2*affinity (x i) (y i))) ≤ E := by
    calc _ ≤ ∑ i∈range (k+1),w i*E :=
               sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (child i) (w0 i)
         _ = (∑ i∈range (k+1),w i)*E := (sum_mul ..).symm
         _ ≤ 1*E := mul_le_mul_of_nonneg_right w1 nonneg
         _ = _ := one_mul _
  have expand : (∑ i∈range (k+1),w i*(2-2*affinity (x i) (y i))) =
      2*(∑ i∈range (k+1),w i)-2*∑ i∈range (k+1),w i*affinity (x i) (y i) := by
    rw [mul_sum,mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro _ _
    ring
  rw [expand] at step
  change (∑ i∈range (k+1),w i*affinity (x i) (y i)) ≤ _ at hmix
  change 2-2*affinity (∑ i∈range (k+1),A i*x i) (∑ i∈range (k+1),B i*y i)≤_
  linarith only [step,hmix,sumLoss]

open EqualityPatternSampling

private def nextCount (k i : ℕ) := if i=k then k+1 else k

private theorem branch_sum (m t k : ℕ) (f : List ℕ→ℝ) :
    expect m (t+1) k f = ∑ i∈range (k+1), weight m k i *
      expect m t (nextCount k i) (fun h => f (i::h)) := by
  rw [EqualityPatternSampling.expect,sum_range_succ]
  simp only [weight,nextCount,if_true]
  have old : (∑ i∈range k,(if i=k then ((m:ℝ)-k)/m else 1/m)*
      expect m t (if i=k then k+1 else k) (fun h => f (i::h))) =
      (1/(m:ℝ))*∑ i∈range k,expect m t k (fun h => f (i::h)) := by
    rw [mul_sum]
    exact sum_congr rfl fun i hi => by simp only [if_neg (mem_range.mp hi).ne]
  rw [old]
  ring

private theorem accumulated {m M t k : ℕ} (pos : 0<m) (sizes : m≤M) (room : 2*(k+t)≤m)
    (f : List ℕ→ℝ) (bounded : ∀ h,0≤f h ∧ f h≤1) :
    2-2*affinity (expect m t k f) (expect M t k f) ≤ (t:ℝ)*(2*k+t)*((M:ℝ)-m)^2/(m:ℝ)^3 := by
  induction t generalizing k f with
  | zero =>
    simp only [EqualityPatternSampling.expect,affinity_self (bounded []),Nat.cast_zero,zero_mul,zero_div]
    norm_num
  | succ t ih =>
    let x i := expect m t (nextCount k i) (fun h => f (i::h))
    let y i := expect M t (nextCount k i) (fun h => f (i::h))
    let E := (t:ℝ)*(2*(k+1)+t)*((M:ℝ)-m)^2/(m:ℝ)^3
    have p : 0<(m:ℝ) := by exact_mod_cast pos
    have cmp : (m:ℝ)≤M := by exact_mod_cast sizes
    have limit : 2*(k:ℝ)≤m := by exact_mod_cast (show 2*k≤m by omega)
    have nr (i : ℕ) : nextCount k i≤k+1 := by unfold nextCount; split <;> omega
    have xy (i : ℕ) : 0≤x i ∧ x i≤1 := expect_bounds pos (by have := nr i; omega) _ (fun _ => bounded _)
    have yy (i : ℕ) : 0≤y i ∧ y i≤1 := expect_bounds (pos.trans_le sizes)
      (by have := nr i; omega) _ (fun _ => bounded _)
    have child (i : ℕ) : 2-2*affinity (x i) (y i)≤E := by
      have c := ih (k:=nextCount k i) (by have := nr i; omega) (fun h => f (i::h)) (fun _ => bounded _)
      apply c.trans
      dsimp only [E]
      have cap : (nextCount k i:ℝ)≤(k:ℝ)+1 := by exact_mod_cast nr i
      gcongr
    rw [branch_sum m,branch_sum M]
    apply (improve p cmp limit (E:=E) (by dsimp [E]; positivity) x y xy yy child).trans
    dsimp only [E]
    rw [Nat.cast_succ,←add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have sq := sq_nonneg ((M:ℝ)-m)
    nlinarith only [sq]

/-- An arbitrary randomized equality-only test on t i.i.d. draws can use
any payoff in [0,1]. Its squared advantage is bounded uniformly. -/
theorem test_gap {m M t : ℕ} (positive : 0<m) (sizes : m≤M) (sample : 2*t≤m)
    (f : List ℕ→ℝ) (bounded : ∀ h, 0≤f h ∧ f h≤1) :
    (expect m t 0 f-expect M t 0 f)^2≤(t:ℝ)^2*((M:ℝ)-m)^2/(m:ℝ)^3 := by
  have first := bernoulli (expect_bounds positive (by omega : 0+t≤m) f bounded)
    (expect_bounds (positive.trans_le sizes) (by omega : 0+t≤M) f bounded)
  apply first.trans
  simpa only [Nat.cast_zero,mul_zero,zero_add,←sq] using
    accumulated (k:=0) positive sizes (by simpa using sample) f bounded

/-- For a gap of at most a square root, equality-only advantage is at most
the ratio of draws to labels through half the population size. -/
theorem linear_gap {m d t : ℕ} (positive : 0<m) (gap : d^2≤m) (sample : 2*t≤m)
    (f : List ℕ→ℝ) (bounded : ∀ h, 0≤f h ∧ f h≤1) :
    |expect m t 0 f-expect (m+d) t 0 f|≤(t:ℝ)/m := by
  have bound := test_gap positive (Nat.le_add_right m d) sample f bounded
  rw [Nat.cast_add,add_sub_cancel_left] at bound
  have hgap : (d:ℝ)^2≤m := by exact_mod_cast gap
  have mp : 0<(m:ℝ) := by exact_mod_cast positive
  apply abs_le_of_sq_le_sq (bound.trans ?_) (by positivity)
  rw [div_pow]
  apply (div_le_div_iff₀ (pow_pos mp _) (pow_pos mp _)).mpr
  have scaled := mul_le_mul_of_nonneg_left hgap (show 0≤(t:ℝ)^2*m^2 by positivity)
  nlinarith only [scaled]

/-- When the alphabet-size increment has square at most the original size,
a quarter as many draws as labels gives at most a quarter-point probability
difference, or at most 5/8 correct decisions with equal prior weights. -/
theorem quarter {m d t : ℕ} (positive : 0<m) (gap : d^2≤m) (sample : 4*t≤m)
    (f : List ℕ→ℝ) (bounded : ∀ h, 0≤f h ∧ f h≤1) :
    |expect m t 0 f-expect (m+d) t 0 f|≤1/4 ∧
    ((1-expect m t 0 f)+expect (m+d) t 0 f)/2≤5/8 := by
  have bound := linear_gap positive gap (by omega : 2*t≤m) f bounded
  have mpos : 0<(m:ℝ) := by exact_mod_cast positive
  have samp : 4*(t:ℝ)≤m := by exact_mod_cast sample
  have result := bound.trans (show (t:ℝ)/m≤1/4 by
    apply (div_le_iff₀ mpos).mpr
    linarith)
  exact ⟨result,by linarith only [(abs_le.mp result).1]⟩

/-- Directly over the two uniform sets of length-t words, with replacement.
The statistic receives only the first-occurrence encoding of the word. -/
theorem uniform_gap {m M t : ℕ} (positive : 0<m) (sizes : m≤M) (sample : 2*t≤m)
    (f : List ℕ→ℝ) (bounded : ∀ h, 0≤f h ∧ f h≤1) :
    ((∑ w : Fin t→Fin m,f (transcript w))/(m:ℝ)^t-
      (∑ w : Fin t→Fin M,f (transcript w))/(M:ℝ)^t)^2 ≤
      (t:ℝ)^2*((M:ℝ)-m)^2/(m:ℝ)^3 := by
  rw [uniform positive f,uniform (positive.trans_le sizes) f]
  exact test_gap positive sizes sample f bounded

end PrimeFactors.EqualityPatternSeparation
