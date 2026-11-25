import PrimeFactors.BinomialDivisorCover
import PrimeFactors.RoundedChebyshevWindows
import Mathlib.Analysis.MeanInequalities

/-! Cost of a complete dense interval cover under the binomial determinant
criteria. The charge is the number of coefficient slots in each polynomial. -/

namespace PrimeFactors.BinomialWindowWork

open Finset
open BinomialDivisorScale (weights)

private def B (k : ℕ) := ∑ i ∈ range (k+1), i
private def T (m : ℕ) := m+m.choose 2

private theorem twiceB (k : ℕ) : 2*B k=k*(k+1) := by
  induction k with
  | zero => simp [B]
  | succ k ih =>
    rw [show B (k+1)=B k+(k+1) from sum_range_succ ..]
    nlinarith only [ih]

private theorem twiceT (m : ℕ) : 2*T m=m*(m+1) := by
  induction m with
  | zero => decide
  | succ m ih =>
    simp only [T,Nat.choose_succ_succ,Nat.choose_one_right] at ih ⊢
    nlinarith only [ih]

private theorem triple_sum (k : ℕ) :
    (∑ i ∈ range (k+1), ∑ j ∈ range i, 3*(j+1)) = (k+2)*B k := by
  have twice (i : ℕ) : 2*(∑ j ∈ range i, 3*(j+1))=3*i*(i+1) := by
    induction i with
    | zero => simp
    | succ i ih => rw [sum_range_succ]; nlinarith only [ih]
  induction k with
  | zero => simp [B]
  | succ k ih =>
    rw [sum_range_succ,ih,show B (k+1)=B k+(k+1) from sum_range_succ ..]
    nlinarith only [twice (k+1),twiceB k]

/-- AM-GM on the triangular list 1; 1,2; ...; 1,...,k. The list has
B=k(k+1)/2 entries and mean (k+2)/3. -/
theorem factorial_upper (k : ℕ) :
    3^(∑ i ∈ range (k+1), i)*(∏ i ∈ range (k+1), i.factorial)≤(k+2)^(∑ i ∈ range (k+1), i) := by
  rcases k with _|k
  · decide
  let h := k+1
  let s : Finset (Σ _i : ℕ, ℕ) := (range (h+1)).sigma (fun i => range i)
  let f (p : Σ _i : ℕ, ℕ) : ℕ := 3*(p.2+1)
  have card : s.card=B h := by simp [s,B,card_sigma]
  have positive : 0<s.card := by rw [card]; have z := twiceB h; dsimp [h] at z ⊢; nlinarith
  have sm : ∑ p ∈ s, f p = (h+2)*s.card := by
    rw [card]; exact (sum_sigma ..).trans (triple_sum h)
  have pr : ∏ p ∈ s, f p=3^(B h) * ∏ i ∈ range (h+1), i.factorial := by
    dsimp only [s]
    rw [prod_sigma]
    simp only [f,prod_mul_distrib,prod_const,card_range,prod_range_add_one_eq_factorial]
    rw [prod_pow_eq_pow_sum]; rfl
  have posR : (0:ℝ)<s.card := by exact_mod_cast positive
  have upper := Real.geom_mean_le_arith_mean s (fun _ => (1:ℝ)) (fun p => (f p:ℝ))
    (fun _ _ => zero_le_one) (by simpa using posR) (fun _ _ => Nat.cast_nonneg _)
  simp only [one_mul,Real.rpow_one,sum_const,nsmul_eq_mul,mul_one] at upper
  have rs : ∑ p ∈ s, (f p:ℝ)=((h:ℝ)+2)*s.card := by exact_mod_cast sm
  rw [rs,mul_div_cancel_right₀ _ posR.ne'] at upper
  have final := Real.rpow_le_rpow (Real.rpow_nonneg (prod_nonneg (fun _ _ => Nat.cast_nonneg _)) _) upper posR.le
  rw [←Real.rpow_mul (prod_nonneg (fun _ _ => Nat.cast_nonneg _)),inv_mul_cancel₀ posR.ne',Real.rpow_one,
    Real.rpow_natCast] at final
  have nat : (∏ p ∈ s, f p)≤(h+2)^s.card := by exact_mod_cast final
  rw [pr,card] at nat
  exact nat

/-- Keep just the positive index times column scales: both the box comparison
and the classical LLL comparison imply this weaker strict inequality. -/
def volume (n D k m H : ℕ) := n^(m+m.choose 2)*weights (k+1) H < D^(m*(k+1))

private theorem volume_square {n D k m H : ℕ} (floor : D^2≤n) (cert : volume n D k m H) :
    n^(2*T m)*(weights (k+1) H)^2 < n^(m*(k+1)) := by
  have h := Nat.pow_lt_pow_left cert (by decide : 2≠0)
  simp only [mul_pow,←pow_mul] at h
  rw [Nat.mul_comm (m+m.choose 2) 2,Nat.mul_comm (m*(k+1)) 2,pow_mul D] at h
  exact h.trans_le (Nat.pow_le_pow_left floor _)

private theorem volume_root {n D k m H J : ℕ} (hn : 0<n) (floor : D^2≤n) (root : n≤J^4)
    (cert : volume n D k m H) : weights (k+1) H < J^(B k) := by
  by_contra! high
  have z := Nat.pow_lt_pow_left (volume_square floor cert) (by decide : 2≠0)
  simp only [mul_pow,←pow_mul] at z
  have exp : m*(k+1)*2≤2*T m*2+B k := by
    have s := sq_nonneg ((2:ℤ)*m-k)
    have b : (2:ℤ)*(B k)=k*((k:ℤ)+1) := by exact_mod_cast twiceB k
    have t : (2:ℤ)*(T m)=m*((m:ℤ)+1) := by exact_mod_cast twiceT m
    exact_mod_cast (show (m:ℤ)*(k+1)*2≤2*(T m:ℤ)*2+B k by nlinarith only [s,t,b,Int.natCast_nonneg k])
  have scale : n^(B k)≤(weights (k+1) H)^4 := calc
    _ ≤ (J^4)^(B k) := Nat.pow_le_pow_left root _
    _ = (J^(B k))^4 := by rw [←pow_mul,Nat.mul_comm 4,pow_mul]
    _ ≤ _ := Nat.pow_le_pow_left high 4
  exact (Nat.not_lt.mpr (calc
    n^(m*(k+1)*2) ≤ n^(2*T m*2+B k) := Nat.pow_le_pow_right hn exp
    _ = n^(2*T m*2)*n^(B k) := pow_add ..
    _ ≤ _ := Nat.mul_le_mul_left _ scale)) z

private theorem falling_lower (H k : ℕ) : (H+1-k)^(B k)≤
    (∏ i ∈ range (k+1), i.factorial)*weights (k+1) H := by
  rw [weights,←prod_mul_distrib,B,←prod_pow_eq_pow_sum]
  apply prod_le_prod'
  intro i hi
  rw [←Nat.descFactorial_eq_factorial_mul_choose]
  exact (Nat.pow_le_pow_left (by have := mem_range.mp hi; omega : H+1-k≤H+1-i) _).trans
    (Nat.pow_sub_le_descFactorial H i)

/-- A passing one-sided span H or centered radius H is limited linearly by the
number of coefficients, for every depth m. The bound uses only a public floor
D at or below sqrt(N). -/
theorem span_bound {n D k m H J : ℕ} (hn : 0<n) (floor : D^2≤n) (root : n≤J^4)
    (cert : volume n D k m H) : 3*(H+1-k)<(k+2)*J := by
  by_contra! bad
  have high := Nat.pow_le_pow_left bad (B k)
  simp only [mul_pow] at high
  have F := factorial_upper k
  change 3^(B k)*(∏ i ∈ range (k+1), i.factorial)≤(k+2)^(B k) at F
  have lf := falling_lower H k
  have combine := (Nat.mul_le_mul_right (J^(B k)) F).trans (high.trans (Nat.mul_le_mul_left _ lf))
  let Z := 3^(B k)*(∏ i ∈ range (k+1), i.factorial)
  have pos : 0<Z := Nat.mul_pos (by positivity) (prod_pos fun i _ => i.factorial_pos)
  have res : Z*J^(B k)≤Z*weights (k+1) H := by dsimp only [Z]; simpa only [Nat.mul_assoc] using combine
  exact (Nat.not_le_of_lt (volume_root hn floor root cert)) ((Nat.mul_le_mul_left_iff pos).mp res)

/-- Discarding the positive box overhead can only weaken the existing test.
V can be the actual centered product, which dominates the one-sided weights
on its positive half. -/
theorem of_box {n D k m H V : ℕ} (scales : weights (k+1) H≤V)
    (cert : n^(m+m.choose 2)*((k+1)^(k+1)*V)<(D^m)^(k+1)) : volume n D k m H := by
  rw [←pow_mul] at cert
  exact (Nat.mul_le_mul_left _ (scales.trans (Nat.le_mul_of_pos_left V (by positivity)))).trans_lt cert

/-- The numerical LLL condition likewise implies the relaxed volume test. -/
theorem of_lll {n D k m H V : ℕ} (scales : weights (k+1) H≤V)
    (cert : (k+1)^(2*(k+1))*2^(k*(k+1))*(n^(m+m.choose 2)*V)^4 < (D^m)^(4*(k+1))) :
    volume n D k m H := by
  apply (Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp
  calc
    _ ≤ (n^(m+m.choose 2)*V)^4 := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ scales) _
    _ ≤ _ := Nat.le_mul_of_pos_left _ (show 0<(k+1)^(2*(k+1))*2^(k*(k+1)) by positivity)
    _ < _ := cert
    _ = (D^(m*(k+1)))^4 := by rw [←pow_mul,←pow_mul]; congr 1; ring

theorem centered_scales (R k : ℕ) : weights (k+1) R ≤
    ∏ i ∈ range (k+1), (if i=0 then 1 else (R+i-1).choose i) := by
  apply prod_le_prod'
  intro i _
  split_ifs with zero
  · simp [zero]
  · exact Nat.choose_le_choose _ (by omega)

private theorem tiny_rank {n D k m H J : ℕ} (floor : D^2≤n) (root : n≤J^4)
    (big : 3≤J) (hm : 0<m) (mk : m≤k) (low : k≤2) (cert : volume n D k m H) : H<J := by
  by_contra! wide
  have hh := big.trans wide
  have c : H≤H.choose 2 := by
    rw [Nat.choose_two_right]
    exact (Nat.le_div_iff_mul_le (by decide)).mpr (Nat.mul_le_mul_left H (by omega))
  have two : weights 2 H=H := by simp [weights,prod_range_succ]
  have three : weights 3 H=H*(H.choose 2) := by simp [weights,prod_range_succ]
  have sq : n≤(weights 3 H)^2 := calc
    n ≤ J^4 := root
    _ ≤ H^4 := Nat.pow_le_pow_left wide _
    _ = (H*H)^2 := by ring
    _ ≤ (weights 3 H)^2 := Nat.pow_le_pow_left (three ▸ Nat.mul_le_mul_left H c) _
  have V := volume_square floor cert
  have choosePos : 0<H.choose 2 := (by omega : 0<H).trans_le c
  have one : 1≤(weights 3 H)^2 := by rw [three]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have one' : 1≤H^2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have cases : (k=1 ∧ m=1) ∨ (k=2 ∧ m=1) ∨ (k=2 ∧ m=2) := by omega
  rcases cases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · change n^2*weights 2 H^2<n^2 at V
    rw [two] at V
    exact (Nat.not_lt_of_ge (by simpa using Nat.mul_le_mul_left (n^2) one')) V
  · change n^2*weights 3 H^2<n^3 at V
    rw [pow_succ n 2] at V
    exact (Nat.not_lt_of_ge (Nat.mul_le_mul_left _ sq)) V
  · change n^6*weights 3 H^2<n^6 at V
    exact (Nat.not_lt_of_ge (by simpa using Nat.mul_le_mul_left (n^6) one)) V

/-- One polynomial with k+1 slots can pay for at most this many integer indices,
including both sides of a centered window. The depth and degree can change
between calls. -/
theorem slot_bound {n D k m H J : ℕ} (hn : 0<n) (floor : D^2≤n) (root : n≤J^4)
    (big : 3≤J) (hm : 0<m) (mk : m≤k) (cert : volume n D k m H) :
    6*(2*H+1)≤5*(k+1)*(J+3) := by
  by_cases low : k≤2
  · have less := tiny_rank floor root big hm mk low cert
    by_cases two : 2≤k
    · have cmp := Nat.mul_le_mul_right (J+3) (show 15≤5*(k+1) by omega)
      omega
    · have eq : k=1 := by omega
      subst k
      have eq : m=1 := by omega
      subst m
      have t := volume_square floor cert
      change n^2*(weights 2 H)^2<n^2 at t
      simp [weights,prod_range_succ] at t
      by_cases hz : H=0
      · subst H; omega
      · have cmp := Nat.le_mul_of_pos_right (n^2) (pow_pos (Nat.pos_of_ne_zero hz) 2)
        omega
  · have h := span_bound hn floor root cert
    have basic : 3*(H+1)≤3*(H+1-k)+3*k := by omega
    have cpp := Nat.mul_le_mul_right J (show 4*(k+2)≤5*(k+1) by omega)
    nlinarith only [h,basic,cpp,Nat.zero_le k]

/-- The factor guesses counted are odd d=2x+1 satisfying ceil(N/(2^1024-1))≤d≤sqrt(N).
On a 2048-bit product the lower endpoint already imposes the 1024-bit floor. -/
noncomputable def candidates (n : ℕ) : Finset ℕ :=
  Ico (((n+2^1024-2)/(2^1024-1))/2) ((n.sqrt+1)/2)

/-- The groups may overlap and may use different centers, valid divisor floors,
degrees, depths and radii. Only the number of index positions they cover and
their own sufficient volume comparisons enter. -/
theorem weighted_cover {ι : Type*} [DecidableEq ι] {n J g : ℕ} (hn : 0<n) (root : n≤J^4)
    (big : 3≤J) (runs : Finset ι) (covered : ι → Finset ℕ) (D k m H : ι → ℕ)
    (full : candidates n⊆runs.biUnion covered)
    (per : ∀ i∈runs, (D i)^2≤n ∧ 0<m i ∧ m i≤k i ∧ volume n (D i) (k i) (m i) (H i) ∧
      (covered i).card≤g*(2*H i+1)) : 6*(candidates n).card≤5*(J+3)*(g*∑ i ∈ runs, (k i+1)) := by
  have count := (card_le_card full).trans card_biUnion_le
  calc
    _ ≤ 6*∑ i ∈ runs, (covered i).card := Nat.mul_le_mul_left _ count
    _ = ∑ i ∈ runs, 6*(covered i).card := mul_sum ..
    _ ≤ ∑ i ∈ runs, (5*(J+3)*g)*(k i+1) := by
      apply sum_le_sum
      intro i hi
      obtain ⟨floor,hm,mk,pass,cap⟩ := per i hi
      have pay := slot_bound hn floor root big hm mk pass
      calc
        _ ≤ 6*(g*(2*H i+1)) := Nat.mul_le_mul_left 6 cap
        _ = g*(6*(2*H i+1)) := by ring
        _ ≤ g*(5*(k i+1)*(J+3)) := Nat.mul_le_mul_left g pay
        _ = _ := by ring
    _ = _ := by rw [←mul_sum,mul_assoc]

/-- Dense coefficient slots in the fixed published centered schedule. -/
def scheduled (n : ℕ) := FeasibleDivisorCover.dimension *
  (BinomialDivisorCover.locationsOf 5359 n false+BinomialDivisorCover.locationsOf 5359 n true)

/-- Same public count, optionally using a rounded upper bound u on sqrt(N). -/
private def countAt (n u : ℕ) (b : Bool) :=
  let stop := if b then u/2+1 else min (u/2+1) FeasibleDivisorCover.cut
  let width := 2*FeasibleDivisorCover.radius b
  let original := (stop-FeasibleDivisorCover.start n b+(width-1))/width
  (original+5358)/5359

private def scheduledAt (n u : ℕ) := FeasibleDivisorCover.dimension*(countAt n u false+countAt n u true)

private theorem scheduled_upper {n u : ℕ} (up : n.sqrt≤u) : scheduled n≤scheduledAt n u := by
  apply Nat.mul_le_mul_left
  have both (b : Bool) : BinomialDivisorCover.locationsOf 5359 n b≤countAt n u b := by
    unfold BinomialDivisorCover.locationsOf FeasibleDivisorCover.count countAt
    apply Nat.div_le_div_right
    apply Nat.add_le_add_right
    apply Nat.div_le_div_right
    apply Nat.add_le_add_right
    apply Nat.sub_le_sub_right
    have z : n.sqrt/2+1≤u/2+1 := Nat.add_le_add_right (Nat.div_le_div_right up) 1
    cases b
    · simp only [FeasibleDivisorCover.stop,Bool.false_eq_true,if_false]
      exact min_le_min_right FeasibleDivisorCover.cut z
    · simp only [FeasibleDivisorCover.stop,if_true]
      exact z
  exact Nat.add_le_add (both false) (both true)

set_option exponentiation.threshold 4096 in
/-- Any complete cover of the odd smaller-factor positions costs more than
2^508 coefficient slots on the fresh input, or more than 2^509 on the crossed
input. The published schedule is within factors 3.83 and 3.63, respectively.
No factor labels enter these calculations. -/
private theorem scaled_control_work {ι : Type*} [DecidableEq ι] {n e g : ℕ}
    (control : (n=ChebyshevQuarticScale.fresh ∧ e=508) ∨ (n=ChebyshevQuarticScale.crossed ∧ e=509))
    (runs : Finset ι) (covered : ι → Finset ℕ) (D k m H : ι → ℕ)
    (full : candidates n⊆runs.biUnion covered)
    (per : ∀ i∈runs, (D i)^2≤n ∧ 0<m i ∧ m i≤k i ∧ volume n (D i) (k i) (m i) (H i) ∧
      (covered i).card≤g*(2*H i+1)) :
    let cost := g*∑ i ∈ runs, (k i+1)
    2^e < cost ∧ 100*scheduled n < (if e=508 then 383 else 363)*cost := by
  let ratio := if e=508 then 383 else 363
  obtain ⟨J,t,u,hn,root,big,rad,up,price,near⟩ : ∃ J t u : ℕ, 0<n ∧ n≤J^4 ∧ 3≤J ∧ t*t≤n ∧ n<u^2 ∧
      5*(J+3)*2^e<6*((t+1)/2-((n+2^1024-2)/(2^1024-1))/2) ∧
      5*(J+3)*100*scheduledAt n u < ratio*(6*((t+1)/2-((n+2^1024-2)/(2^1024-1))/2)) := by
    rcases control with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨3844*2^500,57719*2^1008,57720*2^1008,by decide +kernel⟩
    · exact ⟨3551*2^500,49228*2^1008,49229*2^1008,by decide +kernel⟩
  have pay := weighted_cover hn root big runs covered D k m H full per
  have hs := Nat.le_sqrt.mpr rad
  rw [candidates,Nat.card_Ico] at pay
  have lower := (Nat.mul_le_mul_left 6 (Nat.sub_le_sub_right
    (Nat.div_le_div_right (Nat.add_le_add_right hs 1)) _)).trans pay
  refine ⟨Nat.lt_of_mul_lt_mul_left (price.trans_le lower),?_⟩
  have cmp := (Nat.mul_le_mul_left (5*(J+3)*100) (scheduled_upper (Nat.sqrt_lt'.mpr up).le)).trans_lt
    (near.trans_le (Nat.mul_le_mul_left ratio lower))
  apply Nat.lt_of_mul_lt_mul_left (a:=5*(J+3))
  change 5*(J+3)*(100*scheduled n)<5*(J+3)*(ratio*(g*∑ i∈runs, (k i+1)))
  convert cmp using 1 <;> ring

/-- Cost of any dense ordinary binomial cover, allowing a mixture of one-sided
and centered windows. The published schedule is within a factor of four. -/
theorem control_work {ι : Type*} [DecidableEq ι] {n e : ℕ}
    (control : (n=ChebyshevQuarticScale.fresh ∧ e=508) ∨ (n=ChebyshevQuarticScale.crossed ∧ e=509))
    (runs : Finset ι) (covered : ι → Finset ℕ) (D k m H : ι → ℕ)
    (full : candidates n⊆runs.biUnion covered)
    (per : ∀ i∈runs, (D i)^2≤n ∧ 0<m i ∧ m i≤k i ∧ volume n (D i) (k i) (m i) (H i) ∧
      (covered i).card≤2*H i+1) :
    let cost := ∑ i ∈ runs, (k i+1)
    2^e < cost ∧ 100*scheduled n < (if e=508 then 383 else 363)*cost := by
  simpa only [one_mul] using scaled_control_work (g:=1) control runs covered D k m H full
    (by simpa only [one_mul] using per)

/-- The rounded degree-i scale used in the published construction dominates
choose(U,i), although its window covers the longer span 4U. -/
theorem rounded_scales (U k : ℕ) : weights (k+1) U ≤ ∏ i ∈ range (k+1), RoundedChebyshevWindows.weight U i := by
  apply prod_le_prod'
  intro i _
  have q : U.choose i≤U^i/i.factorial := (Nat.le_div_iff_mul_le i.factorial_pos).mpr
    (by simpa only [Nat.descFactorial_eq_factorial_mul_choose,mul_comm] using Nat.descFactorial_le_pow U i)
  have w : U^i≤ChebyshevDivisorWindow.weight U i := by
    cases i with
    | zero => rfl
    | succ i => exact Nat.le_mul_of_pos_left _ (by decide : 0<2)
  exact ((q.trans (Nat.div_le_div_right w)).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)

/-- The degree charge survives mixed covers using the published rounded weights.
An ordinary window uses at most 2H+1 positions, a rounded one at most 4H+1.
Thus 2^e < 2*cost for e=508 fresh or 509 crossed. -/
theorem rounded_or_ordinary_work {ι : Type*} [DecidableEq ι] {n e : ℕ}
    (control : (n=ChebyshevQuarticScale.fresh ∧ e=508) ∨ (n=ChebyshevQuarticScale.crossed ∧ e=509))
    (runs : Finset ι) (covered : ι → Finset ℕ) (D k m H : ι → ℕ)
    (full : candidates n⊆runs.biUnion covered)
    (per : ∀ i∈runs, (D i)^2≤n ∧ 0<m i ∧ m i≤k i ∧ volume n (D i) (k i) (m i) (H i) ∧
      (covered i).card≤4*H i+1) :
    let cost := ∑ i ∈ runs, (k i+1)
    2^e < 2*cost ∧ 100*scheduled n < (if e=508 then 766 else 726)*cost := by
  have q := scaled_control_work (g:=2) control runs covered D k m H full (by
    intro i hi
    obtain ⟨floor,hm,mk,pass,cap⟩ := per i hi
    exact ⟨floor,hm,mk,pass,by omega⟩)
  refine ⟨q.1,?_⟩
  have last := q.2
  split_ifs at last ⊢ <;> omega

end PrimeFactors.BinomialWindowWork
