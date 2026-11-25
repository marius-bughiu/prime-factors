import PrimeFactors.RecursiveUnitWindows

/-! Degree-512 comparison with the older lower-coordinate error bound. -/

namespace PrimeFactors.RecursiveUnitWindows

open Polynomial Finset

set_option maxRecDepth 16000
set_option exponentiation.threshold 8192

/-- Small certificates for the binary logarithms at every sixteenth degree. -/
private def denominatorBits : List ℕ :=
  [0,50,130,221,321,429,536,649,768,886,1009,1135,1260,1389,1522,1654,1783,
   1920,2056,2193,2333,2473,2613,2758,2901,3046,3189,3335,3482,3630,3778,3928,4081]

private def rowBits (w i : ℕ) := 2+w*i-denominatorBits.getD (i/16) 0

set_option exponentiation.threshold 8192 in
private theorem denominatorBlocks : ∀ j : Fin 33,
    (2:ℕ)^(denominatorBits.getD j.val 0) ≤ ThreeUnitFactorialWindows.denominator (16*j.val) ∧
    ThreeUnitFactorialWindows.denominator (16*j.val) < (2:ℕ)^(denominatorBits.getD j.val 0+1) := by
  decide +kernel

private theorem weight_upper (w i : ℕ) (hi : i<513) :
    weight ThreeUnitFactorialWindows.denominator (2^w) i ≤ 2^(rowBits w i) := by
  let d := ThreeUnitFactorialWindows.denominator i
  have pos : 0<d := ThreeUnitFactorialWindows.denominator_pos _
  have l : (2:ℕ)^(denominatorBits.getD (i/16) 0) ≤ d :=
    (denominatorBlocks ⟨i/16,by omega⟩).1.trans <| Nat.le_of_dvd pos <|
      ThreeUnitFactorialWindows.denominator_dvd (by change 16*(i/16) ≤ i; omega)
  apply Nat.div_le_of_le_mul
  calc
    4*(2^w)^i = (2:ℕ)^(2+w*i) := by rw [pow_add,pow_mul]; norm_num
    _ ≤ 2^(denominatorBits.getD (i/16) 0+rowBits w i) := Nat.pow_le_pow_right (by decide) (by unfold rowBits; omega)
    _ = 2^(denominatorBits.getD (i/16) 0)*2^(rowBits w i) := pow_add ..
    _ ≤ d*2^(rowBits w i) := Nat.mul_le_mul_right _ l

set_option maxRecDepth 8192 in
private theorem bits512 : ∑ i ∈ range 513, rowBits 517 i=66975489 := by decide +kernel

private theorem cost_from_exponents {n m r a b e : ℕ} (big : 2^2047≤n) (W : ℕ→ℕ)
    (count : r^r≤2^a) (prod : (∏ i∈range r,W i)≤2^b)
    (add : a+b<e) (le : m+m.choose 2 ≤ m*r) (budget : e+2047*(m+m.choose 2)≤1023*(m*r)) :
    n^(m+m.choose 2) * (r^r*∏ i : Fin r, W i.val) < ((CoupledDivisorWindow.lower n)^m)^r := by
  rw [Fin.prod_univ_eq_prod_range W r,mul_comm,←pow_mul]
  apply CoupledDivisorWindow.coupled_cost big _ le budget
  exact (Nat.mul_le_mul count prod).trans_lt ((pow_add (2:ℕ) a b) ▸ Nat.pow_lt_pow_right (by decide) add)

private theorem volume_pow {r : ℕ} (w b : ℕ→ℕ) (cap : ∀ i<r, w i≤2^(b i)) :
    (∏ i∈range r, w i) ≤ 2^(∑ i∈range r, b i) := by
  rw [← prod_pow_eq_pow_sum]
  exact prod_le_prod' (fun i h => cap _ (mem_range.mp h))

/-- Degree 512 at index width 2^519. Evaluating only the sum of small
exponents avoids building a 67-million-bit numerical volume. -/
theorem room512 {n : ℕ} (large : 2^2047≤n) :
    n^(256+(256:ℕ).choose 2)*(513^513*∏ i : Fin 513, weight ThreeUnitFactorialWindows.denominator (2^517) i.val)<
      ((CoupledDivisorWindow.lower n)^256)^513 := by
  apply cost_from_exponents (a:=5130) (b:=66975489) (e:=66980620) large
  · decide +kernel
  · rw [←bits512]
    exact volume_pow _ _ (fun i hi => weight_upper 517 i hi)
  · decide
  · rw [Nat.choose_two_right]; decide
  · rw [Nat.choose_two_right]; decide

private def factorialBits : List ℕ :=
  [0,44,117,202,295,394,498,605,716,829,945,1064,1184,1306,1430,1556,1683,
   1812,1942,2074,2206,2340,2475,2611,2748,2886,3024,3164,3305,3446,3588,3731,3875]

set_option exponentiation.threshold 8192 in
private theorem factorialBlocks : ∀ j : Fin 33,
    (16*j.val).factorial < (2:ℕ)^(factorialBits.getD j.val 0+1) := by decide +kernel

private def priorBits (i : ℕ) : ℕ := if i=0 then 0 else max
  (1+517*i-(denominatorBits.getD ((i+15)/16) 0+1))
  (519*(i-1)-(factorialBits.getD ((i-1+15)/16) 0+1))

private theorem bounded_div {b e d : ℕ} (hd : 0<d) (bound : d≤2^e) :
    (2:ℕ)^(b-e) ≤ max 1 (2^b/d) := by
  by_cases le : e≤b
  · apply le_trans _ (le_max_right ..)
    apply (Nat.le_div_iff_mul_le (hd)).mpr
    calc
      _ ≤ 2^(b-e)*2^e := Nat.mul_le_mul_left _ bound
      _ = 2^b := by rw [←pow_add,Nat.sub_add_cancel le]
  · simpa only [Nat.sub_eq_zero_of_le (by omega : b≤e),pow_zero] using (le_max_left 1 (2^b/d))

private theorem prior_lower {i : ℕ} (hi : i<513) :
    (2:ℕ)^(priorBits i) ≤ ThreeUnitFactorialWindows.weight (2^517) i := by
  let d := ThreeUnitFactorialWindows.denominator i
  by_cases z : i=0
  · subst i; decide
  have b : i≤16*((i+15)/16) := by omega
  have cap : d≤2^(denominatorBits.getD ((i+15)/16) 0+1) :=
    (Nat.le_of_dvd (ThreeUnitFactorialWindows.denominator_pos _) (ThreeUnitFactorialWindows.denominator_dvd b)).trans
      (denominatorBlocks ⟨(i+15)/16,by omega⟩).2.le
  have b' : i-1≤16*((i-1+15)/16) := by omega
  have fac : (i-1).factorial≤2^(factorialBits.getD ((i-1+15)/16) 0+1) :=
    (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_dvd_factorial b')).trans
      (factorialBlocks ⟨(i-1+15)/16,by omega⟩).le
  have c : ChebyshevDivisorWindow.weight (2^517) i=2^(1+517*i) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero z
    rw [pow_add (2:ℕ) 1 (517*(j+1)),pow_mul (2:ℕ) 517 (j+1),pow_one]
    rfl
  have first := bounded_div (b:=1+517*i) (ThreeUnitFactorialWindows.denominator_pos i) cap
  have second := bounded_div (b:=519*(i-1)) (Nat.factorial_pos _) fac
  have tail := Finset.single_le_sum (f:=fun j => (4*(2^517:ℕ))^j/j.factorial)
    (fun _ _ => Nat.zero_le _) (mem_range.mpr (show i-1 < i by omega))
  change (4*(2:ℕ)^517)^(i-1)/(i-1).factorial ≤ ∑ j ∈ range i, (4*(2:ℕ)^517)^j/j.factorial at tail
  rw [show 4*(2:ℕ)^517=2^519 by decide,←pow_mul] at tail
  rw [priorBits,if_neg z,ThreeUnitFactorialWindows.weight,c,show 4*(2:ℕ)^517=2^519 by decide]
  rcases le_total (1+517*i-(denominatorBits.getD ((i+15)/16) 0+1))
    (519*(i-1)-(factorialBits.getD ((i-1+15)/16) 0+1)) with le|le
  · rw [max_eq_right le]
    refine second.trans (max_le (Nat.succ_le_succ (Nat.zero_le _)) ?_)
    exact tail.trans ((Nat.le_add_left _ _).trans (Nat.le_succ _))
  · rw [max_eq_left le]
    refine first.trans (max_le (Nat.succ_le_succ (Nat.zero_le _)) ?_)
    exact (Nat.le_add_right _ _).trans (Nat.le_succ _)

set_option maxRecDepth 8192 in
private theorem prior_bits512 : ∑ i ∈ range 513, priorBits i=67021506 := by decide +kernel

/-- The preceding ordinary-binomial-tail majorant exceeds the entire uniform
budget at the same degree, using lower powers before any dimension loss. -/
theorem prior_box_lower : (2:ℕ)^67021506 ≤
    ∏ i ∈ range 513, ThreeUnitFactorialWindows.weight (2^517) i := by
  have h := prod_le_prod' (s:=range 513) (fun i hi => prior_lower (Finset.mem_range.mp hi))
  rwa [prod_pow_eq_pow_sum,prior_bits512] at h

theorem uniform_window512 {n : ℕ} (large : 2^2047≤n)
    (cop : n.Coprime (ThreeUnitFactorialWindows.denominator 512))
    {c t : ℤ} (odd : IsCoprime (2:ℤ) (n:ℤ)) (anchor : (n:ℤ)∣c+2*t) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤512 ∧ ∀ (x : ℕ) (d : ℤ),
      d∣(n:ℤ) → d=c+2*(x:ℤ) → (CoupledDivisorWindow.lower n:ℤ)≤d →
      x≤2^519 → F.eval (x:ℤ)=0 := by
  have hn := (by positivity : 0<(2:ℕ)^2047).trans_le large
  have hd := (by positivity : 0<(2:ℕ)^1023).trans_le (CoupledDivisorWindow.lower_size large)
  simpa only [show 4*(2:ℕ)^517=2^519 by decide] using
    unit_window (k:=512) (m:=256) (U:=2^517) (by decide) hn hd RecursiveUnitScale.denominator_step
      (by decide) cop (room512 large) odd anchor

end PrimeFactors.RecursiveUnitWindows
