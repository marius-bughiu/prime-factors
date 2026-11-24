import PrimeFactors.BitMarginals
import PrimeFactors.Fermat
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Multiplicity

namespace PrimeFactors

private def fourPowMod (m e : ℕ) : ℕ :=
  e.binaryRec (motive := fun _ => ℕ) (1%m) fun bit _ value =>
    let square := value*value % m
    if bit then (4*square)%m else square

private theorem fourPowMod_eq (m e : ℕ) : fourPowMod m e = 4^e % m := by
  induction e using Nat.binaryRec' with
  | z => simp [fourPowMod]
  | f bit n hn ih =>
    unfold fourPowMod at ih ⊢
    rw [Nat.binaryRec_eq _ _ (Or.inr hn), ih, Nat.bit_val, Nat.two_mul, pow_add, pow_add]
    cases bit <;> simp [Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mul_comm]

/-- Value of both symmetric exponential tags, using modular repeated squaring. -/
def ternaryCode (k h : ℕ) : ℕ := 2 * fourPowMod (3^(k+1)) h % 3^(k+1)

private theorem ternaryCode_eq (k h : ℕ) : ternaryCode k h = 2*4^h % 3^(k+1) := by
  simp [ternaryCode, fourPowMod_eq, Nat.mul_mod_mod]

private theorem odd_prime_dvd_exp {r : ℕ} (hr : r.Prime) (odd : Odd r) (k d : ℕ) :
    r^(k+1) ∣ (r+1)^d-1 ↔ r^k ∣ d := by
  have step : r.Coprime (r+1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have lte := Nat.emultiplicity_pow_sub_pow hr odd (x := r+1) (y := 1)
    (by simp) (hr.coprime_iff_not_dvd.mp step) d
  have selfVal : emultiplicity r r = 1 :=
    (Nat.finiteMultiplicity_iff.mpr ⟨hr.ne_one, hr.pos⟩).emultiplicity_self
  simp only [one_pow, Nat.add_sub_cancel, selfVal] at lte
  rw [pow_dvd_iff_le_emultiplicity, pow_dvd_iff_le_emultiplicity, lte, Nat.cast_add,
    Nat.cast_one, add_comm (k : ℕ∞)]
  exact WithTop.add_le_add_iff_left (by simp)

/-- At every odd prime, a weighted scalar retains the exponent modulo exactly r^k. -/
theorem odd_prime_readout_iff {r : ℕ} (hr : r.Prime) (odd : Odd r) (k x y : ℕ) :
    2*(r+1)^x ≡ 2*(r+1)^y [MOD r^(k+1)] ↔ x ≡ y [MOD r^k] := by
  wlog order : x ≤ y generalizing x y
  · rw [Nat.ModEq.comm, Nat.ModEq.comm (a := x), this y x (by omega)]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [pow_add (r+1) x d, ← Nat.mul_assoc]
  let c := 2*(r+1)^x
  have cop : (r^(k+1)).Coprime c := (Nat.Coprime.pow_left _ odd.coprime_two_right).mul_right
    (Nat.Coprime.pow _ _ (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)))
  change c ≡ c * (r+1)^d [MOD r^(k+1)] ↔ x ≡ x+d [MOD r^k]
  have cancel : c ≡ c*(r+1)^d [MOD r^(k+1)] ↔ 1 ≡ (r+1)^d [MOD r^(k+1)] := by
    constructor
    · intro h
      exact Nat.ModEq.cancel_left_of_coprime cop (by simpa using h)
    · intro h
      simpa using h.mul_left c
  rw [cancel, Nat.modEq_iff_dvd' (Nat.pow_pos (Nat.succ_pos _)), odd_prime_dvd_exp hr odd,
    Nat.modEq_iff_dvd' (Nat.le_add_right x d), Nat.add_sub_cancel_left]

theorem ternaryCode_eq_iff (k x y : ℕ) : ternaryCode k x = ternaryCode k y ↔ x ≡ y [MOD 3^k] := by
  rw [ternaryCode_eq, ternaryCode_eq]
  exact odd_prime_readout_iff Nat.prime_three (by decide) k x y

/-- Bit zero has unit weight. Each higher binary bit contributes the
corresponding power of 4 to the tag of that input word. -/
noncomputable def halfWordWeight (k x : ℕ) : ZMod (3^(k+1)) :=
  let places := ((2 : ℕ).digits (x/2)).mapIdx (fun i d => d*2^i)
  (places.map ((4 : ZMod (3^(k+1))) ^ ·)).prod

private theorem halfWordWeight_eq (k x : ℕ) : halfWordWeight k x = (4 : ZMod (3^(k+1)))^(x/2) := by
  unfold halfWordWeight
  have collect (places : List ℕ) : (places.map ((4 : ZMod (3^(k+1))) ^ ·)).prod = 4^places.sum := by
    induction places with
    | nil => simp
    | cons i places ih => simp [ih, pow_add]
  rw [collect, ← Nat.ofDigits_eq_sum_mapIdx, Nat.ofDigits_digits]

/-- One ordinary scalar contraction with a weight on each of the two input words. -/
noncomputable def exponentialReadout (n B k : ℕ) : ℕ :=
  (∑ xy ∈ acceptedBox n B, halfWordWeight k xy.1 * halfWordWeight k xy.2).val

theorem exponentialReadout_semiprime {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p < q) (inside : q < B) (upper : B ≤ p*q) (k : ℕ) :
    exponentialReadout (p*q) B k = ternaryCode k (p/2+q/2) := by
  have distinct : (p, q) ∉ ({(q, p)} : Finset (ℕ × ℕ)) := by simp [ordered.ne]
  rw [ternaryCode_eq, ← ZMod.val_natCast]
  push_cast
  simp only [exponentialReadout, acceptedBox_semiprime hp hq ordered inside upper,
    Finset.sum_insert distinct, Finset.sum_singleton, halfWordWeight_eq]
  rw [← pow_add, ← pow_add, Nat.add_comm (q/2) (p/2), two_mul]

/-- Recover one ternary digit per level using at most two modular powers. -/
def ternaryDecode (signal : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 =>
    let a := ternaryDecode signal k
    let r := 3^k
    let target := signal % 3^(k+2)
    if ternaryCode (k+1) a = target then a
    else if ternaryCode (k+1) (a+r) = target then a+r
    else a+2*r

/-- The executable digit lift recovers the true exponent modulo the exact
period, using only a representative of the observed scalar. -/
theorem ternaryDecode_correct {signal h : ℕ} (k : ℕ)
    (valid : signal % 3^(k+1) = ternaryCode k h) : ternaryDecode signal k = h % 3^k := by
  induction k with
  | zero => simp [ternaryDecode, Nat.mod_one]
  | succ k ih =>
    have smaller := congrArg (· % 3^(k+1)) valid
    have modDiv : 3^(k+1) ∣ 3^(k+1+1) := by rw [pow_succ _ (k+1)]; exact dvd_mul_right _ _
    dsimp only at smaller
    rw [ternaryCode_eq, Nat.mod_mod_of_dvd _ modDiv, Nat.mod_mod_of_dvd _ modDiv,
      ← ternaryCode_eq] at smaller
    have test (z : ℕ) : ternaryCode (k+1) z = signal % 3^(k+2) ↔ z % 3^(k+1) = h % 3^(k+1) := by
      rw [valid, ternaryCode_eq_iff]; rfl
    rw [ternaryDecode, ih smaller]
    simp only [test]
    have lo := Nat.mod_lt h (Nat.pow_pos (by decide : 0 < 3) : 0 < 3^k)
    have zeroFit : h % 3^k < 3^(k+1) := by rw [pow_succ]; omega
    have oneFit : h % 3^k + 3^k < 3^(k+1) := by rw [pow_succ]; omega
    rw [Nat.mod_eq_of_lt zeroFit, Nat.mod_eq_of_lt oneFit]
    split
    · assumption
    · split
      · assumption
      · have repr := Nat.mod_pow_succ (x := h) (b := 3) (k := k)
        have digit := Nat.mod_lt (h/3^k) (by decide : 0 < 3)
        rcases (show (h/3^k)%3 = 0 ∨ (h/3^k)%3 = 1 ∨ (h/3^k)%3 = 2 by omega)
          with d | d | d <;> rw [d] at repr <;> omega

private def combineFour (k a y : ℕ) : ℕ :=
  let m := 3^k
  y + m * (((a + 3*y)*m) % 4)

private theorem combineFour_spec (k a y : ℕ) :
    combineFour k a y ≡ a [MOD 4] ∧ combineFour k a y ≡ y [MOD 3^k] := by
  constructor
  · apply (ZMod.eq_iff_modEq_nat 4).mp
    have sq : ((3 : ZMod 4)^k)^2 = 1 := by
      rw [pow_right_comm, show (3:ZMod 4)^2 = 1 by decide, one_pow]
    unfold combineFour
    push_cast
    rw [ZMod.natCast_mod]
    push_cast
    calc
      _ = (y : ZMod 4) + (a+3*y)*((3:ZMod 4)^k)^2 := by ring
      _ = a + (4 : ZMod 4)*y := by rw [sq]; ring
      _ = a := by rw [show (4:ZMod 4)=0 by decide]; simp
  · exact Nat.add_mul_mod_self_left ..

/-- Use the known sum modulo 4 and shift the resulting CRT residue into a
public interval starting at lo. The period of possible sums is 4·3^k. -/
def sumFromExponentialReadout (n lo k signal : ℕ) : ℕ :=
  let residue := combineFour k (n+1) (2 + 2 * ternaryDecode signal k)
  lo + (((residue : ℤ) - lo) % (4*3^k : ℕ)).toNat

/-- One scalar determines the exact sum when the public interval is strictly
shorter than the CRT period. It therefore determines both quadratic roots. -/
theorem sumFromExponentialReadout_correct {p q B lo k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (po : Odd p) (qo : Odd q) (ordered : p < q) (inside : q < B) (upper : B ≤ p*q)
    (left : lo ≤ p+q) (width : p+q-lo < 4*3^k) :
    sumFromExponentialReadout (p*q) lo k (exponentialReadout (p*q) B k) = p+q := by
  let h := p/2+q/2
  have sig := exponentialReadout_semiprime hp hq ordered inside upper k
  have valid : exponentialReadout (p*q) B k % 3^(k+1) = ternaryCode k h := by
    rw [sig, ternaryCode_eq, Nat.mod_mod]
  have recover := ternaryDecode_correct k valid
  have collect : p+q = 2+2*h := by
    obtain ⟨u, pu⟩ := po
    obtain ⟨v, qv⟩ := qo
    dsimp [h]; omega
  have four : p+q ≡ p*q+1 [MOD 4] := by
    obtain ⟨u, rfl⟩ := po
    obtain ⟨v, rfl⟩ := qo
    apply Nat.modEq_iff_dvd.mpr
    exact ⟨(u:ℤ)*v, by push_cast; ring⟩
  have three : p+q ≡ 2+2*ternaryDecode (exponentialReadout (p*q) B k) k [MOD 3^k] := by
    rw [collect, recover]
    exact ((Nat.mod_modEq h (3^k)).symm.mul_left 2).add_left 2
  let cop := Nat.Coprime.pow_right k (by decide : Nat.Coprime 4 3)
  obtain ⟨r4, r3⟩ := combineFour_spec k (p*q+1) (2+2*ternaryDecode (exponentialReadout (p*q) B k) k)
  have crt := (Nat.modEq_and_modEq_iff_modEq_mul cop).mp ⟨r4.trans four.symm, r3.trans three.symm⟩
  have shift := (Int.natCast_modEq_iff.mpr crt).sub (Int.ModEq.refl (lo : ℤ))
  have small : (p : ℤ)+q-lo < ↑(4*3^k : ℕ) := by
    have castWidth : (↑(p+q-lo : ℕ) : ℤ) < ↑(4*3^k : ℕ) := by exact_mod_cast width
    simpa only [Nat.cast_sub left, Nat.cast_add] using castWidth
  have nonneg : 0 ≤ (p : ℤ)+q-lo := by omega
  unfold sumFromExponentialReadout
  change lo + (((_ : ℤ) - lo) % (4*3^k : ℕ)).toNat = p+q
  change _ % _ = ((↑(p+q : ℕ) : ℤ)-lo) % _ at shift
  rw [shift, Nat.cast_add, Int.emod_eq_of_lt nonneg small]
  omega

/-- The additional orientations (1,n) and (n,1) contribute a publicly known scalar. -/
theorem exponentialReadout_full_box {n B : ℕ} (hn : 1 < n) (wide : n < B) (k : ℕ) :
    (exponentialReadout n B k : ZMod (3^(k+1))) - 2 * 4^(n/2) = exponentialReadout n n k := by
  have left : (1, n) ∉ insert (n, 1) (acceptedBox n n) := by
    simp [acceptedBox, Nat.ne_of_lt hn]
  have right : (n, 1) ∉ acceptedBox n n := by simp [acceptedBox]
  simp only [exponentialReadout, ZMod.natCast_zmod_val, acceptedBox_past_target hn wide,
    Finset.sum_insert left, Finset.sum_insert right, halfWordWeight_eq]
  norm_num
  ring

/-- Restricting both factors to at least a gives an upper endpoint from the product. -/
theorem exponential_sum_window {a p q : ℕ} (ha : 0 < a) (ap : a ≤ p) (aq : a ≤ q) :
    ceilSqrt (4*(p*q)) ≤ p+q ∧ p+q ≤ a + p*q/a := by
  constructor
  · apply ceilSqrt_le_iff.mpr
    nlinarith [sq_nonneg ((p:ℤ)-q)]
  · have bound : p+q ≤ (a*a+p*q)/a := by
      apply (Nat.le_div_iff_mul_le ha).mpr
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le ap
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le aq
      nlinarith [Nat.zero_le (i*j)]
    simpa [Nat.mul_add_div ha] using bound

/-- A nonsquare product over a field guarantees two distinct simple roots of
its factor-sum quadratic. This is the local condition used before Hensel lifting. -/
theorem distinct_simple_factor_roots {K : Type*} [Field K] {x y : K}
    (nonsquare : ¬ IsSquare (x*y)) :
    x ≠ y ∧ (∀ z : K, z^2-(x+y)*z+x*y = 0 ↔ z=x ∨ z=y) ∧
      2*x-(x+y) ≠ 0 ∧ 2*y-(x+y) ≠ 0 := by
  have ne : x ≠ y := by rintro rfl; exact nonsquare ⟨x, rfl⟩
  refine ⟨ne, ?_, ?_, ?_⟩
  · intro z
    rw [show z^2-(x+y)*z+x*y = (z-x)*(z-y) by ring, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  · rwa [show 2*x-(x+y)=x-y by ring, sub_ne_zero]
  · rwa [show 2*y-(x+y)=y-x by ring, sub_ne_zero, ne_comm]

set_option maxRecDepth 10000 in
/-- Kernel-evaluated five-bit input square, with no factors supplied to the readout. -/
theorem exponential_readout_93 : exponentialReadout 93 32 2 = 17 ∧
    sumFromExponentialReadout 93 22 2 17 = 34 ∧ Nat.Prime 3 ∧ Nat.Prime 31 ∧ 3*31 = 93 := by
  have box : acceptedBox 93 32 = {(3,31),(31,3)} := by decide +kernel
  have distinct : (3,31) ∉ ({(31,3)} : Finset (ℕ × ℕ)) := by decide
  have signal : exponentialReadout 93 32 2 = 17 := by
    rw [exponentialReadout, box, Finset.sum_insert distinct, Finset.sum_singleton]
    simp only [halfWordWeight_eq]
    decide +kernel
  refine ⟨signal, ?_, by decide⟩
  rw [← signal, show 93 = 3*31 by decide]
  exact sumFromExponentialReadout_correct (p := 3) (q := 31) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end PrimeFactors
