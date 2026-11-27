import PrimeFactors.Certificate
import Mathlib.Data.Nat.Choose.Central
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Dyadic totals of units and their integer factorial ratios. The arithmetic
input is only the product. The primes occur in the correctness statements. -/

namespace PrimeFactors.DyadicTotativeMasks

/-- Public endpoint at level `j`. -/
def endpoint (n j : ℕ) : ℕ := n / 2 ^ j

/-- Binary digit, indexed from zero. -/
def digit (n j : ℕ) : ℕ := endpoint n j % 2

/-- Integral form of `A! / (⌊A/2⌋!)²`. -/
def coefficient (A : ℕ) : ℕ :=
  if A % 2 = 0 then (A / 2).centralBinom else A * (A / 2).centralBinom

theorem coefficient_pos (A : ℕ) : 0 < coefficient A := by
  unfold coefficient
  split_ifs with h
  · exact Nat.centralBinom_pos _
  · exact Nat.mul_pos (by omega) (Nat.centralBinom_pos _)

theorem coefficient_identity (A : ℕ) :
    coefficient A * (A / 2).factorial * (A / 2).factorial = A.factorial := by
  let m := A / 2
  have base : m.centralBinom * m.factorial * m.factorial = (2*m).factorial := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    simpa only [show 2*m-m=m by omega] using
      Nat.choose_mul_factorial_mul_factorial (show m ≤ 2*m by omega)
  change (if A%2=0 then m.centralBinom else A*m.centralBinom) * _ * _ = _
  split_ifs with h
  · convert base using 2
    dsimp [m]
    omega
  · have rec := Nat.factorial_succ (2*m)
    have odd : A = 2*m+1 := by dsimp [m]; omega
    calc
      _ = A*(m.centralBinom*m.factorial*m.factorial) := by change A*m.centralBinom*m.factorial*m.factorial = _; ring
      _ = A*(2*m).factorial := by rw [base]
      _ = A.factorial := by conv_rhs => rw [odd, rec]; rw [← odd]

private theorem factorial_below {p A : ℕ} (pp : p.Prime) (small : A<p^2) :
    padicValNat p A.factorial = A/p := by
  letI : Fact p.Prime := ⟨pp⟩
  rcases eq_or_ne A 0 with rfl | h
  · simp
  · rw [padicValNat_factorial (Nat.log_lt_of_lt_pow h small),
        show Finset.Ico 1 2 = {1} by decide]
    simp

private theorem scaled_div (p q d : ℕ) (hp : 0<p) : p*q/d/p=q/d := by
  rw [Nat.div_div_eq_div_mul, mul_comm d p, Nat.mul_div_mul_left _ _ hp]

private theorem half_div (A p : ℕ) : A/2/p=A/p/2 := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm 2 p]

/-- Before the first prime square, the prime valuation reads a bit of the
other factor. No primality assumption on that other factor is needed here. -/
theorem valuation {p q j : ℕ} (pp : p.Prime) (small : endpoint (p*q) j < p^2) :
    padicValNat p (coefficient (endpoint (p*q) j)) = digit q j := by
  letI : Fact p.Prime := ⟨pp⟩
  let A := endpoint (p*q) j
  have hA : A < p^2 := small
  have hh : A/2 < p^2 := by omega
  have e := congrArg (padicValNat p) (coefficient_identity A)
  rw [padicValNat.mul (Nat.mul_ne_zero (coefficient_pos _).ne' (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (coefficient_pos _).ne' (Nat.factorial_ne_zero _),
      factorial_below pp hA, factorial_below pp hh, half_div] at e
  have divA : A/p=endpoint q j := scaled_div _ _ _ pp.pos
  rw [divA] at e
  change padicValNat p (coefficient A) = endpoint q j % 2
  omega

private theorem small_rows {p q j : ℕ} (pp : p.Prime) (ordered : p<q)
    (balanced : q<2*p) (hj : 1≤j) :
    endpoint (p*q) j < p^2 ∧ endpoint (p*q) j < q^2 := by
  have d : 2≤2^j := Nat.pow_le_pow_right (n:=2) (by decide) hj
  have half : endpoint (p*q) j ≤ p*q/2 := Nat.div_le_div_left d (by decide)
  have pq : p*q < p*(2*p) := Nat.mul_lt_mul_of_pos_left balanced pp.pos
  have sq : p*q/2<p^2 := (Nat.div_lt_iff_lt_mul (by decide)).2 (by nlinarith)
  exact ⟨half.trans_lt sq, (half.trans_lt sq).trans (by nlinarith)⟩

private theorem gcd_at_digit {p q j : ℕ} (pp : p.Prime) (small : endpoint (p*q) j < p^2) :
    (coefficient (endpoint (p*q) j)).gcd p = (if digit q j=1 then p else 1) := by
  letI : Fact p.Prime := ⟨pp⟩
  have dvd := dvd_iff_padicValNat_ne_zero (p:=p) (coefficient_pos (endpoint (p*q) j)).ne'
  rw [valuation pp small] at dvd
  rw [Nat.gcd_comm]
  have bit : digit q j<2 := Nat.mod_lt _ (by decide)
  split_ifs with h
  · exact Nat.gcd_eq_left (dvd.mpr (by omega))
  · exact pp.coprime_iff_not_dvd.mpr (by rw [dvd]; omega)

/-- From N alone, a single coefficient gcd selects p by the bit of q and q
by the bit of p. A differing bit gives a proper split. -/
theorem gcd_mask {p q j : ℕ} (pp : p.Prime) (qp : q.Prime) (ordered : p<q)
    (balanced : q<2*p) (hj : 1≤j) :
    (coefficient (endpoint (p*q) j)).gcd (p*q) =
      (if digit q j=1 then p else 1) * (if digit p j=1 then q else 1) := by
  obtain ⟨sp,sq⟩ := small_rows pp ordered balanced hj
  rw [Nat.Coprime.gcd_mul _ ((Nat.coprime_primes pp qp).mpr ordered.ne),
    gcd_at_digit pp sp]
  rw [mul_comm p q] at sq ⊢
  rw [gcd_at_digit qp sq]


/-- Counts positive integers at or below the endpoint coprime to the input. -/
noncomputable def unitCount (n A : ℕ) : ℕ := ((Finset.range A).filter (fun i => (i+1).Coprime n)).card

private theorem unit_count {p q A : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (small : A<p*q) : unitCount (p*q) A + A/p + A/q = A := by
  induction A with
  | zero => simp [unitCount]
  | succ A ih =>
    have prev := ih (by omega)
    have next : unitCount (p*q) (A+1) = unitCount (p*q) A +
        (if (A+1).Coprime (p*q) then 1 else 0) := by
      simp only [unitCount, Finset.range_add_one, Finset.filter_insert]
      split_ifs <;> simp [Finset.mem_filter]
    have cp : (A+1).Coprime (p*q) ↔ ¬p∣A+1 ∧ ¬q∣A+1 := by
      rw [Nat.coprime_mul_iff_right]
      exact and_congr (Nat.coprime_comm.trans pp.coprime_iff_not_dvd)
        (Nat.coprime_comm.trans qp.coprime_iff_not_dvd)
    have disjoint (h : p∣A+1) (k : q∣A+1) : False :=
      (Nat.not_le.mpr small) (Nat.le_of_dvd (by omega)
        (((Nat.coprime_primes pp qp).mpr ne).mul_dvd_of_dvd_of_dvd h k))
    rw [next]
    by_cases h : p∣A+1 <;> by_cases k : q∣A+1
    · exact (disjoint h k).elim
    · simp only [cp, h, k, not_true_eq_false, not_false_eq_true, false_and, if_false, add_zero,
        Nat.succ_div_of_dvd h, Nat.succ_div_of_not_dvd k]
      omega
    · simp only [cp, h, k, not_true_eq_false, not_false_eq_true, true_and, if_false, add_zero,
        Nat.succ_div_of_not_dvd h, Nat.succ_div_of_dvd k]
      omega
    · simp only [cp, h, k, not_false_eq_true, and_self, if_true,
        Nat.succ_div_of_not_dvd h, Nat.succ_div_of_not_dvd k]
      omega

private theorem endpoint_succ (n j : ℕ) : endpoint n (j+1) = endpoint n j/2 := by
  simp [endpoint, pow_succ, Nat.div_div_eq_div_mul]

/-- At any positive depth the count gives the sum of the *truncated*
factors. This bound is independent of the distance between the factors. -/
theorem truncated_sum {p q j : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q) (hj : 1≤j) :
    unitCount (p*q) (endpoint (p*q) j) + endpoint p j + endpoint q j =
      endpoint (p*q) j := by
  have d : 2≤2^j := Nat.pow_le_pow_right (n:=2) (by decide) hj
  have small : endpoint (p*q) j < p*q :=
    Nat.div_lt_self (Nat.mul_pos pp.pos qp.pos) (by omega : 1<2^j)
  have h := unit_count pp qp ne small
  have h1 : endpoint (p*q) j/p=endpoint q j := scaled_div _ _ _ pp.pos
  have h2 : endpoint (p*q) j/q=endpoint p j := by
    rw [mul_comm p q]
    exact scaled_div _ _ _ qp.pos
  rw [h1,h2] at h
  omega

/-- A single exact count at half the modulus already gives the full trace
for odd primes. Consequently a fast half-count oracle would suffice to factor. -/
theorem half_count_trace {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (hp : p%2=1) (hq : q%2=1) :
    2 * unitCount (p*q) (endpoint (p*q) 1) + p + q = p*q+1 := by
  have h := truncated_sum pp qp ne (by decide : 1≤1)
  simp only [endpoint,pow_one] at h ⊢
  have odd : (p*q)%2=1 := by rw [Nat.mul_mod,hp,hq]
  omega

/-- Adding the public endpoint digit to twice the half count minus the
whole count eliminates the bulk count and retains the sum of factor bits. -/
theorem unit_contrast {p q j : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q) (hj : 1≤j) :
    2 * unitCount (p*q) (endpoint (p*q) (j+1)) + digit (p*q) j =
      unitCount (p*q) (endpoint (p*q) j) + digit p j + digit q j := by
  have h := truncated_sum pp qp ne hj
  have hh := truncated_sum pp qp ne (show 1≤j+1 by omega)
  rw [endpoint_succ,endpoint_succ,endpoint_succ] at hh
  rw [endpoint_succ]
  unfold digit
  omega

/-- The equal leading and low bits can be skipped for odd equal-width factors.
With components in [2^k, 2^(k+1)), the useful positions are 1 through k−1. -/
theorem exists_differing_digit {p q k : ℕ} (ne : p≠q) (oddP : p%2=1) (oddQ : q%2=1)
    (plo : 2^k≤p) (phi : p<2^(k+1)) (qlo : 2^k≤q) (qhi : q<2^(k+1)) :
    ∃ j, 1≤j ∧ j<k ∧ digit p j≠digit q j := by
  by_contra! all
  apply ne
  apply Nat.eq_of_testBit_eq
  intro i
  have eq : digit p i=digit q i := by
    rcases eq_or_ne i 0 with rfl | hi
    · simpa [digit,endpoint] using oddP.trans oddQ.symm
    rcases lt_trichotomy i k with h | rfl | h
    · exact all i (by omega) h
    · rw [pow_succ] at phi qhi
      have ep : endpoint p i=1 := Nat.div_eq_of_lt_le (by simpa using plo) (by simpa [mul_comm] using phi)
      have eq : endpoint q i=1 := Nat.div_eq_of_lt_le (by simpa using qlo) (by simpa [mul_comm] using qhi)
      simp [digit,ep,eq]
    · have bound : 2^(k+1)≤2^i := Nat.pow_le_pow_right (n:=2) (by decide) h
      simp [digit,endpoint,Nat.div_eq_of_lt (phi.trans_le bound),Nat.div_eq_of_lt (qhi.trans_le bound)]
  simpa only [Nat.testBit_to_div_mod] using congrArg (fun b : ℕ => decide (b=1)) eq

/-- The schedule guarantees a proper divisor for every distinct equal-width
pair of odd primes. It only bounds the number of gcd queries. -/
theorem exists_split {p q k : ℕ} (pp : p.Prime) (qp : q.Prime) (ordered : p<q)
    (oddP : p%2=1) (oddQ : q%2=1)
    (plo : 2^k≤p) (phi : p<2^(k+1)) (qlo : 2^k≤q) (qhi : q<2^(k+1)) :
    ∃ j, 1≤j ∧ j<k ∧
      ((coefficient (endpoint (p*q) j)).gcd (p*q)=p ∨
       (coefficient (endpoint (p*q) j)).gcd (p*q)=q) := by
  obtain ⟨j,hj,hi,diff⟩ := exists_differing_digit ordered.ne oddP oddQ plo phi qlo qhi
  have balanced : q<2*p := by rw [pow_succ] at qhi; omega
  refine ⟨j,hj,hi,?_⟩
  rw [gcd_mask pp qp ordered balanced hj]
  have a : digit p j<2 := Nat.mod_lt _ (by decide)
  have b : digit q j<2 := Nat.mod_lt _ (by decide)
  by_cases h : digit p j=1
  · simp [h, show digit q j≠1 by omega]
  · simp [h, show digit q j=1 by omega]

private theorem central_lower (m : ℕ) : 2^m ≤ m.centralBinom := by
  induction m with
  | zero => simp
  | succ m ih =>
    have step := Nat.succ_mul_centralBinom_succ m
    have ge : (m+1)*(2*m.centralBinom) ≤ (m+1)*(m+1).centralBinom := by
      rw [step]; nlinarith
    rw [pow_succ]
    nlinarith [Nat.le_of_mul_le_mul_left ge (by omega : 0<m+1)]

/-- Reducing the numerator and denominator factorials separately destroys the
digit information: on every scheduled equal-width row, both residues vanish. -/
theorem division_residues_zero {p q k j : ℕ} (pp : p.Prime) (qp : q.Prime)
    (ordered : p<q) (plo : 2^k≤p) (within : j<k) :
    (endpoint (p*q) j).factorial % (p*q) = 0 ∧
    (endpoint (p*q) j/2).factorial % (p*q) = 0 := by
  have powle : 2^(j+1)≤p := (Nat.pow_le_pow_right (n:=2) (by decide) within).trans plo
  have small : q≤endpoint (p*q) j/2 := by
    rw [endpoint, Nat.div_div_eq_div_mul, ← pow_succ, Nat.le_div_iff_mul_le (pow_pos (by decide) _)]
    rw [mul_comm q]
    exact Nat.mul_le_mul_right _ powle
  have vanishes (A : ℕ) (h : q≤A) : A.factorial % (p*q)=0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact ((Nat.coprime_primes pp qp).mpr ordered.ne).mul_dvd_of_dvd_of_dvd
      (Nat.dvd_factorial pp.pos (ordered.le.trans h)) (Nat.dvd_factorial qp.pos h)
  exact ⟨vanishes _ (by omega),vanishes _ small⟩

/-- This lower bound applies to materializing the exact integer coefficient. -/
theorem coefficient_lower (A : ℕ) : 2^(A/2) ≤ coefficient A := by
  unfold coefficient
  split_ifs with h
  · exact central_lower _
  · exact (central_lower _).trans (Nat.le_mul_of_pos_left _ (by omega))

set_option exponentiation.threshold 2100 in
/-- Even the smallest permissible row of a 2048-bit input has at least
2^1025 labels. The exact coefficient has at least 2^1024+1 binary digits. -/
theorem full_width_cost {n j : ℕ} (size : 2^2047≤n) (within : j≤1022) :
    2^1025 ≤ endpoint n j ∧ 2^(2^1024) ≤ coefficient (endpoint n j) := by
  have powle : 2^j ≤ 2^1022 := Nat.pow_le_pow_right (n:=2) (by decide) within
  have row : 2^1025 ≤ endpoint n j := by
    apply (Nat.le_div_iff_mul_le (pow_pos (by decide) j : 0<2^j)).2
    exact (Nat.mul_le_mul_left _ powle).trans (by simpa only [← pow_add] using size)
  refine ⟨row, (Nat.pow_le_pow_right (n:=2) (by decide) ?_).trans (coefficient_lower _)⟩
  exact (Nat.le_div_iff_mul_le (by decide : 0<2)).2 (by simpa only [← pow_succ] using row)

/-- Prime-factor certificates for the three bounded product-only discoveries. -/
theorem fixture_certificates :
    ExactFactorization 2257 [37,61] ∧ ExactFactorization 3127 [53,59] ∧
    ExactFactorization 1763 [41,43] := by
  have pair (p q : ℕ) (pp : p.Prime) (qp : q.Prime) : ExactFactorization (p*q) [p,q] :=
    ExactFactorization.cons pp (by simpa using ExactFactorization.cons qp exactFactorization_nil)
  exact ⟨pair 37 61 (by decide) (by decide), pair 53 59 (by decide) (by decide),
    pair 41 43 (by decide) (by decide)⟩

end PrimeFactors.DyadicTotativeMasks
