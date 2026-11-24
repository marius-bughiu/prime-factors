import PrimeFactors.DivisorSum
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify

namespace PrimeFactors

/-- The numeric envelope obtained by applying Robin to kN and dividing by σ(k). -/
noncomputable def robinMultiplierBound (N k : ℕ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * (N : ℝ) * k *
    Real.log (Real.log ((k : ℝ)*N)) / (ArithmeticFunction.sigma 1 k : ℝ)

/-- The externally verified analytic statement used by the finite comparisons. -/
abbrev RobinMultiplierInequality : Prop :=
  ∀ n : ℕ, 5040 < n → (ArithmeticFunction.sigma 1 n : ℝ) <
    Real.exp Real.eulerMascheroniConstant*n*Real.log (Real.log n)

/-- Applying the same Robin inequality to a smaller, coprime comparison
integer M gives a lower bound on the proposed upper estimate. -/
theorem robinMultiplier_compare {k M N : ℕ} (cop : k.Coprime M) (size : M ≤ N)
    (cut : 5040 < k*M)
    (robin : RobinMultiplierInequality) :
    (N : ℝ)*(ArithmeticFunction.sigma 1 M : ℝ)/M < robinMultiplierBound N k := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by simp [h] at cut
  have hM : 0 < M := Nat.pos_of_ne_zero fun h => by simp [h] at cut
  have hN : 0 < N := hM.trans_le size
  have hsig : 0 < ArithmeticFunction.sigma 1 k := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact (show 0 < 1 by decide).trans_le (Finset.single_le_sum
      (f := id) (fun i _ => Nat.zero_le i) (Nat.one_mem_divisors.mpr hk.ne'))
  have hr := robin (k*M) cut
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime cop,Nat.cast_mul,
    Nat.cast_mul] at hr
  have grow : Real.log (Real.log ((k : ℝ)*M)) ≤ Real.log (Real.log ((k : ℝ)*N)) := by
    have lg : (1 : ℝ) < (k : ℝ)*M := by exact_mod_cast cut.trans_le' (by decide : 1 ≤ 5040)
    exact Real.log_le_log (Real.log_pos lg) (Real.log_le_log (by positivity)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast size) (by positivity)))
  unfold robinMultiplierBound
  apply (div_lt_div_iff₀ (by positivity) (by exact_mod_cast hsig)).mpr
  calc
    _ = (N : ℝ)*((ArithmeticFunction.sigma 1 k : ℝ)*(ArithmeticFunction.sigma 1 M : ℝ)) := by ring
    _ < _ := mul_lt_mul_of_pos_left hr (by exact_mod_cast hN)
    _ ≤ Real.exp Real.eulerMascheroniConstant*N*k*Real.log (Real.log ((k : ℝ)*N))*M := by
      have h := mul_le_mul_of_nonneg_left grow
        (show 0 ≤ (N : ℝ)*(Real.exp Real.eulerMascheroniConstant*((k : ℝ)*M)) by positivity)
      convert h using 1 <;> ring

/-- A single omitted prime already sets a floor on what U can achieve. -/
theorem robinMultiplier_missing_prime {N k r : ℕ} (prime : r.Prime) (omitted : ¬r ∣ k)
    (small : r ≤ N) (cut : 5040 < k*r) (robin : RobinMultiplierInequality) :
    (N : ℝ)+N/(r : ℝ) < robinMultiplierBound N k := by
  have sig : ArithmeticFunction.sigma 1 r = 1+r := by
    simpa [Finset.sum_range_succ] using ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) prime
  have comp := robinMultiplier_compare (prime.coprime_iff_not_dvd.mpr omitted).symm small cut robin
  rw [sig,Nat.cast_add,Nat.cast_one] at comp
  have R : (r : ℝ) ≠ 0 := by exact_mod_cast prime.ne_zero
  convert comp using 1
  field_simp
  ring

/-- A real inequality with a one-unit rounding tolerance forces both
ordered comparison primes to be the true primes. Oddness supplies a
gap of two when only the second comparison prime is smaller. -/
theorem robinMultiplier_rounding {r s p q : ℕ} {U : ℝ} (rpos : 0 < r) (spos : 0 < s)
    (rp : r ≤ p) (sq : s ≤ q) (pq : p ≤ q) (balanced : q ≤ 2*p)
    (odds : Odd s) (oddq : Odd q)
    (comparison : (p : ℝ)*q*(1+1/r)*(1+1/s) < U)
    (round : U < ((p : ℝ)+1)*(q+1)+1) : r = p ∧ s = q := by
  have R : (0 : ℝ) < r := by exact_mod_cast rpos
  have S : (0 : ℝ) < s := by exact_mod_cast spos
  have P : (0 : ℝ) < p := by exact_mod_cast rpos.trans_le rp
  have Q : (0 : ℝ) < q := by exact_mod_cast spos.trans_le sq
  have atQ : 1+1/(q : ℝ) ≤ 1+1/(s : ℝ) :=
    add_le_add_left (one_div_le_one_div_of_le S (by exact_mod_cast sq)) 1
  have first : r = p := by
    by_contra! ne
    have gap : (r : ℝ)+1 ≤ p := by exact_mod_cast (show r+1 ≤ p by omega)
    have qr : (r : ℝ) ≤ q := by exact_mod_cast rp.trans pq
    have lower := mul_le_mul_of_nonneg_left atQ (show 0 ≤ (p : ℝ)*q*(1+1/r) by positivity)
    have identity : (p : ℝ)*q*(1+1/r)*(1+1/q) =
        ((p : ℝ)+1)*(q+1)+((q : ℝ)+1)*(p-r)/r := by field_simp; ring
    rw [identity] at lower
    have gap' : 1 ≤ ((q : ℝ)+1)*(p-r)/r := (le_div_iff₀ R).mpr (by
      nlinarith [mul_nonneg (show 0 ≤ (q : ℝ)+1 by positivity) (show 0 ≤ (p : ℝ)-r-1 by linarith)])
    linarith
  subst r
  refine ⟨rfl,?_⟩
  by_contra! ne
  obtain ⟨a,ha⟩ := odds
  obtain ⟨b,hb⟩ := oddq
  have gap : (s : ℝ)+2 ≤ q := by exact_mod_cast (show s+2 ≤ q by omega)
  have sb : (s : ℝ) ≤ 2*p := by exact_mod_cast sq.trans balanced
  have identity : (p : ℝ)*q*(1+1/p)*(1+1/s) =
      ((p : ℝ)+1)*(q+1)+((p : ℝ)+1)*(q-s)/s := by field_simp; ring
  rw [identity] at comparison
  have gap' : 1 ≤ ((p : ℝ)+1)*(q-s)/s := (le_div_iff₀ S).mpr (by
    nlinarith [mul_nonneg (show 0 ≤ (p : ℝ)+1 by positivity) (show 0 ≤ (q : ℝ)-s-2 by linarith)])
  linarith

/-- With a subunit rounding error, the first two primes omitted by k must
give the actual factorization. The finite theorem takes the external Robin
statement explicitly, and applies it at the two comparison primes. -/
theorem robinMultiplier_first_omitted {k r s p q : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hp : p.Prime) (hq : q.Prime) (rs : r < s) (pq : p < q) (balanced : q ≤ 2*p)
    (rskip : ¬r ∣ k) (sskip : ¬s ∣ k) (cop : k.Coprime (p*q))
    (first : ∀ l, l.Prime → ¬l ∣ k → r ≤ l)
    (second : ∀ l, l.Prime → ¬l ∣ k → l ≠ r → s ≤ l)
    (cut : 5040 < k*(r*s)) (robin : RobinMultiplierInequality)
    (round : ⌊robinMultiplierBound (p*q) k⌋₊ = ArithmeticFunction.sigma 1 (p*q)) :
    r = p ∧ s = q := by
  have copP := (Nat.coprime_mul_iff_right.mp cop).1
  have copQ := (Nat.coprime_mul_iff_right.mp cop).2
  have rp := first p hp (hp.coprime_iff_not_dvd.mp copP.symm)
  have sq := second q hq (hq.coprime_iff_not_dvd.mp copQ.symm) (rp.trans_lt pq).ne'
  have copM := Nat.coprime_mul_iff_right.mpr
    ⟨(hr.coprime_iff_not_dvd.mpr rskip).symm,(hs.coprime_iff_not_dvd.mpr sskip).symm⟩
  have comp := robinMultiplier_compare copM (Nat.mul_le_mul rp sq) cut robin
  rw [sigma_semiprime hr hs rs.ne] at comp
  push_cast at comp
  have R : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have S : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne_zero
  apply robinMultiplier_rounding hr.pos hs.pos rp sq pq.le balanced
    (hs.eq_two_or_odd'.resolve_left (by have := hr.two_le; omega))
    (hq.eq_two_or_odd'.resolve_left (by have := hp.two_le; omega))
  · convert comp using 1
    field_simp
    ring
  · have upper := Nat.lt_floor_add_one (robinMultiplierBound (p*q) k)
    rw [round,sigma_semiprime hp hq pq.ne] at upper
    push_cast at upper
    linarith

/-- If the extrema are evaluated exactly, their integer quotient gives
σ(N)+2 on this balanced range. Here the residual error is strictly less
than one and the quotient is ordinary integer division. -/
theorem robinMultiplier_limit_floor {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (large : 9 ≤ p) (order : p < q) (balanced : q ≤ 2*p) :
    (p*q)^2 / (p*q).totient = ArithmeticFunction.sigma 1 (p*q)+2 := by
  rw [sigma_semiprime hp hq order.ne,Nat.totient_mul ((Nat.coprime_primes hp hq).mpr order.ne),
    Nat.totient_prime hp,Nat.totient_prime hq]
  have P : (9 : ℤ) ≤ p := by exact_mod_cast large
  have O : (p : ℤ) ≤ q := by exact_mod_cast order.le
  have B : (q : ℤ) ≤ 2*p := by exact_mod_cast balanced
  apply Nat.div_eq_of_lt_le
  · zify [hp.one_le,hq.one_le]
    nlinarith [sq_nonneg ((p : ℤ)-q)]
  · zify [hp.one_le,hq.one_le]
    nlinarith [mul_nonneg (sub_nonneg.mpr O) (sub_nonneg.mpr B),
      mul_nonneg (sub_nonneg.mpr P) (show (0 : ℤ) ≤ p by positivity)]

/-- A target σ divisible by four can be decoded from a one-unit estimate
of a real ratio whose integer quotient equals σ+2. -/
theorem robinMultiplier_precision {n d s : ℕ} {y : ℝ} (pos : 0 < d) (four : 4 ∣ s)
    (ratio : n/d = s+2) (accuracy : |y-(n : ℝ)/d| ≤ 1) : 4*⌊y/4⌋₊ = s := by
  obtain ⟨j,rfl⟩ := four
  have lo : (4*j+2)*d ≤ n := (Nat.le_div_iff_mul_le pos).mp (by omega)
  have hi : n < (4*j+3)*d := (Nat.div_lt_iff_lt_mul pos).mp (by omega)
  have D : (0 : ℝ) < d := by exact_mod_cast pos
  have lower : 4*(j : ℝ)+2 ≤ (n : ℝ)/d := (le_div_iff₀ D).mpr (by exact_mod_cast lo)
  have upper : (n : ℝ)/d < 4*(j : ℝ)+3 := (div_lt_iff₀ D).mpr (by exact_mod_cast hi)
  obtain ⟨left,right⟩ := abs_le.mp accuracy
  have nonneg : (0 : ℝ) ≤ j := by positivity
  have rounded : ⌊y/4⌋₊ = j := (Nat.floor_eq_iff (by linarith)).mpr ⟨by linarith,by linarith⟩
  rw [rounded]

/-- One unit of absolute precision in the extremal limit is enough to
recover both balanced odd primes. -/
theorem robinMultiplier_decode {p q : ℕ} {y : ℝ} (hp : p.Prime) (hq : q.Prime)
    (large : 9 ≤ p) (order : p < q) (balanced : q ≤ 2*p)
    (accuracy : |y-(((p*q)^2 : ℕ) : ℝ)/(p*q).totient| ≤ 1) :
    recoverFromSigma (p*q) (4*⌊y/4⌋₊) = (p,q) := by
  obtain ⟨a,ha⟩ := hp.eq_two_or_odd'.resolve_left (by omega)
  obtain ⟨b,hb⟩ := hq.eq_two_or_odd'.resolve_left (by omega)
  have four : 4 ∣ ArithmeticFunction.sigma 1 (p*q) := by
    rw [sigma_semiprime hp hq order.ne,ha,hb]
    exact ⟨(a+1)*(b+1),by ring⟩
  rw [robinMultiplier_precision (Nat.totient_pos.mpr (Nat.mul_pos hp.pos hq.pos))
    four (robinMultiplier_limit_floor hp hq large order balanced) accuracy]
  exact recoverFromSigma_correct hp hq order

end PrimeFactors
