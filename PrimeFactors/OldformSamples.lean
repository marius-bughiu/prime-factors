import PrimeFactors.DivisorSum
import Mathlib.Tactic

/-! # What prime-power samples determine in a space of modular forms

The arithmetic sequence below is the Fourier expansion of a weight-two
Eisenstein form at level 4. At level 4N both F(z) and F(Nz) are oldforms.
These modularity facts are external (Bruin, *Computing coefficients of modular
forms*, §2). We work directly with the coefficients and the known-index model.
-/
namespace PrimeFactors.OldformSamples

/-- Coefficients of F(q^d), for positive d. -/
def dilate (d : ℕ) (f : ℕ → ℤ) (n : ℕ) : ℤ := if d ∣ n then f (n/d) else 0

/-- Adding a multiple of the level-raised form to the original one. -/
def shifted (d : ℕ) (c : ℤ) (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  f n+c*dilate d f n

theorem off_multiples {d n : ℕ} (c : ℤ) (f : ℕ → ℤ) (off : ¬d∣n) :
    shifted d c f n = f n := by simp [shifted,dilate,off]

theorem at_target {d : ℕ} (hd : 0<d) (c : ℤ) {f : ℕ → ℤ} (one : f 1=1) :
    shifted d c f d = f d+c := by simp [shifted,dilate,Nat.div_self hd,one]

theorem no_prime_power {p q ell : ℕ} (pp : p.Prime) (qp : q.Prime)
    (distinct : p≠q) (prime : ell.Prime) (k : ℕ) : ¬p*q∣ell^k := by
  intro dvd
  have first := pp.dvd_of_dvd_pow ((dvd_mul_right p q).trans dvd)
  have second := qp.dvd_of_dvd_pow ((dvd_mul_left q p).trans dvd)
  exact distinct ((Nat.prime_dvd_prime_iff_eq pp prime).mp first |>.trans
    ((Nat.prime_dvd_prime_iff_eq qp prime).mp second).symm)

/-- Sequences of sample values ordered by prime and exponent, including exponent zero. -/
def primePowers (f : ℕ → ℤ) (ell : {r : ℕ // r.Prime}) (k : ℕ) : ℤ := f (ell.val^k)

theorem identical_samples {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (distinct : p≠q)
    (c : ℤ) (f : ℕ→ℤ) :
    primePowers (shifted (p*q) c f) = primePowers f := by
  funext ell k
  exact off_multiples c f (no_prime_power pp qp distinct ell.property k)

/-- The coefficient of -(E₂(z)−3E₂(2z)+2E₂(4z))/24, whose constant vanishes.
Its weight and level are classical. This file uses its explicit coefficient sequence. -/
noncomputable def base (n : ℕ) : ℤ :=
  let s := fun k : ℕ => (ArithmeticFunction.sigma 1 k : ℤ)
  s n-3*dilate 2 s n+2*dilate 4 s n

theorem first : base 1=1 := by simp [base,dilate,ArithmeticFunction.sigma_one_apply]
theorem constant : base 0=0 := by simp [base,dilate]

theorem odd_coeff {n : ℕ} (h : Odd n) : base n = ArithmeticFunction.sigma 1 n := by
  have two : ¬2∣n := by obtain ⟨b,hb⟩ := h; omega
  have four : ¬4∣n := fun hd => two (dvd_trans (by decide : 2∣4) hd)
  simp [base,dilate,two,four]

theorem oldform_pair {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (op : Odd p)
    (oq : Odd q) (distinct : p≠q) (c : ℤ) :
    primePowers (shifted (p*q) c base) = primePowers base ∧
    shifted (p*q) c base 0 = 0 ∧
    shifted (p*q) c base (p*q) = (p*q+(p+q)+1 : ℕ)+c := by
  refine ⟨identical_samples pp qp distinct c base, ?_, ?_⟩
  · simp [shifted,dilate,constant]
  · rw [at_target (Nat.mul_pos pp.pos qp.pos) c first, odd_coeff (op.mul oq),
      sigma_semiprime pp qp distinct]

/-- No rule depending only on the index and all prime-power observations can
recover this coefficient on both forms. -/
theorem cannot_determine {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (distinct : p≠q)
    (read : ℕ → ((ell : {r : ℕ // r.Prime}) → ℕ → ℤ) → ℤ) :
    let n := p*q
    ¬ (read n (primePowers base) = base n ∧
       read n (primePowers (shifted n 1 base)) = shifted n 1 base n) := by
  dsimp only
  rw [identical_samples pp qp distinct, at_target (Nat.mul_pos pp.pos qp.pos) 1 first]
  omega

/-- A known factorization of any positive index where the two expansions
differ already contains both primes of the target. -/
theorem factored_sample {p q m : ℕ} (pp : p.Prime) (qp : q.Prime) (hm : 0<m)
    {f : ℕ→ℤ} {c : ℤ} (different : shifted (p*q) c f m ≠ f m)
    {primes : List ℕ} (product : primes.prod=m) (certified : ∀ r∈primes, r.Prime) :
    p ∈ primes ∧ q ∈ primes := by
  have divides : p*q∣m := by by_contra off; exact different (off_multiples c f off)
  have actual := Nat.primeFactorsList_unique product certified
  constructor
  · exact actual.mem_iff.mpr ((Nat.mem_primeFactorsList_iff_dvd hm.ne' pp).mpr
      ((dvd_mul_right p q).trans divides))
  · exact actual.mem_iff.mpr ((Nat.mem_primeFactorsList_iff_dvd hm.ne' qp).mpr
      ((dvd_mul_left q p).trans divides))

/-- At level 308 the two normalized forms share their entire prime-power data
and differ at index 77. -/
theorem example77 : primePowers (shifted 77 1 base) = primePowers base ∧
    base 77 = 96 ∧ shifted 77 1 base 77 = 97 := by
  have pair := oldform_pair (p:=7) (q:=11) (by decide) (by decide) (by decide)
    (by decide) (by decide) 1
  have value : base 77 = 96 := by
    rw [odd_coeff (by decide), show 77=7*11 by decide, sigma_semiprime (by decide) (by decide) (by decide)]
    norm_num
  exact ⟨pair.1, value, by rw [at_target (by decide) 1 first, value]; decide⟩

end PrimeFactors.OldformSamples
