import PrimeFactors.MixedPrefixSample
import PrimeFactors.ChebyshevPrimePowers

/-! Removing prime powers below a cutoff from the product form of the lcm.
Only primes at most the square root can contribute a higher power. -/

namespace PrimeFactors.ChebyshevPrimeCount

open Finset MixedPrefixSample

set_option exponentiation.threshold 8192

private def primesThrough (n : ℕ) := (range (n+1)).filter Nat.Prime

private theorem mem_primesThrough {p n : ℕ} : p∈primesThrough n ↔ p≤n ∧ p.Prime := by
  simp only [primesThrough,mem_filter,mem_range,Nat.lt_succ_iff]

attribute [local irreducible] primesThrough

private def lcmProduct (n : ℕ) := ∏ p∈primesThrough n, p^(Nat.log p n)
private def introduced (n cut : ℕ) := (primesThrough n).filter (fun p => cut<p)

/-- Split a prime's contribution into its old power, one allowance for
small primes, and one allowance for newly introduced primes. -/
private theorem local_bound {n cut s p : ℕ} (np : 0<n) (large : n≤s^2)
    (hp : p.Prime) (pn : p≤n) :
    p^(Nat.log p n) ≤ (if p≤cut then p^(Nat.log p cut) else 1) *
       (if p≤s then n else 1) * (if cut<p then n else 1) := by
  have pos : 0<p^(Nat.log p cut) := pow_pos hp.pos _
  have cap := Nat.pow_log_le_self p np.ne'
  by_cases short : p≤s
  · by_cases old : p≤cut
    · simpa only [if_pos short,if_pos old,if_neg (Nat.not_lt.mpr old),mul_one] using
        cap.trans (Nat.le_mul_of_pos_left n pos)
    · simpa only [if_pos short,if_neg old,if_pos (Nat.lt_of_not_ge old),one_mul] using
        cap.trans (Nat.le_mul_of_pos_right n np)
  · have high : s<p := by omega
    have small : n<p^2 := large.trans_lt (Nat.pow_lt_pow_left high (by decide))
    have lg : Nat.log p n=1 := Nat.log_eq_of_pow_le_of_lt_pow (by simpa using pn) small
    rw [lg,pow_one,if_neg short,mul_one]
    by_cases old : p≤cut
    · rw [if_pos old,if_neg (Nat.not_lt.mpr old),mul_one]
      have le : 1≤Nat.log p cut := Nat.le_log_of_pow_le hp.one_lt (by simpa using old)
      simpa only [pow_one] using Nat.pow_le_pow_right hp.pos le
    · simpa only [if_neg old,if_pos (Nat.lt_of_not_ge old),one_mul] using pn

private theorem product_bound {n cut s : ℕ} (np : 0<n) (before : cut≤n) (sqroot : n≤s^2) :
    lcmProduct n ≤ lcmProduct cut * n^(s+(introduced n cut).card) := by
  let P := primesThrough n
  have product := Finset.prod_le_prod' (s:=P) fun p hp =>
    local_bound (cut:=cut) np sqroot (mem_primesThrough.mp hp).2 (mem_primesThrough.mp hp).1
  simp only [prod_mul_distrib] at product
  rw [←prod_filter (s:=P) (fun p => p≤cut) (fun p => p^(Nat.log p cut)),
      ←prod_filter (s:=P) (fun p => p≤s) (fun _ => n),
      ←prod_filter (s:=P) (fun p => cut<p) (fun _ => n)] at product
  have old : P.filter (fun p => p≤cut) = primesThrough cut := by
    ext p; simp only [P,mem_filter,mem_primesThrough]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.trans before,h.2⟩,h.1⟩⟩
  have subset : P.filter (fun p => p≤s) ⊆ Icc 1 s := by
    intro p hp
    obtain ⟨mem,le⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨(mem_primesThrough.mp mem).2.pos,le⟩
  have size : (P.filter (fun p => p≤s)).card ≤ s := by
    simpa only [Nat.card_Icc,Nat.add_sub_cancel] using card_le_card subset
  rw [old,prod_const,prod_const] at product
  change lcmProduct n≤lcmProduct cut*n^(P.filter (fun p => p≤s)).card*n^(introduced n cut).card at product
  rw [Nat.mul_assoc,←pow_add] at product
  exact product.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right np (Nat.add_le_add_right size _)))

private theorem mem_upper {p : ℕ} :
    p∈upperPrimes ↔ ((X≤p ∧ p<2*X) ∧ p.Prime) ∧ 283*X≤200*p := by
  simp only [upperPrimes,primes,mem_filter,mem_Ico]

attribute [local irreducible] upperPrimes

private theorem sub_upper :
    introduced (2*X) (283*X/200) ⊆ upperPrimes := by
  intro p hp
  obtain ⟨h,above⟩ := mem_filter.mp hp
  obtain ⟨upto,prime⟩ := mem_primesThrough.mp h
  have nonprime : ¬(2*X).Prime := by
    rw [show 2*X=(2:ℕ)^1024 by decide +kernel]
    exact Nat.Prime.not_prime_pow (by decide)
  have ne : p≠2*X := by rintro rfl; exact nonprime prime
  have bp := (Nat.div_lt_iff_lt_mul (by decide : 0<200)).mp above
  exact mem_upper.mpr ⟨⟨⟨by omega,by omega⟩,prime⟩,by omega⟩

private theorem count_for {n cut s : ℕ} (np : 0<n) (before : cut≤n) (cap : n≤s^2)
    (V : Finset ℕ) (sub : introduced n cut⊆V) :
    lcmProduct n≤lcmProduct cut*n^(s+V.card) :=
  (product_bound np before cap).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right np (Nat.add_le_add_left (card_le_card sub) s)))

private theorem lcm_eq (n : ℕ) : lcmProduct n=ChebyshevPrimePowers.L n := by
  unfold lcmProduct primesThrough ChebyshevPrimePowers.L
  rfl

attribute [local irreducible] lcmProduct ChebyshevPrimePowers.L introduced

/-- Comparing the two lcms needs one factor at most 2X for each small prime
and for each prime counted by the concrete upper-interval population. -/
theorem cutoff :
    ChebyshevPrimePowers.L (2*X) ≤ ChebyshevPrimePowers.L (283*X/200)*
      (2*X)^(2^512+upperPrimes.card) := by
  rw [←lcm_eq,←lcm_eq]
  exact count_for (s:=2^512) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ sub_upper

end PrimeFactors.ChebyshevPrimeCount
