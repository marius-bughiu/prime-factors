import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.NNRat.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Sqrt

namespace PrimeFactors

/-- A product comparison by substitution across a cutoff. The common
coordinates cancel. Missing coordinates cost at most the cutoff value;
new coordinates contribute at least that value. -/
private theorem sieveBudget_replace {ι R : Type*} [DecidableEq ι] [CommMonoid R]
    [PartialOrder R] [IsOrderedMonoid R] (P S : Finset ι) (f : ι → R) (v : R)
    (missing : ∀ x ∈ P \ S, f x ≤ v) (added : ∀ x ∈ S \ P, v ≤ f x)
    (powers : v^(P \ S).card ≤ v^(S \ P).card) :
    (∏ x ∈ P, f x) ≤ ∏ x ∈ S, f x := by
  have split (a b : Finset ι) :
      (∏ x ∈ a \ b, f x)*(∏ x ∈ a ∩ b, f x) = ∏ x ∈ a, f x := by
    simpa only [Finset.sdiff_inter_self_left] using
      (Finset.prod_sdiff (f := f) (Finset.inter_subset_left (s₁ := a) (s₂ := b)))
  have diffs : (∏ x ∈ P \ S, f x) ≤ ∏ x ∈ S \ P, f x := calc
    _ ≤ ∏ _x ∈ P \ S, v := Finset.prod_le_prod' missing
    _ = _ := Finset.prod_const _
    _ ≤ _ := powers
    _ = ∏ _x ∈ S \ P, v := (Finset.prod_const _).symm
    _ ≤ _ := Finset.prod_le_prod' added
  rw [← split P S, ← split S P, Finset.inter_comm S P]
  exact mul_le_mul_right' diffs _

private def sieveBudget_oddPrimes (n : ℕ) : Finset ℕ :=
  (Finset.range (n+1)).filter fun p => p.Prime ∧ 2 < p

private theorem sieveBudget_prefix_mem {n p : ℕ} :
    p ∈ sieveBudget_oddPrimes n ↔ p ≤ n ∧ p.Prime ∧ 2 < p := by
  simp [sieveBudget_oddPrimes, Nat.lt_succ_iff]

/-- Lower bound for the density of Stănică's local two-sign union at p. -/
noncomputable def sieveBudget_fraction (p : ℕ) : ℚ≥0 :=
  ((3*p-1 : ℕ) : ℚ≥0) / (4*p)

private theorem sieveBudget_fraction_mono {p q : ℕ} (hp : 0 < p) (pq : p ≤ q) :
    sieveBudget_fraction p ≤ sieveBudget_fraction q := by
  have hq : 0 < q := hp.trans_le pq
  unfold sieveBudget_fraction
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  exact_mod_cast (show (3*p-1)*(4*q) ≤ (3*q-1)*(4*p) by
    have a : 3*p-1+1 = 3*p := by omega
    have b : 3*q-1+1 = 3*q := by omega
    have eq : (3*p-1+1)*(4*q) = (3*q-1+1)*(4*p) := by rw [a,b]; ring
    simp only [Nat.add_mul,Nat.one_mul] at eq
    omega)

private theorem sieveBudget_first62 :
    (sieveBudget_oddPrimes 307).card = 62 ∧
      2^400 < ∏ p ∈ sieveBudget_oddPrimes 307, p := by decide +kernel

private theorem sieveBudget_first61 :
    (sieveBudget_oddPrimes 293).card = 61 ∧
      1/(2^27 : ℚ≥0) < ∏ p ∈ sieveBudget_oddPrimes 293, sieveBudget_fraction p := by
  decide +kernel

/-- Below 2^400 a modulus cannot contain 62 distinct odd prime divisors.
Having omitted some of the first 62 primes only increases the required product. -/
theorem sieveBudget_count (S : Finset ℕ) {m : ℕ} (low : m < 2^400)
    (primes : ∀ p ∈ S, p.Prime ∧ 2 < p) (fits : (∏ p ∈ S, p) ≤ m) :
    S.card ≤ 61 := by
  let P := sieveBudget_oddPrimes 307
  by_contra! many
  have size : P.card ≤ S.card := by have := sieveBudget_first62.1; dsimp [P]; omega
  have compare := sieveBudget_replace P S id 307
    (fun x hx => (sieveBudget_prefix_mem.mp (Finset.mem_sdiff.mp hx).1).1)
    (fun x hx => by
      obtain ⟨inS,notP⟩ := Finset.mem_sdiff.mp hx
      have hx := primes x inS
      by_contra! below
      change x < 307 at below
      exact notP (sieveBudget_prefix_mem.mpr ⟨by omega,hx⟩))
    (by
      apply pow_le_pow_right₀ (by decide)
      have a := Finset.card_sdiff_add_card_inter P S
      have b := Finset.card_sdiff_add_card_inter S P
      rw [Finset.inter_comm S P] at b
      omega)
  exact (not_le_of_gt sieveBudget_first62.2) (compare.trans (fits.trans low.le))

/-- The product of the local density lower bounds exceeds 2^(-27), for every
choice of at most 61 distinct odd primes. The worst 61 are the first 61. -/
theorem sieveBudget_density (S : Finset ℕ) (primes : ∀ p ∈ S, p.Prime ∧ 2 < p)
    (count : S.card ≤ 61) :
    1/(2^27 : ℚ≥0) < ∏ p ∈ S, sieveBudget_fraction p := by
  let P := sieveBudget_oddPrimes 293
  have size : S.card ≤ P.card := by simp [P,sieveBudget_first61.1,count]
  apply sieveBudget_first61.2.trans_le
  apply sieveBudget_replace P S sieveBudget_fraction (sieveBudget_fraction 293)
  · intro x hx
    obtain ⟨small,prime,_⟩ := sieveBudget_prefix_mem.mp (Finset.mem_sdiff.mp hx).1
    exact sieveBudget_fraction_mono prime.pos small
  · intro x hx
    obtain ⟨inS,notP⟩ := Finset.mem_sdiff.mp hx
    apply sieveBudget_fraction_mono (by decide)
    by_contra! below
    exact notP (sieveBudget_prefix_mem.mpr ⟨by omega,primes x inS⟩)
  · apply pow_le_pow_of_le_one (zero_le _) (by decide +kernel)
    have a := Finset.card_sdiff_add_card_inter P S
    have b := Finset.card_sdiff_add_card_inter S P
    rw [Finset.inter_comm S P] at b
    omega

/-- The uniform bounds apply directly to every collection of selected odd prime
divisors of a positive modulus. The modulus itself may contain repeated factors. -/
theorem sieveBudget_modulus (S : Finset ℕ) {m : ℕ} (positive : 0 < m)
    (low : m < 2^400) (selected : ∀ p ∈ S, p.Prime ∧ 2 < p ∧ p ∣ m) :
    S.card ≤ 61 ∧ 1/(2^27 : ℚ≥0) < ∏ p ∈ S, sieveBudget_fraction p := by
  have primes : ∀ p ∈ S, p.Prime ∧ 2 < p := fun p hp =>
    ⟨(selected p hp).1, (selected p hp).2.1⟩
  have subset : S ⊆ m.primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨(selected p hp).1, (selected p hp).2.2, positive.ne'⟩
  have divides : (∏ p ∈ S, p) ∣ ∏ p ∈ m.primeFactors, p := by
    refine ⟨∏ p ∈ m.primeFactors \ S, p, ?_⟩
    simpa only [id_eq, Nat.mul_comm] using (Finset.prod_sdiff (f := id) subset).symm
  have count := sieveBudget_count S low primes
    (Nat.le_of_dvd positive (divides.trans (Nat.prod_primeFactors_dvd m)))
  exact ⟨count, sieveBudget_density S primes count⟩

/-- Exact unshifted width in the reference implementation. -/
def sieveBudget_width (N m : ℕ) : ℕ :=
  2 * (3 * (N.sqrt+1) * (2*m.sqrt+2) / (m*m) + 2) + 1

/-- A lower bound that includes all integer roundings in the public schedule. -/
theorem sieveBudget_squared_width (N m : ℕ) (positive : 0 < m) :
    144*N ≤ (sieveBudget_width N m)^2*m^3 := by
  let s := N.sqrt+1
  let u := m.sqrt+1
  let a := 3*s*(2*u)
  let d := m*m
  have hd : 0 < d := Nat.mul_pos positive positive
  have step : a ≤ (a / d + 1)*d :=
    (Nat.lt_mul_div_succ a hd).le.trans_eq (Nat.mul_comm ..)
  have width : 2*a ≤ sieveBudget_width N m * d := by
    change 2*a ≤ (2*(3*s*(2*m.sqrt+2)/d+2)+1)*d
    rw [show 2*m.sqrt+2=2*u by dsimp [u]; omega]
    change 2*a ≤ (2*(a/d+2)+1)*d
    nlinarith only [Nat.mul_le_mul_left 2 step, Nat.zero_le d]
  have sq := Nat.pow_le_pow_left width 2
  have prod := Nat.mul_le_mul (Nat.lt_succ_sqrt' N).le (Nat.lt_succ_sqrt' m).le
  change N*m ≤ s^2*u^2 at prod
  apply Nat.le_of_mul_le_mul_right (c := m) _ positive
  dsimp [a,d] at sq
  nlinarith only [sq, Nat.mul_le_mul_left 144 prod]

set_option exponentiation.threshold 5000 in
/-- Any modulus below 2^400 forces a width exceeding 2^427 at 2048 bits. -/
theorem sieveBudget_wide_width {N m : ℕ} (bits : 2^2047 ≤ N)
    (positive : 0 < m) (low : m < 2^400) : 2^427 < sieveBudget_width N m := by
  by_contra! small
  have up := Nat.mul_le_mul (Nat.pow_le_pow_left small 2) (Nat.pow_le_pow_left low.le 3)
  have down := (Nat.mul_le_mul_left 144 bits).trans (sieveBudget_squared_width N m positive)
  exact (by decide +kernel : ¬ (144*2^2047 ≤ ((2^427)^2)*((2^400)^3))) (down.trans up)

set_option exponentiation.threshold 5000 in
/-- Either scan at least 2^400 residues or emit more than 2^400 baby entries.
The inputs to the table bound are its complete-period density and the number
of full periods included in the padded exponent interval. -/
theorem sieveBudget_work_2048 {N m M kept entries : ℕ} (S : Finset ℕ)
    (bits : 2^2047 ≤ N) (pos : 0<m) (period : 0<M)
    (selected : ∀ p ∈ S, p.Prime ∧ 2<p ∧ p ∣ m)
    (density : (∏ p ∈ S, sieveBudget_fraction p) ≤ (kept : ℚ≥0)/M)
    (full : ((sieveBudget_width N m + M - 1)/M)*kept ≤ entries) :
    2^400 ≤ m ∨ 2^400 < entries := by
  by_cases large : 2^400 ≤ m
  · exact Or.inl large
  right
  have low := Nat.lt_of_not_ge large
  have width := sieveBudget_wide_width bits pos low
  have retained := ((sieveBudget_modulus S pos low selected).2).trans_le density
  have cross := (div_lt_div_iff₀ (by positivity : (0 : ℚ≥0)<2^27)
    (by exact_mod_cast period : (0 : ℚ≥0)<M)).mp retained
  rw [one_mul] at cross
  have den : M < kept*2^27 := by exact_mod_cast cross
  let w := sieveBudget_width N m
  have cover : w ≤ M*((w+M-1)/M) := by
    have := Nat.div_add_mod (w+M-1) M
    have := Nat.mod_lt (w+M-1) period
    omega
  have total : w ≤ entries*2^27 := calc
    _ ≤ M*((w+M-1)/M) := cover
    _ ≤ (kept*2^27)*((w+M-1)/M) := Nat.mul_le_mul_right _ den.le
    _ = (((w+M-1)/M)*kept)*2^27 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ full
  apply lt_of_not_ge
  intro bound
  have impossible := width.trans_le (total.trans (Nat.mul_le_mul_right (2^27) bound))
  exact (by decide +kernel : ¬ (2^427 < 2^400 * 2^27)) impossible

end PrimeFactors
