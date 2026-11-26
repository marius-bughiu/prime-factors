import PrimeFactors.FixedDivisorSignatures

/-! Minimum number of fixed gcd constants separating every eligible prime pair,
assuming two explicit counts in O(1)-fraction subintervals of the prime catalogue. -/
namespace PrimeFactors.OptimalDivisorSignatures

open Finset MixedPrefixSample FixedDivisorSignatures

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

/-- Any two distinct primes above this cutoff have a full-width product. -/
noncomputable def cliquePrimes := primes.filter fun p => 3*X ≤ 2*p

/-- Every full-width pair contains at least one prime above this cutoff. -/
noncomputable def codedPrimes := primes.filter fun p => 7*X ≤ 5*p

/-- Constants are chosen once, before either factor or the product is known. -/
def coversEligible {k : ℕ} (C : Fin k → ℕ) : Prop :=
  ∀ z ∈ eligible, ∃ j, 1 < (C j).gcd (z.1*z.2) ∧ (C j).gcd (z.1*z.2) < z.1*z.2

attribute [local irreducible] X primes eligible sample ordered cliquePrimes codedPrimes

private theorem is_prime {p : ℕ} (hp : p∈primes) : p.Prime := by
  rw [primes] at hp
  exact (mem_filter.mp hp).2

private theorem eligible_clique {p q : ℕ} (hp : p∈cliquePrimes) (hq : q∈cliquePrimes)
    (order : p<q) : (p,q)∈eligible := by
  rw [cliquePrimes] at hp hq
  obtain ⟨pm,pl⟩ := mem_filter.mp hp
  obtain ⟨qm,ql⟩ := mem_filter.mp hq
  have bound := Nat.mul_le_mul pl ql
  rw [eligible, sample]
  exact mem_filter.mpr ⟨mem_ordered.mpr ⟨pm,qm,order.ne,
    by nlinarith only [bound, Nat.zero_le (X*X)], trivial⟩,order⟩

private theorem larger_is_coded {p q : ℕ} (mem : (p,q)∈eligible) :
    q∈codedPrimes := by
  rw [eligible,sample] at mem
  obtain ⟨orderedPair,lt⟩ := mem_filter.mp mem
  obtain ⟨_,qm,_,size,_⟩ := (mem_ordered (E:=fun _ => True) (z:=(p,q))).mp orderedPair
  rw [codedPrimes]
  apply mem_filter.mpr ⟨qm,?_⟩
  change p < q at lt
  change 2*X^2 ≤ p*q at size
  change 7*X ≤ 5*q
  by_contra! short
  have small := Nat.mul_self_lt_mul_self short
  have compare := Nat.mul_le_mul_right q lt.le
  nlinarith only [small, compare, size, Nat.zero_le (X*X)]

private theorem lower_bits {k : ℕ} {C : Fin k → ℕ} (hit : coversEligible C) :
    cliquePrimes.card ≤ 2^k := by
  apply clique_bound
  · intro p hp
    rw [cliquePrimes] at hp
    exact is_prime (mem_filter.mp hp).1
  · intro p hp q hq ne
    rcases lt_or_gt_of_ne ne with lt | lt
    · exact hit (p,q) (eligible_clique hp hq lt)
    · simpa only [Nat.mul_comm q p] using hit (q,p) (eligible_clique hq hp lt)

/-- Give every prime of T an individual color and all remaining primes one color.
A pair in S is separated whenever its second member belongs to T. -/
theorem cover_large_endpoint (S T : Finset ℕ) (pr : ∀ p∈S, Nat.Prime p) {k : ℕ}
    (room : T.card < 2^k) :
    ∃ C : Fin k → ℕ, ∀ p∈S, ∀ q∈S, p≠q → q∈T →
      ∃ j, 1 < (C j).gcd (p*q) ∧ (C j).gcd (p*q) < p*q := by
  classical
  have card : Fintype.card (Option T) ≤ Fintype.card (Fin k → Bool) := by simpa using room
  obtain ⟨code⟩ := Function.Embedding.nonempty_of_card_le card
  let color (p : ℕ) : Option T := if h : p∈T then some ⟨p,h⟩ else none
  let bit (p : ℕ) := code (color p)
  refine ⟨fun j => column S (fun p => bit p j), ?_⟩
  intro p pm q qm ne high
  have diff : color p ≠ color q := by
    dsimp only [color]
    rw [dif_pos high]
    split
    · exact fun eq => ne (congrArg Subtype.val (Option.some.inj eq))
    · exact Option.noConfusion
  have coord : ∃ j, bit p j≠bit q j := by
    by_contra! eq
    exact diff (code.injective (funext eq))
  obtain ⟨j,hj⟩ := coord
  have unequal : ¬(p ∣ column S (fun x => bit x j) ↔ q ∣ column S (fun x => bit x j)) := by
    rw [prescribe S pr bit p pm j, prescribe S pr bit q qm j]
    simpa using hj
  refine ⟨j,?_⟩
  rcases separates (pr p pm) (pr q qm) unequal with h | h <;> rw [h]
  · exact ⟨(pr p pm).one_lt, lt_mul_of_one_lt_right (pr p pm).pos (pr q qm).one_lt⟩
  · exact ⟨(pr q qm).one_lt, lt_mul_of_one_lt_left (pr q qm).pos (pr p pm).one_lt⟩

/-- One code for each large prime and one shared code for the rest suffice. -/
theorem cover_of_room {k : ℕ} (room : codedPrimes.card < 2^k) :
    ∃ C : Fin k → ℕ, coversEligible C := by
  obtain ⟨C,h⟩ := cover_large_endpoint primes codedPrimes (fun _ => is_prime) room
  refine ⟨C, ?_⟩
  rintro ⟨p,q⟩ mem
  have high := larger_is_coded mem
  rw [eligible,sample] at mem
  obtain ⟨orderedPair,_⟩ := mem_filter.mp mem
  obtain ⟨pm,qm,ne,_,_⟩ := (mem_ordered (E:=fun _ => True) (z:=(p,q))).mp orderedPair
  exact h p pm q qm ne high

/-- The lower and upper cardinal assumptions concern different catalogue intervals. -/
theorem minimum (k : ℕ) (lower : 2^1012 < cliquePrimes.card)
    (upper : codedPrimes.card < 2^1013) :
    (∃ C : Fin k → ℕ, coversEligible C) ↔ 1013 ≤ k := by
  constructor
  · rintro ⟨C,h⟩
    by_contra! small
    have limit := Nat.pow_le_pow_right (by decide : 0<2) (by omega : k≤1012)
    exact (Nat.lt_irrefl _) (lower.trans_le ((lower_bits h).trans limit))
  · intro enough
    exact cover_of_room (upper.trans_le (Nat.pow_le_pow_right (by decide) enough))

/-- Numerical margins for the two interval estimates. The analytic estimates
are supplied explicitly. Only the encoding and the numerical comparison occur here. -/
theorem minimum_of_interval_estimates (k : ℕ)
    (lower : (X:ℚ)/(2*710) - 4*(X:ℚ)/10^13 ≤ (cliquePrimes.card:ℚ))
    (upper : (codedPrimes.card:ℚ) ≤ 3*(X:ℚ)/(5*709) + 4*(X:ℚ)/10^13) :
    (∃ C : Fin k → ℕ, coversEligible C) ↔ 1013 ≤ k := by
  have lo : (2:ℚ)^1012 < (X:ℚ)/(2*710) - 4*(X:ℚ)/10^13 := by rw [X]; norm_num
  have hi : 3*(X:ℚ)/(5*709) + 4*(X:ℚ)/10^13 < (2:ℚ)^1013 := by rw [X]; norm_num
  apply minimum
  · exact_mod_cast lo.trans_le lower
  · exact_mod_cast upper.trans_lt hi

end PrimeFactors.OptimalDivisorSignatures
