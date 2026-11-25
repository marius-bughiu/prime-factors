import PrimeFactors.UniformDivisorCount
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Count the partners of a fixed prime whose two modular inverses have a
prescribed signed difference. Only the population estimate uses hidden data. -/

namespace PrimeFactors.InverseGapPopulation
open Finset

set_option exponentiation.threshold 200000

/-- Fixed by the smaller prime and a proposed inverse difference. -/
def value (p : ℕ) (e : ℤ) : ℕ := ((p:ℤ)^2+e*p-1).natAbs

/-- For the true inverse difference, every possible prime sum is a divisor
of the same nonzero integer for the entire row. -/
theorem value_eq {p q u v : ℕ} (below : v<p) (pair : p*u+q*v=p*q+1) :
    value p ((u:ℤ)-v) = (p-v)*(p+q) := by
  have eq : (p:ℤ)*u+q*v=p*q+1 := by exact_mod_cast pair
  have identity : (p:ℤ)^2+((u:ℤ)-v)*p-1=((p-v)*(p+q):ℕ) := by
    push_cast [Nat.cast_sub below.le]
    linarith only [eq]
  rw [value,identity,Int.natAbs_natCast]

/-- This statement applies to any finite set of first primes and guesses. Each
pair is counted once even if a caller's hypotheses allow several witnesses. -/
theorem families {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {guesses : Finset ℤ}
    (witness : ∀ x ∈ pairs, x.1 ∈ first ∧ ∃ u v : ℕ, v<x.1 ∧
      x.1*u+x.2*v=x.1*x.2+1 ∧ (u:ℤ)-v ∈ guesses) :
    pairs.card ≤ ∑ p ∈ first, ∑ e ∈ guesses, (value p e).divisors.card := by
  classical
  let fiber (p : ℕ) (e : ℤ) := (value p e).divisors
  let covered (p : ℕ) (e : ℤ) := (fiber p e).image (fun d => (p,d-p))
  have inside : pairs ⊆ first.biUnion (fun p => guesses.biUnion (covered p)) := by
    intro x hx
    obtain ⟨hp,u,v,hv,eq,he⟩ := witness x hx
    apply mem_biUnion.mpr ⟨x.1,hp,?_⟩
    apply mem_biUnion.mpr ⟨(u:ℤ)-v,he,?_⟩
    apply mem_image.mpr ⟨x.1+x.2,?_,by simp⟩
    apply Nat.mem_divisors.mpr
    rw [value_eq hv eq]
    exact ⟨dvd_mul_left .., (Nat.mul_pos (Nat.sub_pos_of_lt hv) (by omega)).ne'⟩
  calc
    _ ≤ _ := card_le_card inside
    _ ≤ _ := card_biUnion_le
    _ ≤ _ := sum_le_sum fun p _ => card_biUnion_le.trans (sum_le_sum fun e _ => card_image_le)

/-- Inverse differences too large for 1024-bit factors are impossible.
For each remaining guess the positive row integer is below 2^2049. -/
theorem value_size {p : ℕ} {e : ℤ} (hp : p<2^1024) (he : |e|<2^1024) (pos : 1<p) :
    0<value p e ∧ value p e<2^2049 := by
  let z : ℤ := (p:ℤ)^2+e*p-1
  have ne : z ≠ 0 := by
    intro zero
    have divides : (p:ℤ) ∣ 1 := ⟨(p:ℤ)+e,by dsimp [z] at zero; linarith only [zero]⟩
    have natDvd : p ∣ 1 := by exact_mod_cast divides
    have := Nat.le_of_dvd (by decide : 0<1) natDvd
    omega
  have pp : 0 < (p:ℤ) := by exact_mod_cast (show 0<p by omega)
  have pbound : (p:ℤ)<2^1024 := by exact_mod_cast hp
  have near := abs_lt.mp he
  have sq := mul_self_lt_mul_self (le_of_lt pp) pbound
  have upper := mul_lt_mul_of_pos_right near.2 pp
  have lower := mul_lt_mul_of_pos_right near.1 pp
  have outer := mul_lt_mul_of_pos_left pbound (by positivity : (0:ℤ)<2^1024)
  have scale : (2:ℤ)^2049=2*((2:ℤ)^1024)^2 := by norm_num
  have az : |z| < 2^2049 := by
    dsimp only [z]
    rw [abs_lt,scale]
    constructor <;> nlinarith only [pp,sq,upper,lower,outer,sq_nonneg (p:ℤ)]
  refine ⟨Int.natAbs_pos.mpr ne,?_⟩
  change z.natAbs < _
  exact_mod_cast (show (z.natAbs:ℤ)<2^2049 by simpa [Int.natCast_natAbs] using az)

/-- A guessed gap can work accidentally. This row counts *every* success of the
public divisibility test, including guesses unrelated to the true inverses. -/
def looseValue (p : ℕ) (e : ℤ) : ℕ := value p e * value p (-e)

theorem loose_divisor {p q : ℕ} {e : ℤ}
    (hit : ((p:ℤ)+q) ∣ ((p:ℤ)*q+1)^2+(p:ℤ)*q*e^2) :
    p+q ∣ looseValue p e := by
  have identity : ((p:ℤ)*q+1)^2+(p:ℤ)*q*e^2 -
      (((p:ℤ)^2+e*p-1)*((p:ℤ)^2+(-e)*p-1)) =
      ((p:ℤ)+q)*(p*(p*q-p^2+2+e^2)) := by ring
  have diff : ((p:ℤ)+q) ∣ ((p:ℤ)*q+1)^2+(p:ℤ)*q*e^2 -
      (((p:ℤ)^2+e*p-1)*((p:ℤ)^2+(-e)*p-1)) := ⟨_,identity⟩
  have prodDvd := dvd_sub hit diff
  rw [sub_sub_cancel] at prodDvd
  obtain ⟨k,hk⟩ := prodDvd
  use k.natAbs
  simpa [looseValue,value,Int.natAbs_mul] using congrArg Int.natAbs hk

theorem loose_families {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {guesses : Finset ℤ}
    (witness : ∀ x ∈ pairs, x.1 ∈ first ∧ ∃ e ∈ guesses, 0<looseValue x.1 e ∧
      ((x.1:ℤ)+x.2) ∣ ((x.1:ℤ)*x.2+1)^2+(x.1:ℤ)*x.2*e^2) :
    pairs.card ≤ ∑ p ∈ first, ∑ e ∈ guesses, (looseValue p e).divisors.card := by
  classical
  let covered (p : ℕ) (e : ℤ) := (looseValue p e).divisors.image (fun d => (p,d-p))
  have inside : pairs ⊆ first.biUnion (fun p => guesses.biUnion (covered p)) := by
    intro x hx
    obtain ⟨hp,e,he,pos,hit⟩ := witness x hx
    exact mem_biUnion.mpr ⟨x.1,hp,mem_biUnion.mpr ⟨e,he,mem_image.mpr
      ⟨x.1+x.2,Nat.mem_divisors.mpr ⟨loose_divisor hit,pos.ne'⟩,by simp⟩⟩⟩
  calc
    _ ≤ _ := card_le_card inside
    _ ≤ _ := card_biUnion_le
    _ ≤ _ := sum_le_sum fun p _ => card_biUnion_le.trans (sum_le_sum fun e _ => card_image_le)

theorem loose_size {p : ℕ} {e : ℤ} (hp : p<2^1024) (he : |e|<2^1024) (pos : 1<p) :
    0<looseValue p e ∧ looseValue p e<2^4098 := by
  obtain ⟨a,b⟩ := value_size hp he pos
  obtain ⟨c,d⟩ := value_size (e:=-e) hp (by simpa using he) pos
  have bound := Nat.mul_lt_mul_of_lt_of_le b d.le (by positivity)
  refine ⟨Nat.mul_pos a c,?_⟩
  exact bound.trans_le (by decide +kernel)

/-- The permissive test can split a product even with the wrong inverse gap. -/
theorem accidental_example :
    2749*388 ≡ 1 [MOD 3907] ∧ 3907*2476 ≡ 1 [MOD 2749] ∧
    (388:ℤ)-2476 = -2088 ∧ (6656:ℕ) ∣ (10740343+1)^2 + 10740343*8^2 ∧
    ¬(6656:ℕ) ∣ 10740343+1 ∧ 2749+3907=6656 ∧ 2749*3907=10740343 := by
  decide +kernel

private theorem divisor_caps {n : ℕ} (pos : 0<n) :
    (n<2^2049 → n.divisors.card ≤ 11*2^236) ∧
    (n<2^4098 → n.divisors.card ≤ 3*2^433) := by
  have universal := UniformDivisorCount.power_bound pos
  constructor <;> intro size <;> apply (Nat.pow_le_pow_iff_left (by decide : 336 ≠ 0)).mp
  · exact universal.trans ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left size.le 32)).trans
      (by decide +kernel))
  · exact universal.trans ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left size.le 32)).trans
      (by decide +kernel))

/-- Conversion from per-row candidate counts to population fractions.
The denominator hypothesis is provided by explicit published prime counts. -/
private theorem population_count {P G A B T bits : ℕ} (num : G≤P*(T*A))
    (den : 2^1023*P<44331*B) (scale : 44331*(2^bits*A) ≤ 2^1023) (steps : 0<T)
    (cap : 0<A) : 2^bits*G < T*B := by
  have left := Nat.mul_le_mul_left (2^1023*2^bits) num
  have middle := Nat.mul_lt_mul_of_pos_right den (Nat.mul_pos (Nat.mul_pos (by positivity : 0<2^bits) steps) cap)
  have right := Nat.mul_le_mul_right (T*B) scale
  apply Nat.lt_of_mul_lt_mul_left (a:=2^1023)
  calc
    _ ≤ _ := by simpa only [Nat.mul_assoc] using left
    _ = (2^1023*P)*(2^bits*T*A) := by ac_rfl
    _ < _ := middle
    _ = (44331*(2^bits*A))*(T*B) := by ac_rfl
    _ ≤ _ := right

/-- A fixed list of at most 2^40 differences matches the actual inverses
on fewer than one pair in 2^728 in the target population. -/
theorem true_fraction {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {guesses : Finset ℤ}
    {population : ℕ} (base : 2^1023*first.card<44331*population)
    (small : ∀ p∈first, 1<p ∧ p<2^1024) (rangeE : ∀ e∈guesses, |e|<2^1024)
    (steps : 0<guesses.card) (budget : guesses.card≤2^40)
    (witness : ∀ x ∈ pairs, x.1 ∈ first ∧ ∃ u v : ℕ, v<x.1 ∧
      x.1*u+x.2*v=x.1*x.2+1 ∧ (u:ℤ)-v ∈ guesses) :
    2^768*pairs.card<guesses.card*population ∧ 2^728*pairs.card<population := by
  have num := families witness
  have rows : pairs.card≤first.card*(guesses.card*(11*2^236)) := by
    apply num.trans
    calc
      _ ≤ ∑ p ∈ first, ∑ _e ∈ guesses, 11*2^236 := by
        apply sum_le_sum; intro p hp
        apply sum_le_sum; intro e he
        obtain ⟨a,b⟩ := value_size (small p hp).2 (rangeE e he) (small p hp).1
        exact (divisor_caps a).1 b
      _ = _ := by simp [nsmul_eq_mul]
  have odds := population_count rows base (bits:=768) (by decide +kernel) steps (by positivity)
  refine ⟨odds,?_⟩
  have total := odds.trans_le (Nat.mul_le_mul_right population budget)
  exact Nat.lt_of_mul_lt_mul_left (a:=2^40) (by
    rwa [←Nat.mul_assoc,←pow_add] : 2^40*(2^728*pairs.card)<2^40*population)

/-- Even when accidental hits count, the public divisibility tests for a fixed
list of up to 2^40 bounded guesses cover fewer than one pair in 2^532. -/
theorem loose_fraction {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {guesses : Finset ℤ}
    {population : ℕ} (base : 2^1023*first.card<44331*population)
    (small : ∀ p∈first, 1<p ∧ p<2^1024) (rangeE : ∀ e∈guesses, |e|<2^1024)
    (steps : 0<guesses.card) (budget : guesses.card≤2^40)
    (witness : ∀ x ∈ pairs, x.1 ∈ first ∧ ∃ e ∈ guesses,
      ((x.1:ℤ)+x.2) ∣ ((x.1:ℤ)*x.2+1)^2+(x.1:ℤ)*x.2*e^2) :
    2^572*pairs.card<guesses.card*population ∧ 2^532*pairs.card<population := by
  have num := loose_families (pairs:=pairs) (first:=first) (guesses:=guesses) (fun x hx => by
    obtain ⟨hp,e,he,h⟩ := witness x hx
    exact ⟨hp,e,he,(loose_size (small _ hp).2 (rangeE e he) (small _ hp).1).1,h⟩)
  have rows : pairs.card≤first.card*(guesses.card*(3*2^433)) := by
    apply num.trans
    calc
      _ ≤ ∑ p ∈ first, ∑ _e ∈ guesses, 3*2^433 := by
        apply sum_le_sum; intro p hp
        apply sum_le_sum; intro e he
        obtain ⟨a,b⟩ := loose_size (small p hp).2 (rangeE e he) (small p hp).1
        exact (divisor_caps a).2 b
      _ = _ := by simp [nsmul_eq_mul]
  have odds := population_count rows base (bits:=572) (by decide +kernel) steps (by positivity)
  refine ⟨odds,?_⟩
  have total := odds.trans_le (Nat.mul_le_mul_right population budget)
  exact Nat.lt_of_mul_lt_mul_left (a:=2^40) (by
    rwa [←Nat.mul_assoc,←pow_add] : 2^40*(2^532*pairs.card)<2^40*population)

end PrimeFactors.InverseGapPopulation
