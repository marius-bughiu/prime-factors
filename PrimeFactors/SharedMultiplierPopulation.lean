import PrimeFactors.SharedMultiplierPartners
import PrimeFactors.SquareRootPhasePopulation
import PrimeFactors.ShiftedEndpointPopulation

/-! Population reached by an actual square with a proper gcd in an initial
trace prefix. A multiplier catalogue may depend on the smaller prime, with
the same catalogue used for every possible partner of that prime. -/
namespace PrimeFactors.SharedMultiplierPopulation
open Finset MixedPrefixSample

set_option exponentiation.threshold 4096
set_option maxHeartbeats 800000

/-- The two integer roots of a multiplier square give u*v=k*p*q. A proper
gcd of u with the input finds a factor. Choose u to be either root. -/
def Splits (p q k : ℕ) : Prop :=
  ∃ u v : ℕ, u*v=k*(p*q) ∧ 1<(p*q).gcd u ∧ (p*q).gcd u<p*q ∧
    (u:ℝ)+v < 2*Real.sqrt ((k:ℝ)*p*q)+(2^32+1)

private theorem gap_of_split {p q k : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (kp : 0<k) (split : Splits p q k) :
    ∃ a∈k.divisors, (Real.sqrt ((a*p:ℕ):ℝ)-Real.sqrt ((k/a*q:ℕ):ℝ))^2 < 2^32+1 := by
  obtain ⟨u,v,prod,proper,small,trace⟩ := split
  obtain ⟨b,a,weights,sum⟩ := ShiftedEndpointPopulation.allocation pp qp ne prod proper small
  have mem : a∈k.divisors := Nat.mem_divisors.mpr ⟨weights ▸ dvd_mul_left a b,kp.ne'⟩
  have apos := Nat.pos_of_mem_divisors mem
  have div : k/a=b := by rw [weights,Nat.mul_div_cancel _ apos]
  refine ⟨a,mem,?_⟩
  rw [div]
  have eq : ((k:ℝ)*p*q)=((a*p:ℕ):ℝ)*((b*q:ℕ):ℝ) := by rw [weights]; push_cast; ring
  rw [eq, Real.sqrt_mul (Nat.cast_nonneg _) _] at trace
  have cast : (u:ℝ)+v=((a*p:ℕ):ℝ)+((b*q:ℕ):ℝ) := by exact_mod_cast sum
  nlinarith only [trace,cast,Real.sq_sqrt (Nat.cast_nonneg (a*p)),Real.sq_sqrt (Nat.cast_nonneg (b*q))]

/-- One fixed multiplier, granting access to all of its divisor allocations. -/
theorem one_multiplier {k p : ℕ} (kp : 0<k) (kcap : k≤2^2048)
    (pp : p.Prime) (lower : 2^1023≤p) (upper : p<2^1024) (Q : Finset ℕ)
    (hits : ∀ q∈Q, p<q ∧ q<2^1024 ∧ q.Prime ∧ Splits p q k) : Q.card≤2^535 := by
  classical
  let r := Real.sqrt (Real.sqrt k)
  have rp : 0<r := by dsimp [r]; positivity
  have rpow : r^4=(k:ℝ) := by
    rw [show 4=2*2 by decide,pow_mul,show r^2=Real.sqrt k from Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg _)]
  have rcap : r≤2^512 := by
    apply le_of_not_gt; intro h
    have bound := pow_lt_pow_left₀ h (by positivity : (0:ℝ)≤2^512) (by decide : 4≠0)
    rw [rpow,←pow_mul] at bound
    exact (not_lt_of_ge (by exact_mod_cast kcap : (k:ℝ)≤2^2048)) bound
  let row (a : ℕ) := Q.filter fun q => (Real.sqrt ((a*p:ℕ):ℝ)-Real.sqrt ((k/a*q:ℕ):ℝ))^2 < 2^32+1
  have cover : Q ⊆ k.divisors.biUnion row := by
    intro q hq
    obtain ⟨lt,_,qp,split⟩ := hits q hq
    obtain ⟨a,ha,small⟩ := gap_of_split pp qp lt.ne kp split
    exact mem_biUnion.mpr ⟨a,ha,mem_filter.mpr ⟨hq,small⟩⟩
  have each (a : ℕ) (ha : a∈k.divisors) :
      ((row a).card:ℝ) ≤ 1+8*(2:ℝ)^512*65537/r := by
    have ap := Nat.pos_of_mem_divisors ha
    have prod := Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1
    have bp : 0<k/a := Nat.pos_of_ne_zero (fun e => by simp [e] at prod; omega)
    apply SharedMultiplierPartners.count ap bp prod lower upper (row a)
    intro q hq
    obtain ⟨hq,eq⟩ := mem_filter.mp hq
    obtain ⟨lt,cap,_,_⟩ := hits q hq
    exact ⟨lt.le,cap,eq⟩
  have dc : (k.divisors.card:ℝ) ≤ 9*r := by
    have bound : (k.divisors.card:ℝ)^4<9^4*(k:ℝ) := by exact_mod_cast MultiplierDivisorReach.fourth_power_bound kp.ne'
    apply le_of_not_gt; intro h
    have cmp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤9*r) h.le 4
    rw [mul_pow,rpow] at cmp
    linarith
  have wc : (Q.card:ℝ) ≤ 2^535 := calc
    _ ≤ ∑ a∈k.divisors, ((row a).card:ℝ) := by exact_mod_cast (card_le_card cover).trans card_biUnion_le
    _ ≤ ∑ _a∈k.divisors, (1+8*(2:ℝ)^512*65537/r) := sum_le_sum each
    _ = (k.divisors.card:ℝ)*(1+8*2^512*65537/r) := by simp; ring
    _ ≤ (9*r)*(1+8*2^512*65537/r) := mul_le_mul_of_nonneg_right dc (by positivity)
    _ = 9*r+9*8*2^512*65537 := by field_simp; ring
    _ ≤ 9*2^512+9*8*2^512*65537 := by gcongr
    _ ≤ _ := by norm_num
  exact_mod_cast wc

attribute [local irreducible] MixedPrefixSample.eligible MixedPrefixSample.ordered MixedPrefixSample.primes

/-- Even with a separate catalogue for every first prime, the fraction of
eligible pairs reached via a proper gcd is below M / 2^472. -/
theorem catalogue {M : ℕ} (mp : 0<M) (menu : ℕ → Finset ℕ)
    (cap : ∀ p∈primes, (menu p).card≤M)
    (weights : ∀ p∈primes, ∀ k∈menu p, 0<k ∧ k≤2^2048)
    (pairs : Finset (ℕ×ℕ)) (subset : pairs⊆eligible)
    (success : ∀ z∈pairs, ∃ k∈menu z.1, Splits z.1 z.2 k) :
    2^472*pairs.card < M*eligible.card := by
  classical
  let partners p := primes.filter fun q => (p,q)∈pairs
  have data {p q : ℕ} (h : (p,q)∈pairs) : p∈primes ∧ q∈primes ∧ p<q := by
    have he := subset h
    rw [eligible,sample] at he
    obtain ⟨ho,lt⟩ := mem_filter.mp he
    obtain ⟨hp,hq,_,_,_⟩ := mem_ordered.mp ho
    exact ⟨hp,hq,lt⟩
  have prime_data {p : ℕ} (hp : p∈primes) : 2^1023≤p ∧ p<2^1024 ∧ p.Prime := by
    rw [primes] at hp
    obtain ⟨int,pr⟩ := mem_filter.mp hp
    obtain ⟨lo,hi⟩ := mem_Ico.mp int
    exact ⟨lo,lt_of_lt_of_eq hi (by decide +kernel),pr⟩
  have each (p : ℕ) (hp : p∈primes) : (partners p).card≤M*2^535 := by
    let hit (k : ℕ) := (partners p).filter fun q => Splits p q k
    have cover : partners p ⊆ (menu p).biUnion hit := by
      intro q hq
      obtain ⟨k,hk,h⟩ := success (p,q) (mem_filter.mp hq).2
      exact mem_biUnion.mpr ⟨k,hk,mem_filter.mpr ⟨hq,h⟩⟩
    apply (card_le_card cover).trans
    apply (card_biUnion_le_card_mul _ _ (2^535) ?_).trans (Nat.mul_le_mul_right _ (cap p hp))
    intro k hk
    obtain ⟨kp,kt⟩ := weights p hp k hk
    obtain ⟨lo,hi,pr⟩ := prime_data hp
    apply one_multiplier kp kt pr lo hi
    intro q hq
    obtain ⟨part,h⟩ := mem_filter.mp hq
    obtain ⟨qmem,pair⟩ := mem_filter.mp part
    exact ⟨(data pair).2.2,(prime_data qmem).2.1,(prime_data qmem).2.2,h⟩
  have cover : pairs ⊆ primes.biUnion (fun p => (partners p).image (fun q => (p,q))) := by
    rintro ⟨p,q⟩ h
    obtain ⟨hp,hq,_⟩ := data h
    exact mem_biUnion.mpr ⟨p,hp,mem_image_of_mem _ (mem_filter.mpr ⟨hq,h⟩)⟩
  have total := (card_le_card cover).trans (card_biUnion_le_card_mul _ _ (M*2^535)
    (fun p hp => card_image_le.trans (each p hp)))
  have m := Nat.mul_lt_mul_of_pos_left SquareRootPhasePopulation.marginal mp
  have scaled := Nat.mul_le_mul_left (2^472) total
  have factor : (2:ℕ)^472*2^535*41056 ≤ X := by decide +kernel
  have gm := Nat.mul_le_mul_right (M*primes.card) factor
  apply Nat.lt_of_mul_lt_mul_right (a:=41056)
  nlinarith only [gm,m,Nat.mul_le_mul_right 41056 scaled]

theorem billion {menu : ℕ → Finset ℕ} (cap : ∀ p∈primes, (menu p).card≤10^9)
    (weights : ∀ p∈primes, ∀ k∈menu p, 0<k ∧ k≤2^2048)
    (pairs : Finset (ℕ×ℕ)) (subset : pairs⊆eligible)
    (success : ∀ z∈pairs, ∃ k∈menu z.1, Splits z.1 z.2 k) :
    2^442*pairs.card < eligible.card := by
  have large := catalogue (by decide : 0<10^9) menu cap weights pairs subset success
  have coeff : (10:ℕ)^9*2^442≤2^472 := by decide +kernel
  have scaled := Nat.mul_le_mul_right pairs.card coeff
  exact Nat.lt_of_mul_lt_mul_left (a:=10^9) (by nlinarith only [large,scaled])

/-- Every product can choose freely among the eight preselected multipliers. -/
theorem eight {menu : ℕ → Finset ℕ} (cap : ∀ p∈primes, (menu p).card≤8)
    (weights : ∀ p∈primes, ∀ k∈menu p, 0<k ∧ k≤2^2048)
    (pairs : Finset (ℕ×ℕ)) (subset : pairs⊆eligible)
    (success : ∀ z∈pairs, ∃ k∈menu z.1, Splits z.1 z.2 k) :
    2^469*pairs.card < eligible.card := by
  have h := catalogue (by decide : 0<8) menu cap weights pairs subset success
  apply Nat.lt_of_mul_lt_mul_left (a:=8)
  have power : (8:ℕ)*2^469=2^472 := by decide +kernel
  simpa only [←Nat.mul_assoc,power] using h

/-- Allow 128 bits of arbitrary product-dependent advice in choosing the
billion-entry catalogue. For each first prime, all possible messages are priced. -/
theorem advice128 {ι : Type*} [DecidableEq ι] (messages : ℕ → Finset ι)
    (limit : ∀ p∈primes, (messages p).card≤2^128) (menu : ℕ → ι → Finset ℕ)
    (cap : ∀ p∈primes, ∀ i∈messages p, (menu p i).card≤10^9)
    (weights : ∀ p∈primes, ∀ i∈messages p, ∀ k∈menu p i, 0<k ∧ k≤2^2048)
    (pairs : Finset (ℕ×ℕ)) (subset : pairs⊆eligible)
    (success : ∀ z∈pairs, ∃ i∈messages z.1, ∃ k∈menu z.1 i, Splits z.1 z.2 k) :
    2^314*pairs.card < eligible.card := by
  let all p := (messages p).biUnion (menu p)
  have bound (p : ℕ) (hp : p∈primes) : (all p).card≤2^128*10^9 :=
    (card_biUnion_le_card_mul _ _ _ (cap p hp)).trans (Nat.mul_le_mul_right _ (limit p hp))
  have sizes (p : ℕ) (hp : p∈primes) (k : ℕ) (hk : k∈all p) : 0<k ∧ k≤2^2048 := by
    obtain ⟨i,hi,mem⟩ := mem_biUnion.mp hk
    exact weights p hp i hi k mem
  have h := catalogue (by decide +kernel : 0<2^128*10^9) all bound sizes pairs subset (by
    intro z hz
    obtain ⟨i,hi,k,hk,split⟩ := success _ hz
    exact ⟨k,mem_biUnion.mpr ⟨i,hi,hk⟩,split⟩)
  have coef : (2:ℕ)^128*10^9*2^314≤2^472 := by decide +kernel
  apply Nat.lt_of_mul_lt_mul_left (a:=2^128*10^9)
  exact lt_of_le_of_lt (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right pairs.card coef) h

end PrimeFactors.SharedMultiplierPopulation
