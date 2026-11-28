import PrimeFactors.LocalSumGuessCoverage

/-! Exact number of distinct sum remainders required to cover half of all
ordered pairs with a fixed square unit product modulo 5^e, for e≥2. -/

namespace PrimeFactors.HalfMassFive

open Finset LocalSumGuessCoverage PrimeSquareSumWeights
open scoped Classical
open private PrimeFactors.digit_card PrimeFactors.two_unit from PrimeFactors.PrimePowerCount

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The actual precision is k+2. -/
abbrev RingAt (k : ℕ) := ZMod (5^(k+2))

noncomputable def support (n k : ℕ) := univ.filter (AdmissibleSum (n : RingAt k))

private noncomputable def regular (k : ℕ) :=
  univ.filter (fun s : RingAt k => firstPrimeDigit 5 (k+1) s = 0)

/-- Among the attainable residues, the two singular first digits are the
nonzero ones. The unique regular first digit at prime five is zero. -/
noncomputable def singular (n k : ℕ) := support n k \ regular k

private theorem positive_iff {m n : ℕ} [NeZero m] (s : ZMod m) :
    0<weight n s ↔ AdmissibleSum (n : ZMod m) s := by
  rw [weight,Finite.card_pos_iff]
  constructor
  · rintro ⟨v⟩
    exact ⟨v.val.val.1,v.val.val.2,v.val.property,v.property⟩
  · rintro ⟨x,y,prod,sum⟩
    exact ⟨⟨⟨(x,y),prod⟩,sum⟩⟩

/-- The attaining set consists precisely of the admissible residues whose
discriminant vanishes modulo five. -/
theorem mem_singular_iff {n k : ℕ} (unit : ¬5∣n) (sq : IsSquare (n : ZMod 5))
    (s : RingAt k) : s∈singular n k ↔ AdmissibleSum (n : RingAt k) s ∧
      firstPrimeDigit 5 (k+1) (s^2-4*n) = 0 := by
  simp only [singular,support,regular,mem_sdiff,mem_filter,mem_univ,true_and]
  apply and_congr_right
  rintro ⟨x,y,prod,rfl⟩
  let f := firstPrimeDigit 5 (k+1)
  have product : f x*f y=(n : ZMod 5) := by simpa only [map_mul,map_natCast] using congrArg f prod
  have nz : (n : ZMod 5)≠0 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp.mt unit
  obtain ⟨u,square⟩ := sq
  have small : ∀ r t u : ZMod 5, r*t≠0 → r*t=u*u →
      (r+t≠0 ↔ (r+t)^2-4*(r*t)=0) := by decide +kernel
  simpa only [map_sub,map_pow,map_add,map_mul,map_ofNat,map_natCast,←product] using
    small (f x) (f y) u (product ▸ nz) (product.trans square)

private theorem given_support {n k : ℕ} {s : RingAt k} (h : s∈support n k) :
    AdmissibleSum (n : RingAt k) s := (mem_filter.mp h).2

private theorem min_weight {n k : ℕ} {s : RingAt k} (h : s∈support n k) : 2≤weight n s := by
  obtain ⟨x,y,prod,rfl⟩ := given_support h
  rw [PrimePowerPairWeight.weight_of_pair (p:=5) (by decide) prod]
  split_ifs
  · have pos : 0 < 5^(PrimePowerPairWeight.cappedOrder 5 (k+2) (x-y).val) := pow_pos (by decide) _
    omega
  · calc
      2 ≤ 5^1 := by decide
      _ ≤ 5^((k+2)/2) := Nat.pow_le_pow_right (by decide) (by omega)

private theorem support_count {n : ℕ} (unit : ¬5∣n) (sq : IsSquare (n : ZMod 5)) (k : ℕ) :
    (support n k).card=5^(k+1)+2*primePowerSquareCount 5 k := by
  have nz : firstPrimeDigit 5 (k+1) (n : RingAt k)≠0 := by
    rw [map_natCast]
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp.mt unit
  have count := card_primePower_admissibleSum (by decide : 5≠2) (k+1) _ nz
  simpa only [support,Nat.card_eq_fintype_card,Fintype.card_subtype,map_natCast,sq,decide_true,
    primePowerSumCount,Bool.true_eq,if_true,collidingDigitCount,show (5-3)/2=1 by decide,one_mul] using count

private theorem regular_count (k : ℕ) : (regular k).card=5^(k+1) := by
  simpa only [regular,Nat.card_eq_fintype_card,Fintype.card_subtype] using
    PrimeFactors.digit_card (p:=5) (k+1) 0

private theorem regular_weight {n k : ℕ} (unit : ¬5∣n) (sq : IsSquare (n : ZMod 5))
    {s : RingAt k} (h : s∈regular k) : weight n s=2 := by
  let D := s^2-4*(n : RingAt k)
  have digit : firstPrimeDigit 5 (k+1) D=(n : ZMod 5) := by
    simp only [D,map_sub,map_pow,map_mul,map_ofNat,map_natCast,(mem_filter.mp h).2,
      zero_pow (by decide : 2≠0),zero_sub,←neg_mul,show (-4 : ZMod 5)=1 by decide,one_mul]
  obtain ⟨d,rep⟩ := ZMod.intCast_surjective D
  rw [←rep,map_intCast] at digit
  have nz : (d : ZMod 5)≠0 := digit ▸ (ZMod.natCast_zmod_eq_zero_iff_dvd n 5).mp.mt unit
  rw [weight_roots (PrimeFactors.two_unit (p:=5) (by decide) _)]
  change Nat.card {x : RingAt k // x^2=D} = 2
  rw [←rep,primitiveNorm_odd_root_count (p:=5) (by decide) d nz (k+1),if_pos (digit ▸ sq)]

private theorem regular_sub {n k : ℕ} (unit : ¬5∣n) (sq : IsSquare (n : ZMod 5)) :
    regular k ⊆ support n k := by
  intro s hs
  apply mem_filter.mpr
  exact ⟨mem_univ _,(positive_iff s).mp (by rw [regular_weight unit sq hs]; decide)⟩

private theorem supported_total (n k : ℕ) :
    covered n (support n k) = Nat.card (Pairs n (5^(k+2))) := by
  rw [←covered_univ,covered_eq_sum,covered_eq_sum]
  apply sum_subset (subset_univ _)
  intro s _ absent
  apply Nat.eq_zero_of_not_pos
  intro pos
  exact absent (mem_filter.mpr ⟨mem_univ _,(positive_iff s).mp pos⟩)

private theorem total_pairs {n : ℕ} (unit : ¬5∣n) (k : ℕ) :
    Nat.card (Pairs n (5^(k+2))) = 4*5^(k+1) := by
  rw [total ((ZMod.isUnit_iff_coprime _ _).mpr ((Nat.prime_five.coprime_iff_not_dvd.mpr unit).symm.pow_right _)),
    Nat.totient_prime_pow_succ Nat.prime_five (k+1)]
  omega

/-- This explicit set attains half of the total mass with precisely the stated cardinality. -/
theorem attained {n : ℕ} (unit : ¬5∣n) (sq : IsSquare (n : ZMod 5)) (k : ℕ) :
    (singular n k).card = 2*primePowerSquareCount 5 k ∧
    2*covered n (singular n k) = Nat.card (Pairs n (5^(k+2))) := by
  have sub := regular_sub (k:=k) unit sq
  have counts := card_sdiff_add_card_eq_card sub
  rw [regular_count,support_count unit sq] at counts
  have weightSum : (∑ s ∈ regular k, weight n s) = 2*5^(k+1) := by
    simpa only [regular_count,Nat.mul_comm] using
      (sum_const_nat (fun s hs => regular_weight unit sq hs) : (∑ s ∈ regular k, weight n s) = (regular k).card*2)
  have totalSum := supported_total n k
  rw [covered_eq_sum,total_pairs unit] at totalSum
  have balanced := sum_sdiff (f:=weight n) sub
  rw [weightSum,totalSum] at balanced
  rw [singular,covered_eq_sum,total_pairs unit]
  omega

/-- Every set of guesses, including sets containing unattainable residues,
must reach this cardinality to cover half of the ordered pairs. -/
theorem necessary {n : ℕ} (unit : ¬5∣n) (sq : IsSquare (n : ZMod 5)) (k : ℕ)
    (S : Finset (RingAt k)) (half : Nat.card (Pairs n (5^(k+2))) ≤ 2*covered n S) :
    2*primePowerSquareCount 5 k ≤ S.card := by
  let omitted := support n k \ S
  have loss : omitted.card*2 ≤ ∑ s ∈ (univ \ S), weight n s := by
    calc
      _ = ∑ _s ∈ omitted, 2 := by simp
      _ ≤ ∑ s ∈ omitted, weight n s := sum_le_sum (fun _ hs => min_weight (mem_sdiff.mp hs).1)
      _ ≤ _ := sum_le_sum_of_subset (fun s hs => mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp hs).2⟩)
  have cards : (support n k).card ≤ omitted.card+S.card := card_le_card_sdiff_add_card
  have all := sum_sdiff (f:=weight n) (subset_univ S)
  rw [←covered_eq_sum,←covered_eq_sum,←covered_eq_sum,covered_univ,total_pairs unit] at all
  rw [←covered_eq_sum] at loss
  rw [total_pairs unit] at half
  rw [support_count unit sq] at cards
  omega

/-- The sharp minimum over all finite lists of distinct guesses. -/
theorem minimum {n : ℕ} (unit : ¬5∣n) (sq : IsSquare (n : ZMod 5)) (k : ℕ) :
    IsLeast {c : ℕ | ∃ S : Finset (RingAt k), S.card=c ∧
      Nat.card (Pairs n (5^(k+2)))≤2*covered n S} (2*primePowerSquareCount 5 k) := by
  obtain ⟨size,cover⟩ := attained unit sq k
  refine ⟨⟨singular n k,size,cover.ge⟩,?_⟩
  rintro _ ⟨S,rfl,h⟩
  exact necessary unit sq k S h

theorem precision100 : 2*primePowerSquareCount 5 98 = (5^99+7)/6 ∧
    2^227 < (5^99+7)/6 := by decide +kernel

/-- For product one at precision 100, this integer is the attainable minimum. -/
theorem minimum_100 :
    IsLeast {c : ℕ | ∃ S : Finset (ZMod (5^100)), S.card=c ∧
      Nat.card (Pairs 1 (5^100))≤2*covered 1 S} ((5^99+7)/6) := by
  rw [←precision100.1]
  exact minimum (n:=1) (by decide) (by norm_num) 98

end PrimeFactors.HalfMassFive
