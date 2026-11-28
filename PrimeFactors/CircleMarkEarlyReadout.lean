import PrimeFactors.CircleMarkTargetFrequency

/-! Before either local half-period is exhausted the first-hit histogram is flat.
Its normalization retains one scalar reading of the product's totient. -/
namespace PrimeFactors.CircleMarkEarlyReadout

open Finset CircleMarkTargetFrequency

/-- Probability of a hit on the first positive coordinate for a uniform eligible target. -/
noncomputable abbrev early (n : ℕ) [NeZero n] := rate n (Icc 1 1)

private theorem halves {p : ℕ} (odd : Odd p) : p=2*((p-1)/2)+1 := by
  obtain ⟨k,h⟩ := odd
  omega

theorem early_eq {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) :
    early (p*q) = 1/((p:ℚ)-1) + 1/((q:ℚ)-1) := by
  have P := hp.out.two_le
  have Q := hq.out.two_le
  simp only [early,first_hit diff op oq,min_eq_left (show 1≤(p-1)/2 by omega),
    min_eq_left (show 1≤(q-1)/2 by omega),Nat.cast_one]

/-- Exact early CDF, so each first-hit rank up to either half-period has the same mass. -/
theorem flat_prefix {p q L : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (pl : L≤(p-1)/2) (ql : L≤(q-1)/2) :
    rate (p*q) (Icc 1 L) = L*early (p*q) := by
  rw [first_hit diff op oq,min_eq_left pl,min_eq_left ql,early_eq diff op oq]
  ring

/-- Counting just the first bucket already determines the prime sum. The total
population and this first bucket together also have a public cardinality. -/
theorem first_bucket {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) :
    2*(hits (p*q) (Icc 1 1)).card+2 = p+q ∧
    2*((targets (p*q)).card+(hits (p*q) (Icc 1 1)).card)+1 = p*q := by
  obtain ⟨total,hit⟩ := counts diff op oq (Icc 1 1)
  have P := hp.out.two_le
  have Q := hq.out.two_le
  rw [prefix_cover op,prefix_cover oq,min_eq_left (show 1≤(p-1)/2 by omega),
    min_eq_left (show 1≤(q-1)/2 by omega),one_mul,mul_one] at hit
  rw [hit,total]
  have a := halves (hp.out.odd_of_ne_two op)
  have b := halves (hq.out.odd_of_ne_two oq)
  constructor
  · omega
  · conv_rhs => rw [a,b]
    ring

/-- Conditioning on an early hit, with misses or the cohort size hidden, leaves a
uniform rank law independent of the product. -/
theorem conditional {p q k L : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (pos : 0<L) (kL : k≤L)
    (pl : L≤(p-1)/2) (ql : L≤(q-1)/2) :
    0 < rate (p*q) (Icc 1 L) ∧
    rate (p*q) (Icc 1 k) / rate (p*q) (Icc 1 L) = (k:ℚ)/L := by
  have P : (1:ℚ)<p := by exact_mod_cast hp.out.one_lt
  have Q : (1:ℚ)<q := by exact_mod_cast hq.out.one_lt
  have dn : 0<early (p*q) := by
    rw [early_eq diff op oq]
    exact add_pos (one_div_pos.mpr (sub_pos.mpr P)) (one_div_pos.mpr (sub_pos.mpr Q))
  rw [flat_prefix diff op oq (kL.trans pl) (kL.trans ql),flat_prefix diff op oq pl ql]
  exact ⟨mul_pos (by exact_mod_cast pos) dn, mul_div_mul_right _ _ dn.ne'⟩

/-- The same early hit probability gives the usual totient exactly when N is known. -/
theorem totient_reading {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) :
    (1+early (p*q))*((p*q).totient:ℚ)=(p:ℚ)*q-1 := by
  rw [early_eq diff op oq,Nat.totient_mul ((Nat.coprime_primes hp.out hq.out).mpr diff),
    Nat.totient_prime hp.out,Nat.totient_prime hq.out,Nat.cast_mul,
    Nat.cast_sub hp.out.one_le,Nat.cast_sub hq.out.one_le,Nat.cast_one]
  have P : (1:ℚ)<p := by exact_mod_cast hp.out.one_lt
  have Q : (1:ℚ)<q := by exact_mod_cast hq.out.one_lt
  field_simp [ne_of_gt (sub_pos.mpr P),ne_of_gt (sub_pos.mpr Q)]
  ring

/-- The normalized single-coordinate observable can be inverted if supplied exactly. -/
noncomputable def inferredSum (n : ℕ) (d : ℚ) : ℚ := 2+((n:ℚ)-1)*d/(1+d)

theorem inferred_correct {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) :
    inferredSum (p*q) (early (p*q))=(p:ℚ)+q := by
  have P : (1:ℚ)<p := by exact_mod_cast hp.out.one_lt
  have Q : (1:ℚ)<q := by exact_mod_cast hq.out.one_lt
  have d := early_eq diff op oq
  have pos : 0 < 1+early (p*q) := by
    rw [d]
    linarith only [one_div_pos.mpr (sub_pos.mpr P),one_div_pos.mpr (sub_pos.mpr Q)]
  have eqn := totient_reading diff op oq
  rw [Nat.totient_mul ((Nat.coprime_primes hp.out hq.out).mpr diff),
    Nat.totient_prime hp.out,Nat.totient_prime hq.out,Nat.cast_mul,
    Nat.cast_sub hp.out.one_le,Nat.cast_sub hq.out.one_le,Nat.cast_one] at eqn
  rw [inferredSum,Nat.cast_mul,←eqn]
  field_simp [pos.ne']
  nlinarith only [eqn,congrArg (fun t : ℚ => t*(1+early (p*q))) eqn]

/-- Changing a nonnegative reading by epsilon changes the inferred sum by at
most (N-1)*epsilon. -/
theorem stability {n : ℕ} (hn : 1≤n) {a b : ℚ} (ha : 0≤a) (hb : 0≤b) :
    |inferredSum n a-inferredSum n b| ≤ ((n:ℚ)-1)*|a-b| := by
  have A : 0<1+a := by linarith
  have B : 0<1+b := by linarith
  have N : 0≤(n:ℚ)-1 := sub_nonneg.mpr (by exact_mod_cast hn)
  have eqn : inferredSum n a-inferredSum n b = ((n:ℚ)-1)*(a-b)/((1+a)*(1+b)) := by
    unfold inferredSum
    field_simp [A.ne',B.ne']
    ring
  rw [eqn,abs_div,abs_mul,abs_of_nonneg N,abs_of_pos (mul_pos A B)]
  apply div_le_self (mul_nonneg N (abs_nonneg _))
  nlinarith only [ha,hb,mul_nonneg ha hb]

/-- Distinct toy products have identical censored distributions through rank 18,
including their chance of a miss. -/
theorem matching_histograms (L : ℕ) (limit : L≤18) :
    rate 2501 (Icc 1 L)=(L:ℚ)/24 ∧ rate 2701 (Icc 1 L)=(L:ℚ)/24 := by
  have calcRate (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (d : p≠q) (op : p≠2) (oq : q≠2)
      (pl : 18≤(p-1)/2) (ql : 18≤(q-1)/2)
      (value : 1/((p:ℚ)-1)+1/((q:ℚ)-1)=1/24) :
      rate (p*q) (Icc 1 L)=(L:ℚ)/24 := by
    rw [flat_prefix d op oq (limit.trans pl) (limit.trans ql),early_eq d op oq,value]
    ring
  letI : Fact (Nat.Prime 41) := ⟨by decide⟩
  letI : Fact (Nat.Prime 61) := ⟨by decide⟩
  letI : Fact (Nat.Prime 37) := ⟨by decide⟩
  letI : Fact (Nat.Prime 73) := ⟨by decide⟩
  exact ⟨calcRate 41 61 (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num),
    calcRate 37 73 (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num)⟩

end PrimeFactors.CircleMarkEarlyReadout
