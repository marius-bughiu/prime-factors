import PrimeFactors.LocalSumMenu

/-! If we know a product and the distinct odd primes in a sum sieve, how much
can increasing their exponents reduce the fraction of surviving sums?

The exact local counts used here come from `PrimePowerCount`. For context see
Bower, Evans, Luo and Miller, <https://arxiv.org/abs/1212.2930>, and Hittmeir's
factor sieve, <https://arxiv.org/abs/2205.10074>. Over a complete period, the
density improvement at an odd prime p is at most (p+1)²/(p²−2p−1). The product of
these upper bounds over odd primes below 512 is less than 1680. Each repeated
prime above that cutoff costs at least 18 bits in the wheel modulus and gives a
density improvement of at most 128/127. These facts imply the 12-bit bound
`extra_filtering` without constructing the list of allowed residues. -/

namespace PrimeFactors.OddSumWheel

open Finset LocalSumMenu

/-- Fraction of a complete period that is compatible with a factor sum. -/
noncomputable def density (n m : ℕ) : ℚ := (count n m : ℚ) / m

private def premium (p : ℕ) : ℚ :=
  ((p : ℚ) + 1)^2 / ((p : ℚ)^2 - 2*p - 1)

private lemma denominator_pos {p : ℕ} (hp : 3 ≤ p) :
    0 < (p : ℚ)^2 - 2*p - 1 := by
  have h : (3 : ℚ) ≤ p := by exact_mod_cast hp
  nlinarith [sq_nonneg ((p : ℚ)-3)]

private lemma premium_ge_one {p : ℕ} (hp : 3 ≤ p) : 1 ≤ premium p := by
  rw [premium, le_div_iff₀ (denominator_pos hp)]
  nlinarith [show 0 ≤ (p : ℚ) by positivity]

private lemma premium_large {p : ℕ} (hp : 512 ≤ p) : premium p ≤ 128/127 := by
  rw [premium, div_le_iff₀ (denominator_pos (by omega : 3 ≤ p))]
  have h : (512 : ℚ) ≤ p := by exact_mod_cast hp
  nlinarith [sq_nonneg ((p : ℚ)-512)]

private theorem price_local {p : ℕ} (prime : p.Prime) (odd : p ≠ 2) (k : ℕ)
    (sq : Bool) :
    (primePowerSumCount p sq 1 : ℚ) * (p : ℚ)^k ≤
    premium p * primePowerSumCount p sq (k+1) := by
  haveI : Fact p.Prime := ⟨prime⟩
  have hp : 3 ≤ p := by have := prime.two_le; omega
  cases sq with
  | false =>
    simp only [primePowerSumCount,Bool.false_eq_true,if_false,pow_zero,mul_one,
      Nat.cast_mul,Nat.cast_pow]
    exact le_mul_of_one_le_left (by positivity) (premium_ge_one hp)
  | true =>
    have high := primePowerSumCount_closed_square (p:=p) odd k
    have half : 2*primePowerSumCount p true 1=p+1 := by
      have heven := prime.odd_of_ne_two odd
      obtain ⟨t,ht⟩ := heven
      simp [primePowerSumCount,collidingDigitCount]
      omega
    have hhalf : 2*(primePowerSumCount p true 1 : ℚ) = p+1 := by exact_mod_cast half
    have bound : p^2*p^k ≤ 2*(p+1)*primePowerSumCount p true (k+1)+(2*p+1)*p^k := by omega
    have hb : (p : ℚ)^2*(p : ℚ)^k ≤
        2*(p+1)*(primePowerSumCount p true (k+1) : ℚ)+(2*p+1)*(p : ℚ)^k := by
      exact_mod_cast bound
    rw [premium,div_mul_eq_mul_div, le_div_iff₀ (denominator_pos hp)]
    have hnon : 0 ≤ (p : ℚ)+1 := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left hb hnon,
      congrArg (fun z : ℚ => z*(p : ℚ)^k*((p : ℚ)^2-2*p-1)) hhalf]

private noncomputable def charge (p k : ℕ) : ℚ :=
  if k = 0 then 1 else if p < 512 then premium p else 128 / 127

private lemma charge_pos {p : ℕ} (hp : 3 ≤ p) (k : ℕ) : 0 ≤ charge p k := by
  unfold charge
  split_ifs
  · norm_num
  · exact le_trans zero_le_one (premium_ge_one hp)
  · norm_num

private theorem density_local {n p : ℕ} (prime : p.Prime) (odd : p ≠ 2)
    (cop : p.Coprime n) (k : ℕ) :
    density n p ≤ charge p k * density n (p^(k+1)) := by
  classical
  haveI : Fact p.Prime := ⟨prime⟩
  have pp : 0 < (p : ℚ) := by exact_mod_cast prime.pos
  have counts (i : ℕ) : count n (p^(i+1)) =
      primePowerSumCount p (decide (IsSquare (n : ZMod p))) (i+1) := by
    simpa only [map_natCast] using card_primePower_admissibleSum odd i (n : ZMod (p^(i+1)))
      (by rw [map_natCast]; exact (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp.mt (prime.coprime_iff_not_dvd.mp cop))
  by_cases z : k=0
  · simp [z,charge]
  have weak := price_local prime odd k (decide (IsSquare (n : ZMod p)))
  have base := counts 0
  simp only [Nat.zero_add,pow_one] at base
  unfold density
  rw [base,counts,Nat.cast_pow,mul_div_assoc',div_le_div_iff₀ pp (pow_pos pp _),pow_succ]
  have replace : premium p ≤ charge p k := by
    simp only [charge,if_neg z]
    split_ifs with h
    · exact le_rfl
    · exact premium_large (by omega)
  have step := weak.trans (mul_le_mul_of_nonneg_right replace (by positivity))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right step pp.le

private lemma density_prod (n : ℕ) (S : Finset ℕ) (e : ℕ → ℕ)
    (primes : ∀ p ∈ S, p.Prime) :
    density n (∏ p ∈ S, p^(e p)) = ∏ p ∈ S, density n (p^(e p)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    haveI : Nonempty {s : ZMod 1 // AdmissibleSum (n : ZMod 1) s} :=
      ⟨⟨1+n,1,n,one_mul _,rfl⟩⟩
    simp only [prod_empty,density,count,Nat.cast_one,div_one]
    rw [Nat.card_unique, Nat.cast_one]
  | @insert p S out ih =>
    have prime := primes p (mem_insert_self ..)
    have rest (q) (hq : q ∈ S) := primes q (mem_insert_of_mem hq)
    have cop : (p^(e p)).Coprime (∏ q ∈ S, q^(e q)) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (((Nat.coprime_primes prime (rest q hq)).mpr (fun h => out (h ▸ hq))).pow_left _).pow_right _
    simp only [prod_insert out]
    rw [←ih rest]
    unfold density
    change (count n (p^e p * ∏ q ∈ S, q^e q) : ℚ) / _ = _
    rw [show count n (p^e p * ∏ q ∈ S, q^e q) = _ from card_admissibleSum_crt cop n,
      Nat.cast_mul,Nat.cast_mul,div_mul_div_comm]
    rfl

private noncomputable def smallPrimes : Finset ℕ := (range 512).filter (fun p => 3 ≤ p ∧ p.Prime)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem small_budget : (∏ p ∈ smallPrimes, premium p) ≤ 1680 := by decide +kernel

private theorem charge_budget (S : Finset ℕ) (k : ℕ → ℕ)
    (primes : ∀ p ∈ S, p.Prime ∧ 3 ≤ p)
    (cap : (∏ p ∈ S, p^(k p+1)) ≤ 2^2048) :
    (∏ p ∈ S, charge p (k p)) < 4096 := by
  classical
  let small := S.filter (· < 512)
  let big := S.filter (fun p => 512 ≤ p ∧ k p ≠ 0)
  have ss : small ⊆ smallPrimes := by
    intro p h
    obtain ⟨m,lt⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨mem_range.mpr lt,(primes p m).2,(primes p m).1⟩
  have ee : smallPrimes.filter (· ∈ small) = small := by
    ext p
    simp only [mem_filter,and_iff_right_iff_imp]
    exact @ss p
  have small_bound : (∏ p ∈ small, premium p) ≤ 1680 := by
    calc
      _ = ∏ p ∈ smallPrimes, if p ∈ small then premium p else 1 := by
        rw [←prod_filter,ee]
      _ ≤ ∏ p ∈ smallPrimes, premium p := by
        apply prod_le_prod
        · intro p h; split_ifs
          · exact (premium_ge_one (mem_filter.mp h).2.1).trans' zero_le_one
          · norm_num
        · intro p h; split_ifs
          · rfl
          · exact premium_ge_one (mem_filter.mp h).2.1
      _ ≤ _ := small_budget
  have big_count : big.card ≤ 113 := by
    have lower : (2:ℕ)^(18*big.card) ≤ 2^2048 := calc
      _ = ∏ p ∈ big, (2:ℕ)^18 := by rw [prod_const, ←pow_mul]
      _ = ∏ p ∈ S, if 512 ≤ p ∧ k p ≠ 0 then (2:ℕ)^18 else 1 := by
        exact prod_filter _ _
      _ ≤ ∏ p ∈ S, p^(k p+1) := by
        apply prod_le_prod (fun _ _ => Nat.zero_le _)
        intro p h
        split_ifs with a
        · exact (Nat.pow_le_pow_left a.1 2).trans
            (Nat.pow_le_pow_right (primes p h).1.pos (by omega))
        · exact Nat.one_le_pow _ _ (primes p h).1.pos
      _ ≤ _ := cap
    have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp lower
    omega
  have combined : (∏ p ∈ S, charge p (k p)) ≤
      (∏ p ∈ small, premium p) * (128/127 : ℚ)^big.card := by
    rw [show (128/127 : ℚ)^big.card = ∏ p ∈ big, (128/127 : ℚ) by rw [prod_const]]
    simp only [small,big,prod_filter,←prod_mul_distrib]
    apply prod_le_prod
    · intro p h; exact charge_pos (primes p h).2 _
    · intro p h
      dsimp only [charge]
      by_cases kp : k p=0 <;> by_cases a : p<512
      · simp [kp,a,premium_ge_one (primes p h).2]
      · simp [kp,a]
      · simp [kp,a,not_le_of_gt a]
      · simp [kp,a,Nat.le_of_not_gt a]
  exact combined.trans_lt <| calc
    _ ≤ 1680*(128/127 : ℚ)^113 := mul_le_mul small_bound
      (pow_le_pow_right₀ (by norm_num) big_count) (by positivity) (by norm_num)
    _ < _ := by decide +kernel

/-- For any product-dependent odd modulus of at most 2^2048, lifting the primes
of its squarefree radical can thin the set of allowed sums by less than 4096
in a complete period. This compares densities and imposes no interval placement. -/
theorem extra_filtering {n m : ℕ} (pos : 0 < m) (odd : ¬2∣m)
    (unit : m.Coprime n) (cap : m ≤ 2^2048) :
    density n (∏ p ∈ m.primeFactors, p) < 4096*density n m := by
  classical
  let S := m.primeFactors
  let k (p : ℕ) := m.factorization p - 1
  have primes (p) (h : p ∈ S) : p.Prime ∧ 3 ≤ p := by
    obtain ⟨pr,div,_⟩ := Nat.mem_primeFactors.mp h
    exact ⟨pr,by have := pr.two_le; by_contra! z; exact odd ((show p=2 by omega) ▸ div)⟩
  have pr (p) (h : p ∈ S) := (primes p h).1
  have index (p) (h : p ∈ S) : k p+1=m.factorization p := by
    have := (pr p h).factorization_pos_of_dvd pos.ne' (Nat.mem_primeFactors.mp h).2.1
    dsimp [k]; omega
  have product : (∏ p ∈ S, p^(k p+1)) = m := by
    exact (prod_congr rfl (fun p h => congrArg (p^·) (index p h))).trans
      (Nat.factorization_prod_pow_eq_self pos.ne')
  have base := density_prod n S (fun _ => 1) pr
  simp only [pow_one] at base
  have full := density_prod n S (fun p => k p+1) pr
  rw [product] at full
  have loc (p) (h : p ∈ S) := density_local (pr p h) (show p≠2 by have := (primes p h).2;omega)
    (unit.of_dvd_left (Nat.mem_primeFactors.mp h).2.1) (k p)
  have dpos : 0<density n m := by
    letI : NeZero m := ⟨pos.ne'⟩
    haveI : Nonempty {s : ZMod m // AdmissibleSum (n : ZMod m) s} :=
      ⟨⟨1+n,1,n,one_mul _,rfl⟩⟩
    exact div_pos (by exact_mod_cast (Nat.card_pos (α:={s : ZMod m // AdmissibleSum (n : ZMod m) s})))
      (by exact_mod_cast pos)
  rw [base]
  calc
    _ ≤ ∏ p ∈ S, charge p (k p)*density n (p^(k p+1)) := by
      apply prod_le_prod _ loc
      intro p _; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    _ = (∏ p ∈ S, charge p (k p))*density n m := by rw [prod_mul_distrib,←full]
    _ < _ := mul_lt_mul_of_pos_right (charge_budget S k primes (product ▸ cap)) dpos

end PrimeFactors.OddSumWheel
