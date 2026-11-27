import PrimeFactors.ShortPascalRow

/-! A public row of Pascal's triangle whose low columns test consecutive
members of an arithmetic progression against the hidden prime divisors. -/

namespace PrimeFactors.QuotientPascalMasks

theorem low_column {p m k : ℕ} (hp : p.Prime) (short : k < p) :
    p ∣ m.choose k ↔ m % p < k := by
  letI : Fact p.Prime := ⟨hp⟩
  have lucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := m) (k := k) (p := p)
  rw [Nat.mod_eq_of_lt short, Nat.div_eq_of_lt short, Nat.choose_zero_right, mul_one] at lucas
  rw [← Nat.modEq_zero_iff_dvd]
  constructor
  · intro h
    by_contra! inside
    exact ShortPascalRow.prime_above_row hp (Nat.mod_lt m hp.pos) inside
      (Nat.modEq_zero_iff_dvd.mp (lucas.symm.trans h))
  · intro outside
    rw [Nat.choose_eq_zero_of_lt outside] at lucas
    exact lucas

/-- The public relation c + d*m ≡ 0 mod N turns a low column in row m
into a test of the k terms c, c+d, ..., c+d*(k-1). -/
theorem address_hits {p m d c k : ℕ} (hp : p.Prime) (short : k < p)
    (unit : p.Coprime d) (address : p ∣ c + d*m) :
    p ∣ m.choose k ↔ ∃ j < k, p ∣ c + d*j := by
  rw [low_column hp short]
  constructor
  · intro hit
    refine ⟨m%p, hit, Nat.modEq_zero_iff_dvd.mp ?_⟩
    exact (((Nat.mod_modEq m p).mul_left d).add_left c).trans address.modEq_zero_nat
  · rintro ⟨j, jk, hit⟩
    have eq := Nat.ModEq.add_left_cancel' c (hit.modEq_zero_nat.trans address.zero_modEq_nat)
    have same := Nat.ModEq.cancel_left_of_coprime unit eq
    change j%p = m%p at same
    rwa [← same, Nat.mod_eq_of_lt (jk.trans short)]

noncomputable def progression (c d k : ℕ) := ∏ j ∈ Finset.range k, (c+d*j)

private theorem gcd_class {p q v : ℕ} (hp : p.Prime) (hq : q.Prime) (distinct : p ≠ q) :
    v.gcd (p*q) = (if p ∣ v then p else 1)*(if q ∣ v then q else 1) := by
  by_cases ph : p ∣ v <;> by_cases qh : q ∣ v <;> simp only [ph,qh,if_true,if_false,mul_one,one_mul]
  · exact Nat.gcd_eq_right (((Nat.coprime_primes hp hq).mpr distinct).mul_dvd_of_dvd_of_dvd ph qh)
  · exact NormBatchGCD.one_batch hq ph qh
  · rw [Nat.mul_comm p q]
    exact NormBatchGCD.one_batch hp qh ph
  · rw [Nat.gcd_comm]
    exact (Nat.coprime_mul_iff_left.mpr
      ⟨hp.coprime_iff_not_dvd.mpr ph, hq.coprime_iff_not_dvd.mpr qh⟩).gcd_eq_one

/-- The binomial and the progression have exactly the same gcd with the product. -/
theorem gcd_transfer {p q m d c k : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p < q)
    (short : k < p) (unit : (p*q).Coprime d) (address : p*q ∣ c + d*m) :
    (m.choose k).gcd (p*q) = (progression c d k).gcd (p*q) := by
  have side {s : ℕ} (hs : s.Prime) (hsn : s ∣ p*q) (hks : k < s) :
      s ∣ m.choose k ↔ s ∣ progression c d k := by
    rw [address_hits hs hks (unit.of_dvd_left hsn) (hsn.trans address), progression,
      hs.prime.dvd_finset_prod_iff]
    simp
  simp only [gcd_class hp hq order.ne, side hp (dvd_mul_right p q) short,
    side hq (dvd_mul_left q p) (short.trans order)]

/-- Without a translation, every positive term is below d*k. Small d
and small k cannot expose even a single large prime. -/
theorem short_quotient_misses {p m d r k : ℕ} (hp : p.Prime) (short : k < p)
    (unit : p.Coprime d) (address : p ∣ r+d*m) (positive : 0 < r)
    (remainder : r < d) (size : d*k ≤ p) : ¬p ∣ m.choose k := by
  rw [address_hits hp short unit address]
  rintro ⟨j, jk, hit⟩
  have bound := Nat.mul_le_mul_left d (show j+1 ≤ k from jk)
  rw [Nat.mul_add, Nat.mul_one] at bound
  exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hit

/-- Every odd candidate from c through u occurs in this single column. -/
def oddColumn (c u : ℕ) := (u-c)/2+1

theorem odd_interval {p q c u : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p < q)
    (oddP : p%2=1) (oddQ : q%2=1) (oddC : c%2=1)
    (lower : c ≤ p) (upper : p ≤ u) (endBefore : u < q) (short : oddColumn c u < p) :
    (((p*q-c)/2).choose (oddColumn c u)).gcd (p*q) = p := by
  have npos : p ≤ p*q := Nat.le_mul_of_pos_right _ hq.pos
  have np : p*q%2=1 := by rw [Nat.mul_mod, oddP, oddQ]
  have address : c + 2*((p*q-c)/2) = p*q := by omega
  have unit (s : ℕ) (prime : s.Prime) (odd : s%2=1) : s.Coprime 2 := by
    apply prime.coprime_iff_not_dvd.mpr
    intro h
    have := (Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp h
    omega
  apply NormBatchGCD.one_batch hq
  · rw [address_hits hp short (unit p hp oddP) (address ▸ dvd_mul_right p q)]
    refine ⟨(p-c)/2, ?_, ?_⟩
    · unfold oddColumn; omega
    · rw [show c+2*((p-c)/2) = p by omega]
  · rw [address_hits hq (short.trans order) (unit q hq oddQ) (address ▸ dvd_mul_left q p)]
    rintro ⟨j, hj, hit⟩
    unfold oddColumn at hj
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hit


/-- The least odd integer at least l. -/
def firstOdd (l : ℕ) := 2*(l/2)+1

/-- Exact number of odd candidates in a nonempty interval that contains an odd number. -/
theorem column_length {l u : ℕ} (nonempty : firstOdd l ≤ u) :
    2*oddColumn (firstOdd l) u ≤ u+1-l+1 ∧
    u+1-l ≤ 2*oddColumn (firstOdd l) u+1 := by
  unfold firstOdd oddColumn at *
  omega

/-- With equal-width odd primes the complete odd lane uses only public endpoints. -/
theorem verified_row {n p q B : ℕ} (product : n=p*q) (hp : p.Prime) (hq : q.Prime)
    (order : p<q) (oddP : p%2=1) (oddQ : q%2=1) (lo : B≤p) (hi : q<2*B) :
    let c := firstOdd (ShortPascalRow.lower n B)
    (((n-c)/2).choose (oddColumn c n.sqrt)).gcd n = p := by
  subst n
  have ps := hp.two_le
  have lowerBound : ShortPascalRow.lower (p*q) B ≤ p := by
    unfold ShortPascalRow.lower
    apply max_le lo
    apply Nat.succ_le_of_lt
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    have := Nat.mul_le_mul_left p (show q≤2*B-1 by omega)
    have := Nat.mul_pos hp.pos hq.pos
    omega
  have upper := Nat.le_sqrt.mpr (Nat.mul_le_mul_left p order.le)
  have before := Nat.sqrt_lt.mpr (Nat.mul_lt_mul_of_pos_right order hq.pos)
  have above : B ≤ ShortPascalRow.lower (p*q) B := le_max_left _ _
  dsimp only
  apply odd_interval hp hq order oddP oddQ
  · unfold firstOdd; omega
  · unfold firstOdd; omega
  · exact upper
  · exact before
  · unfold oddColumn firstOdd; omega

/-- In the quotient row floor(a*p*q/d), the low digit modulo p is fixed by
the residue of a*q modulo d. This gives an exact threshold for each hidden prime. -/
theorem quotient_threshold {p q a d k : ℕ} (hp : p.Prime) (short : k<p) (pos : 0<d) :
    p ∣ ((a*(p*q)/d).choose k) ↔ p*((a*q)%d)<d*k := by
  have split : a*(p*q) = p*((a*q)%d) + d*(p*((a*q)/d)) := by
    conv_lhs => rw [show a*(p*q) = p*(a*q) by ring, ←Nat.mod_add_div (a*q) d]
    ring
  have less : p*((a*q)%d)/d < p := (Nat.div_lt_iff_lt_mul pos).mpr
    (Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ pos) hp.pos)
  rw [low_column hp short, split, Nat.add_mul_div_left _ _ pos, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt less, Nat.div_lt_iff_lt_mul pos, Nat.mul_comm k d]

end PrimeFactors.QuotientPascalMasks
