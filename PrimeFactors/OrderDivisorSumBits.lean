import PrimeFactors.ReducedSlopes
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-! Sum congruences from certified divisors of the exponent of the unit group.
The first sum bit beyond modulus four also has a direct square-class interpretation. -/

namespace PrimeFactors.OrderDivisorSumBits

private theorem gcd_lcm_distrib {a b n : ℕ} (ha : 0<a) (hb : 0<b) (hn : 0<n) :
    (a.lcm b).gcd n = (a.gcd n).lcm (b.gcd n) := by
  have hl := Nat.lcm_ne_zero ha.ne' hb.ne'
  have ga := (Nat.gcd_pos_of_pos_left n ha).ne'
  have gb := (Nat.gcd_pos_of_pos_left n hb).ne'
  apply Nat.factorization_inj (Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hl)).ne'
    (Nat.lcm_ne_zero ga gb)
  rw [Nat.factorization_gcd hl hn.ne', Nat.factorization_lcm ha.ne' hb.ne',
    Nat.factorization_lcm ga gb, Nat.factorization_gcd ha.ne' hn.ne',
    Nat.factorization_gcd hb.ne' hn.ne']
  ext i
  change min (max _ _) _ = max (min _ _) (min _ _)
  omega

theorem gcd_exponent {p q : ℕ} (hp : 1<p) (hq : 1<q) :
    ((p-1).lcm (q-1)).gcd (p*q-1) = (p-1).gcd (q-1) := by
  have prod : 1 < p*q := by nlinarith
  rw [gcd_lcm_distrib (by omega) (by omega) (by omega),
    gcd_predecessor_product (by omega) (by omega)]
  rw [Nat.mul_comm p q, gcd_predecessor_product (by omega) (by omega),
    Nat.gcd_comm (q-1), Nat.lcm_self]

/-- With the full exponent the multiple of the unknown totient is exact. -/
theorem totient_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ne : p≠q) :
    (p*q).totient =
      ((p-1).lcm (q-1)) * (((p-1).lcm (q-1)).gcd (p*q-1)) := by
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).mpr ne),Nat.totient_prime hp,
    Nat.totient_prime hq,gcd_exponent hp.one_lt hq.one_lt,mul_comm ((p-1).lcm (q-1)),
    Nat.gcd_mul_lcm]

private theorem sum_mod_iff {p q m : ℕ} (hp : 1≤p) (hq : 1≤q) :
    p+q ≡ p*q+1 [MOD m] ↔ m ∣ (p-1)*(q-1) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p≠0)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q≠0)
  simp only [Nat.succ_sub_one]
  have product : (a+1)*(b+1)+1 = (a+1+(b+1))+a*b := by ring
  rw [product,Nat.modEq_iff_dvd' (Nat.le_add_right _ _),Nat.add_sub_cancel_left]

/-- Only a divisor of the group exponent is needed. The resulting modulus
depends on the given divisor and the public product. -/
theorem of_dvd_exponent {p q m : ℕ} (hp : 1<p) (hq : 1<q)
    (orderDvd : m ∣ (p-1).lcm (q-1)) :
    p+q ≡ p*q+1 [MOD m*m.gcd (p*q-1)] := by
  apply (sum_mod_iff hp.le hq.le).mpr
  have common : m.gcd (p*q-1) ∣ ((p-1).lcm (q-1)).gcd (p*q-1) :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans orderDvd) (Nat.gcd_dvd_right _ _)
  rw [gcd_exponent hp hq] at common
  rw [← Nat.gcd_mul_lcm (p-1) (q-1),mul_comm m]
  exact Nat.mul_dvd_mul common orderDvd

theorem unit_order_dvd {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ne : p≠q)
    (u : (ZMod (p*q))ˣ) : orderOf u ∣ (p-1).lcm (q-1) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  let e := (Units.mapEquiv (ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr ne)).toMulEquiv).trans
    MulEquiv.prodUnits
  rw [←e.orderOf_eq u, Prod.orderOf]
  apply Nat.lcm_dvd
  · apply dvd_trans _ (Nat.dvd_lcm_left _ _)
    exact orderOf_dvd_of_pow_eq_one (ZMod.units_pow_card_sub_one_eq_one p (e u).1)
  · apply dvd_trans _ (Nat.dvd_lcm_right _ _)
    exact orderOf_dvd_of_pow_eq_one (ZMod.units_pow_card_sub_one_eq_one q (e u).2)

/-- One power identity and one nonidentity per distinct prime divisor of m
certify the exact order. All powers are taken modulo the public product. -/
theorem certified {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (ne : p≠q)
    (u : (ZMod (p*q))ˣ) (pos : 0<m) (kill : u^m=1)
    (minimal : ∀ r : ℕ, r.Prime → r∣m → u^(m/r)≠1) :
    p+q ≡ p*q+1 [MOD m*m.gcd (p*q-1)] := by
  apply of_dvd_exponent hp.one_lt hq.one_lt
  rw [←orderOf_eq_of_pow_and_pow_div_prime pos kill minimal]
  exact unit_order_dvd hp hq ne u

/-- A certified factor 2^c of the exponent gives c plus min(c,v₂(N−1))
low sum bits without requiring the rest of the exponent. -/
theorem dyadic_of_dvd {p q c : ℕ} (hp : 1<p) (hq : 1<q)
    (orderDvd : 2^c ∣ (p-1).lcm (q-1)) :
    p+q ≡ p*q+1 [MOD 2^(c+min c ((p*q-1).factorization 2))] := by
  have hn : p*q-1≠0 := by
    have : 1<p*q := by nlinarith
    omega
  apply (of_dvd_exponent hp hq orderDvd).of_dvd
  rw [pow_add]
  apply Nat.mul_dvd_mul (dvd_refl _)
  exact Nat.dvd_gcd (Nat.pow_dvd_pow 2 (min_le_left ..))
    ((Nat.prime_two.pow_dvd_iff_le_factorization hn).mpr (min_le_right ..))

/-- The exact count is also the sum of the two local predecessor valuations. -/
theorem local_bits_iff {p q k : ℕ} (hp : 1<p) (hq : 1<q) :
    p+q ≡ p*q+1 [MOD 2^k] ↔ k ≤ (p-1).factorization 2 + (q-1).factorization 2 := by
  have ha : p-1 ≠ 0 := by omega
  have hb : q-1 ≠ 0 := by omega
  rw [sum_mod_iff hp.le hq.le, Nat.prime_two.pow_dvd_iff_le_factorization (mul_ne_zero ha hb),
    Nat.factorization_mul ha hb, Finsupp.add_apply]

/-- Exact length of the agreement of the low bits of S and N+1, given the
2-adic order of the full exponent. The public valuation of N−1 truncates
the extra bits contributed by the smaller local predecessor valuation. -/
theorem dyadic_iff {p q k : ℕ} (hp : 1<p) (hq : 1<q) :
    p+q ≡ p*q+1 [MOD 2^k] ↔
      k ≤ ((p-1).lcm (q-1)).factorization 2 +
        min (((p-1).lcm (q-1)).factorization 2) ((p*q-1).factorization 2) := by
  have ha : p-1≠0 := by omega
  have hb : q-1≠0 := by omega
  have hl := Nat.lcm_ne_zero ha hb
  have hn : p*q-1≠0 := by
    have : 1<p*q := by nlinarith
    omega
  have hg := (Nat.gcd_pos_of_pos_left (p*q-1) (Nat.pos_of_ne_zero hl)).ne'
  rw [sum_mod_iff hp.le hq.le,←Nat.gcd_mul_lcm (p-1) (q-1),←gcd_exponent hp hq,
    Nat.prime_two.pow_dvd_iff_le_factorization (mul_ne_zero hg hl),
    Nat.factorization_mul hg hl, Finsupp.add_apply, Nat.factorization_gcd hl hn]
  change (_ ≤ min _ _ + _) ↔ _
  omega

private theorem neg_one_square {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ne : p≠q) :
    IsSquare (-1 : ZMod (p*q)) ↔ p%4≠3 ∧ q%4≠3 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  let e := ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr ne)
  rw [←ZMod.exists_sq_eq_neg_one_iff,←ZMod.exists_sq_eq_neg_one_iff]
  constructor
  · intro h
    have h' : IsSquare (-1 : ZMod p × ZMod q) := by simpa using h.map e
    obtain ⟨r, hr⟩ := h'
    exact ⟨⟨r.1,congrArg Prod.fst hr⟩,⟨r.2,congrArg Prod.snd hr⟩⟩
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    have h : IsSquare (-1 : ZMod p × ZMod q) := ⟨(x,y),Prod.ext hx hy⟩
    simpa using h.map e.symm

private theorem mod_eight (p q : ℕ) (hp : Odd p) (hq : Odd q) :
    ((p*q)%4=1 → (p+q ≡ p*q+1 [MOD 8] ↔ p%4≠3 ∧ q%4≠3)) ∧
    ((p*q)%4=3 → p+q ≡ p*q+1 [MOD 8]) := by
  let a : Fin 8 := ⟨p%8,Nat.mod_lt _ (by decide)⟩
  let b : Fin 8 := ⟨q%8,Nat.mod_lt _ (by decide)⟩
  have table : ∀ x y : Fin 8, x.val%2=1 → y.val%2=1 →
      ((x.val*y.val%4=1 → (x.val+y.val ≡ x.val*y.val+1 [MOD 8] ↔ x.val%4≠3 ∧ y.val%4≠3)) ∧
       (x.val*y.val%4=3 → x.val+y.val ≡ x.val*y.val+1 [MOD 8])) := by decide
  have ap : a.val ≡ p [MOD 8] := Nat.mod_modEq p 8
  have bq : b.val ≡ q [MOD 8] := Nat.mod_modEq q 8
  have four : 4∣8 := by decide
  have two : 2∣8 := by decide
  have ar := ap.of_dvd four
  have br := bq.of_dvd four
  have product := (ap.mul bq).of_dvd four
  have sum8 := ap.add bq
  have plus8 := (ap.mul bq).add_right 1
  specialize table a b (Eq.trans (ap.of_dvd two) (Nat.odd_iff.mp hp)) (Eq.trans (bq.of_dvd two) (Nat.odd_iff.mp hq))
  unfold Nat.ModEq at ar br product sum8 plus8 table ⊢
  simpa only [ar,br,product,sum8,plus8] using table

theorem first_unknown_bit {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ne : p≠q)
    (po : p≠2) (qo : q≠2) (one : (p*q)%4=1) :
    p+q ≡ p*q+1 [MOD 8] ↔ IsSquare (-1 : ZMod (p*q)) := by
  rw [neg_one_square hp hq ne]
  exact (mod_eight p q (hp.odd_of_ne_two po) (hq.odd_of_ne_two qo)).1 one

theorem sum_of_three_mod_four {p q : ℕ} (hp : Odd p) (hq : Odd q) (three : (p*q)%4=3) :
    p+q ≡ p*q+1 [MOD 8] := (mod_eight p q hp hq).2 three

theorem square_gives_four_bits {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ne : p≠q) (po : p≠2) (qo : q≠2) (root : IsSquare (-1 : ZMod (p*q))) :
    p+q ≡ p*q+1 [MOD 16] := by
  obtain ⟨pr,qr⟩ := (neg_one_square hp hq ne).mp root
  have pp := Nat.odd_iff.mp (hp.odd_of_ne_two po)
  have qq := Nat.odd_iff.mp (hq.odd_of_ne_two qo)
  apply (sum_mod_iff hp.one_lt.le hq.one_lt.le).mpr
  exact Nat.mul_dvd_mul (by omega : 4∣p-1) (by omega : 4∣q-1)

theorem nonsquare_bit {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ne : p≠q)
    (po : p≠2) (qo : q≠2) (one : (p*q)%4=1) (miss : ¬IsSquare (-1 : ZMod (p*q))) :
    p+q+4 ≡ p*q+1 [MOD 8] := by
  have pp := Nat.odd_iff.mp (hp.odd_of_ne_two po)
  have qq := Nat.odd_iff.mp (hq.odd_of_ne_two qo)
  have four : p+q ≡ p*q+1 [MOD 4] := (sum_mod_iff hp.one_lt.le hq.one_lt.le).mpr
    (Nat.mul_dvd_mul (by omega : 2∣p-1) (by omega : 2∣q-1))
  have eight := mt (first_unknown_bit hp hq ne po qo one).mp miss
  unfold Nat.ModEq at *
  omega

/-- Two balanced products have the same last five bits and different sum
residues. One square root of minus one is 776 for the second product. -/
theorem same_low_word :
    (71*127:ℕ)%32=25 ∧ (73*113:ℕ)%32=25 ∧ (71+127:ℕ)%8=6 ∧ (73+113:ℕ)%8=2 ∧
      ¬IsSquare (-1 : ZMod (71*127)) ∧ (776:ZMod (73*113))^2 = -1 := by
  refine ⟨by decide,by decide,by decide,by decide,?_,by decide⟩
  rw [neg_one_square (by decide) (by decide) (by decide)]
  decide

end PrimeFactors.OrderDivisorSumBits
