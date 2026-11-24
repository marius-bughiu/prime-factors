import PrimeFactors.ReducedSlopes

namespace PrimeFactors

/-- Modulo the order of the units at p, the product acts on exponents as q does. -/
theorem gcd_product_power_predecessor {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (k : ℕ) :
    (p-1).gcd ((p*q)^k-1) = (p-1).gcd (q^k-1) := by
  have h : (p*q)^k ≡ q^k [MOD p-1] := by
    simpa using ((Nat.modEq_sub hp).mul_right q).pow k
  have h' : (p*q)^k-1 ≡ q^k-1 [MOD p-1] := by
    apply Nat.ModEq.add_right_cancel' 1
    simpa only [Nat.sub_add_cancel (Nat.pow_pos (Nat.mul_pos hp hq)),
      Nat.sub_add_cancel (Nat.pow_pos hq)] using h
  simpa only [Nat.gcd_comm (p-1)] using h'.gcd_eq

/-- The geometric multiplier (N^k-1)/(N-1) is an integer. -/
theorem predecessor_dvd_power_predecessor {n : ℕ} (hn : 0 < n) (k : ℕ) :
    n-1 ∣ n^k-1 := by
  apply (Nat.modEq_iff_dvd' (Nat.pow_pos hn)).mp
  simpa using ((Nat.modEq_sub hn).pow k).symm

/-- Raising a unit to an arbitrary known exponent deletes its intersection
with the local group size, whether or not any primes of that size are known. -/
theorem local_order_dvd_residual {p : ℕ} (hp : p.Prime) (u : (ZMod p)ˣ) (e : ℕ) :
    orderOf (u^e) ∣ (p-1) / (p-1).gcd e := by
  letI : Fact p.Prime := ⟨hp⟩
  let g := (p-1).gcd e
  obtain ⟨t, ht⟩ : g ∣ e := Nat.gcd_dvd_right _ _
  have kill : e * ((p-1)/g) = (p-1)*t := by
    calc
      e*((p-1)/g) = ((p-1)/g * g)*t := by rw [ht]; ring
      _ = (p-1)*t := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]
  apply orderOf_dvd_of_pow_eq_one
  change (u^e)^((p-1)/g) = 1
  rw [← pow_mul, kill, pow_mul, ZMod.units_pow_card_sub_one_eq_one, one_pow]

/-- The product-only exponent N^k-1 removes the part of p-1 dividing q^k-1. -/
theorem cyclotomic_period_dvd {p q : ℕ} (hp : p.Prime) (hq : 0 < q)
    (u : (ZMod p)ˣ) (k : ℕ) :
    orderOf (u^((p*q)^k-1)) ∣ (p-1) / (p-1).gcd (q^k-1) := by
  rw [← gcd_product_power_predecessor hp.pos hq]
  exact local_order_dvd_residual hp u _

/-- A shared divisor of p-1 and the cubic cyclotomic value at q gives a
concrete upper bound for the period, even if it divides neither q-1 nor q+1. -/
theorem cubic_period_le_of_common_divisor {p q d : ℕ} (hp : p.Prime) (hq : 0 < q)
    (u : (ZMod p)ˣ) (hd : d ∣ p-1) (hc : d ∣ q^2+q+1) :
    orderOf (u^((p*q)^3-1)) ≤ (p-1)/d := by
  have identity : q^3-1 = (q-1)*(q^2+q+1) := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
    rw [Nat.succ_sub_one, Nat.succ_eq_add_one]
    apply Nat.sub_eq_of_eq_add
    ring
  have both : d ∣ (p-1).gcd (q^3-1) :=
    Nat.dvd_gcd hd (identity ▸ hc.trans (dvd_mul_left _ _))
  have pos := Nat.sub_pos_of_lt hp.one_lt
  have gp := Nat.gcd_pos_of_pos_left (q^3-1) pos
  have rp := Nat.div_pos (Nat.gcd_le_left (q^3-1) pos) gp
  exact (Nat.le_of_dvd rp (cyclotomic_period_dvd hp hq u 3)).trans
    (Nat.div_le_div_left (Nat.le_of_dvd gp both) (Nat.pos_of_dvd_of_pos hd pos))

/-- Complementary-divisor recovery from a whole collision stays valid after
any further powering of the predecessor base. -/
theorem extended_periods_coprime {p q e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (x : (ZMod p)ˣ) (y : (ZMod q)ˣ) (multiple : p*q-1 ∣ e) :
    (orderOf (x^e)).Coprime (orderOf (y^e)) := by
  obtain ⟨t, rfl⟩ := multiple
  rw [pow_mul, pow_mul]
  exact (reduced_periods_coprime hp hq x y).of_dvd
    (orderOf_pow_dvd (x := x^(p*q-1)) t) (orderOf_pow_dvd (x := y^(p*q-1)) t)

/-- An exhausted product-only table also excludes large common divisors
of p-1 and q^k-1, even when these two integers are both unknown. -/
theorem cyclotomic_table_excludes {p q m k : ℕ} (hp : p.Prime) (hq : 0 < q) (hm : 0 < m)
    (u : (ZMod (p*q))ˣ)
    (clear : IsUnit (reducedTableProduct ((u : ZMod (p*q)) ^ ((p*q)^k-1)) m)) :
    m*m * (p-1).gcd (q^k-1) < p-1 := by
  letI : Fact p.Prime := ⟨hp⟩
  let f := ZMod.castHom (dvd_mul_right p q) (ZMod p)
  let x := ZMod.unitsMap (dvd_mul_right p q) u
  let v := x^((p*q)^k-1)
  let g := (p-1).gcd (q^k-1)
  have pos := Nat.sub_pos_of_lt hp.one_lt
  have gp : 0 < g := Nat.gcd_pos_of_pos_left _ pos
  have rp : 0 < (p-1)/g := Nat.div_pos (Nat.gcd_le_left _ pos) gp
  have shortImpossible : m*m < (p-1)/g := by
    by_contra! short
    obtain ⟨i, j, hi, hj, upper, _, matchAt⟩ := exists_reduced_table_collision v hm
      ((Nat.le_of_dvd rp (cyclotomic_period_dvd hp hq x k)).trans short)
    have nonzero := (clear.map f).ne_zero
    unfold reducedTableProduct at nonzero
    simp only [map_prod, map_sub, map_pow] at nonzero
    have entry := Finset.prod_ne_zero_iff.mp
      (Finset.prod_ne_zero_iff.mp nonzero i (Finset.mem_range.mpr hi))
      (j-1) (Finset.mem_range.mpr (show j-1 < m by omega))
    rw [Nat.sub_add_cancel hj] at entry
    apply entry
    apply sub_eq_zero.mpr
    simpa only [v, Units.val_pow_eq_pow_val] using congrArg Units.val matchAt.symm
  exact (Nat.mul_lt_mul_of_pos_right shortImpossible gp).trans_le (Nat.div_mul_le_self _ _)

/-- In the identity branch, test powers of the odd part of the known exponent.
The first component to reach 1 separates the primes when the 2-primary orders differ. -/
theorem halving_chain_separates {G H : Type*} [Group G] [Group H] (x : G) (y : H)
    {t : ℕ} (hx : x^(2^t : ℕ) = 1) (hy : y^(2^t : ℕ) = 1)
    (different : orderOf x ≠ orderOf y) :
    ∃ i < t, (x^(2^i : ℕ) = 1 ∧ y^(2^i : ℕ) ≠ 1) ∨
      (x^(2^i : ℕ) ≠ 1 ∧ y^(2^i : ℕ) = 1) := by
  obtain ⟨a, ha, xa⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
  obtain ⟨b, hb, yb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hy)
  have ab : a ≠ b := fun eqn => different (xa.trans (eqn ▸ yb.symm))
  simp only [ne_eq, ← orderOf_dvd_iff_pow_eq_one, xa, yb,
    Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2:ℕ))]
  rcases lt_or_gt_of_ne ab with small | small
  · exact ⟨a, by omega, Or.inl ⟨le_rfl, by omega⟩⟩
  · exact ⟨b, by omega, Or.inr ⟨by omega, le_rfl⟩⟩

end PrimeFactors
