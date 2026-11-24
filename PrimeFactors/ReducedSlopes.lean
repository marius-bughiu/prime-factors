import PrimeFactors.Subgroup

namespace PrimeFactors

/-- Euclidean reduction for the exponent obtained from a product alone. -/
theorem gcd_predecessor_product {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (p-1).gcd (p*q-1) = (p-1).gcd (q-1) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  rw [Nat.succ_sub_one, Nat.succ_sub_one]
  have calcExp : (a+1)*(b+1)-1 = b + a*(b+1) := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  rw [calcExp, Nat.gcd_add_mul_left_right]

/-- In the cyclic group at p, raising to N-1 removes the common predecessor
divisor. This bounds the hidden period even when its complementary factor is unknown. -/
theorem order_product_predecessor_dvd {p q : ℕ} (hp : p.Prime) (hq : 0 < q)
    (u : (ZMod p)ˣ) :
    orderOf (u^(p*q-1)) ∣ (p-1) / (p-1).gcd (q-1) := by
  letI : Fact p.Prime := ⟨hp⟩
  let g := (p-1).gcd (q-1)
  have gd : g ∣ p*q-1 := by
    dsimp [g]
    rw [← gcd_predecessor_product hp.pos hq]
    exact Nat.gcd_dvd_right _ _
  obtain ⟨k, hk⟩ := gd
  apply orderOf_dvd_of_pow_eq_one
  rw [← pow_mul, hk]
  have decomp : g*k*((p-1)/g) = (p-1)*k := by
    rw [show g*k*((p-1)/g) = ((p-1)/g * g)*k by ring,
      Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]
  rw [decomp, pow_mul, ZMod.units_pow_card_sub_one_eq_one, one_pow]

/-- The two projected periods after the product-derived exponent are coprime. -/
theorem reduced_periods_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (x : (ZMod p)ˣ) (y : (ZMod q)ˣ) :
    (orderOf (x^(p*q-1))).Coprime (orderOf (y^(p*q-1))) := by
  apply Nat.Coprime.of_dvd (order_product_predecessor_dvd hp hq.pos x)
    (show orderOf (y^(p*q-1)) ∣ (q-1) / (p-1).gcd (q-1) by
      rw [Nat.mul_comm, Nat.gcd_comm]
      exact order_product_predecessor_dvd hq hp.pos y)
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ (Nat.sub_pos_of_lt hp.one_lt))

/-- If the period at p is bounded by m², the two geometric tables with exponents
i and m*j (0 ≤ i < m, 1 ≤ j ≤ m) must meet there, with a strictly positive gap. -/
theorem exists_reduced_table_collision {G : Type*} [Group G] [Finite G] (v : G) {m : ℕ}
    (hm : 0 < m) (small : orderOf v ≤ m*m) :
    ∃ i j : ℕ, i < m ∧ 0 < j ∧ j ≤ m ∧ i < m*j ∧ v^i = v^(m*j) := by
  let d := orderOf v
  let k := (d-1) / m
  let b := (d-1) % m
  have hd : 0 < d := orderOf_pos v
  have step : b + m*k = d-1 := Nat.mod_add_div _ _
  have bsmall : b < m := Nat.mod_lt _ hm
  have ksmall : k < m := (Nat.div_lt_iff_lt_mul hm).mpr (by dsimp [d]; omega)
  let i := m - 1 - b
  have delta : m*(k+1) = i + d := by rw [Nat.mul_add, Nat.mul_one]; dsimp [i]; omega
  refine ⟨i,k+1, by dsimp [i]; omega, Nat.succ_pos _, by omega, by omega, ?_⟩
  rw [delta, pow_add, pow_orderOf_eq_one, mul_one]

/-- A collision modulo the product supplies a positive exponent k killing
both projections. One divisor of k distinguishes them whenever at least one
is nontrivial. This includes pairs with an odd joint period. -/
theorem reduced_full_collision_splits {G H : Type*} [Group G] [Group H] (x : G) (y : H)
    {k : ℕ} (coprime : (orderOf x).Coprime (orderOf y))
    (nontrivial : x ≠ 1 ∨ y ≠ 1) (killedX : x^k = 1) :
    ∃ e : ℕ, e ∣ k ∧ ((x^e = 1 ∧ y^e ≠ 1) ∨ (x^e ≠ 1 ∧ y^e = 1)) := by
  by_cases hy : y = 1
  · exact ⟨1, one_dvd _, Or.inr ⟨by simpa [hy] using nontrivial, by simp [hy]⟩⟩
  · refine ⟨orderOf x, orderOf_dvd_of_pow_eq_one killedX, Or.inl ⟨pow_orderOf_eq_one _, ?_⟩⟩
    intro equal
    exact hy (orderOf_eq_one_iff.mp (coprime.symm.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one equal)))

/-- Scanning z ≤ sqrt(k) and trying z and k/z includes every divisor of k. -/
theorem divisor_at_small_endpoint {e k : ℕ} (hk : 0 < k) (he : e ∣ k) :
    ∃ z : ℕ, 0 < z ∧ z ≤ k.sqrt ∧ z ∣ k ∧ (e = z ∨ e = k/z) := by
  obtain ⟨t, eqn⟩ := he
  have ep : 0 < e := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at eqn; omega
  have tp : 0 < t := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at eqn; omega
  rcases le_total e t with h | h
  · exact ⟨e, ep, Nat.le_sqrt.mpr (eqn ▸ Nat.mul_le_mul_left e h), ⟨t,eqn⟩, Or.inl rfl⟩
  · refine ⟨t, tp, Nat.le_sqrt.mpr (eqn ▸ Nat.mul_le_mul_right t h), ⟨e,eqn.trans (Nat.mul_comm _ _)⟩, Or.inr ?_⟩
    rw [eqn, Nat.mul_div_cancel _ tp]

/-- Being a unit is an input-only certificate that no baby and giant meet at a prime divisor. -/
noncomputable def reducedTableProduct {n : ℕ} (v : ZMod n) (m : ℕ) : ZMod n :=
  ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m, (v^(m*(j+1)) - v^i)

/-- A failed, fully checked block bounds how large the common predecessor
divisor can still be. Every group operation in the unit certificate is modulo N. -/
theorem reduced_table_excludes {p q m : ℕ} (hp : p.Prime) (hq : 0 < q) (hm : 0 < m)
    (u : (ZMod (p*q))ˣ) (clear : IsUnit (reducedTableProduct ((u : ZMod (p*q)) ^ (p*q-1)) m)) :
    m*m < (p-1) / (p-1).gcd (q-1) := by
  letI : Fact p.Prime := ⟨hp⟩
  let f := ZMod.castHom (dvd_mul_right p q) (ZMod p)
  let x := ZMod.unitsMap (dvd_mul_right p q) u
  let v := x^(p*q-1)
  have period := order_product_predecessor_dvd hp hq x
  have size : 0 < (p-1) / (p-1).gcd (q-1) := Nat.div_pos
    (Nat.gcd_le_left _ (Nat.sub_pos_of_lt hp.one_lt)) (Nat.gcd_pos_of_pos_left _ (Nat.sub_pos_of_lt hp.one_lt))
  by_contra! short
  obtain ⟨i, j, hi, hj, upp, _, matchAt⟩ :=
    exists_reduced_table_collision v hm ((Nat.le_of_dvd size period).trans short)
  have nonzero := (clear.map f).ne_zero
  unfold reducedTableProduct at nonzero
  simp only [map_prod, map_sub, map_pow] at nonzero
  have entry := Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp nonzero i (Finset.mem_range.mpr hi))
    (j-1) (Finset.mem_range.mpr (show j-1 < m by omega))
  rw [Nat.sub_add_cancel hj] at entry
  apply entry
  apply sub_eq_zero.mpr
  have eqn := congrArg Units.val matchAt.symm
  simpa only [v, Units.val_pow_eq_pow_val] using eqn

/-- The packed convolution in the experiment computes this scaled polynomial
evaluation. Its scale is a unit whenever v is. -/
theorem scaled_geometric_evaluation {R : Type*} [CommSemiring R] (v : R) (a : ℕ → R) (i d : ℕ) :
    v ^ (i.choose 2 + d.choose 2) * (∑ j ∈ Finset.range (d+1), a j * (v^i)^j) =
      ∑ j ∈ Finset.range (d+1), a j * v ^ (d.choose 2 - j.choose 2) * v ^ ((i+j).choose 2) := by
  have choose_add (j : ℕ) : (i+j).choose 2 = i.choose 2 + j.choose 2 + i*j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [← Nat.add_assoc, Nat.choose_succ_succ' (i+j) 1, Nat.choose_succ_succ' j 1,
        Nat.choose_one_right, Nat.choose_one_right, ih, Nat.mul_succ]
      norm_num1 at *
      omega
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have mono := Nat.choose_le_choose 2 (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  rw [← pow_mul, mul_left_comm, ← pow_add, mul_assoc, ← pow_add, choose_add]
  congr 2
  omega

private theorem cyclic_killed_count {G : Type*} [Group G] [IsCyclic G] [Fintype G] [DecidableEq G]
    (e : ℕ) : (Finset.univ.filter (fun x : G => x^e = 1)).card = (Fintype.card G).gcd e := by
  classical
  let g := (Fintype.card G).gcd e
  have same : (Finset.univ.filter (fun x : G => x^e = 1)) =
      Finset.univ.filter (fun x : G => x^g = 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← orderOf_dvd_iff_pow_eq_one]
    exact ⟨fun h => Nat.dvd_gcd orderOf_dvd_card h, fun h => h.trans (Nat.gcd_dvd_right _ _)⟩
  rw [same, ← sum_card_orderOf_eq_card_pow_eq_one (Nat.gcd_pos_of_pos_left e Fintype.card_pos).ne']
  calc
    _ = ∑ i ∈ g.divisors, i.totient := Finset.sum_congr rfl (fun i hi =>
      IsCyclic.card_orderOf_eq_totient ((Nat.dvd_of_mem_divisors hi).trans (Nat.gcd_dvd_left _ _)))
    _ = _ := Nat.sum_totient g

/-- Exact number of uninformative bases among all units of a distinct semiprime.
Dividing by (p-1)(q-1) gives failure probability 1/(r*s). -/
theorem count_product_predecessor_identity {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (different : p ≠ q) [NeZero (p*q)] :
    (Finset.univ.filter (fun x : (ZMod (p*q))ˣ => x^(p*q-1) = 1)).card =
      ((p-1).gcd (q-1))^2 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  let e := p*q-1
  let iso : (ZMod (p*q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr different)).toMulEquiv).trans
      MulEquiv.prodUnits
  let xs := Finset.univ.filter (fun x : (ZMod p)ˣ => x^e = 1)
  let ys := Finset.univ.filter (fun x : (ZMod q)ˣ => x^e = 1)
  have transfer : (Finset.univ.filter (fun x : (ZMod (p*q))ˣ => x^e = 1)).card =
      (xs ×ˢ ys).card := by
    apply Finset.card_bijective iso iso.bijective
    intro x
    simp only [xs, ys, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    change x^e = 1 ↔ (iso x ^ e).1 = (1 : (ZMod p)ˣ × (ZMod q)ˣ).1 ∧
      (iso x ^ e).2 = (1 : (ZMod p)ˣ × (ZMod q)ˣ).2
    rw [← Prod.ext_iff, ← map_pow, ← map_one iso, iso.injective.eq_iff]
  change _ = _
  rw [transfer, Finset.card_product]
  dsimp only [xs,ys]
  rw [cyclic_killed_count, cyclic_killed_count, (Nat.prime_iff_card_units p).mp hp,
    (Nat.prime_iff_card_units q).mp hq]
  dsimp only [e]
  rw [gcd_predecessor_product hp.pos hq.pos, Nat.mul_comm p q, gcd_predecessor_product hq.pos hp.pos,
    Nat.gcd_comm (q-1), pow_two]

end PrimeFactors
