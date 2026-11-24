import PrimeFactors.Subgroup
import PrimeFactors.Isolation

namespace PrimeFactors

/-- The exponent on the right is known from the product alone. -/
theorem unit_pow_factorSum {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (u : (ZMod (p * q))ˣ) : u ^ (p + q) = u ^ (p * q + 1) := by
  letI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have one := pow_card_eq_one (x := u)
  rw [ZMod.card_units_eq_totient, Nat.totient_mul ((Nat.coprime_primes hp hq).2 hne),
    Nat.totient_prime hp, Nat.totient_prime hq] at one
  have identity : p * q + 1 = (p - 1) * (q - 1) + (p + q) := by
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne_zero
    rw [hi, hj]
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    ring
  rw [identity, pow_add _ ((p - 1) * (q - 1)), one, one_mul]

/-- If an exponent gap is shorter than q−1, at least one small prime unit has unequal
powers at the two exponents. The size of the base set enters only through the
published small-prime-outside-subgroups hypothesis. -/
theorem exists_separating_power_base {p q B s d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (small : SmallPrimeOutside (p * q) B) (hd : 0 < d) (short : d < q - 1) :
    ∃ a, a.Prime ∧ a ≤ B ∧ ∃ ha : a.Coprime (p * q),
      (ZMod.unitOfCoprime a ha) ^ (s + d) ≠ (ZMod.unitOfCoprime a ha) ^ s := by
  letI : Fact q.Prime := ⟨hq⟩
  letI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  let f := powMonoidHom (α := (ZMod (p * q))ˣ) d
  have proper : f.ker ≠ ⊤ := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
    let π := ZMod.unitsMap (dvd_mul_left q p)
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (dvd_mul_left q p) g
    intro full
    have inKer : u ∈ f.ker := full ▸ Subgroup.mem_top u
    have eqn : u ^ d = 1 := inKer
    have mapped := congrArg π eqn
    rw [map_pow, map_one] at mapped
    change ZMod.unitsMap _ u = g at hu
    change (ZMod.unitsMap _ u) ^ d = 1 at mapped
    rw [hu] at mapped
    have divides := orderOf_dvd_of_pow_eq_one mapped
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      (Nat.prime_iff_card_units q).1 hq] at divides
    exact (Nat.not_le_of_lt short) (Nat.le_of_dvd hd divides)
  obtain ⟨a, prime, bound, ha, outside⟩ := small f.ker proper
  refine ⟨a, prime, bound, ha, fun same => outside ?_⟩
  change (ZMod.unitOfCoprime a ha) ^ d = 1
  simpa [pow_add] using same

/-- Any two distinct integers in the balanced factor-sum interval differ by less
than q−1. This includes the endpoint rounding and uses no unknown factor as input
to the interval tests. -/
theorem balanced_window_difference_lt {p q s t : ℕ} (hp : 0 < p) (hq : 2 < q)
    (pq : p ≤ q) (lower : 4 * (p * q) ≤ s ^ 2) (upper : 2 * t ^ 2 ≤ 9 * (p * q))
    (st : s ≤ t) : t - s < q - 1 := by
  have ps : p ≤ s := Nat.mul_self_le_mul_self_iff.mp (by
    nlinarith [Nat.mul_le_mul_left p pq])
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le st
  simp only [Nat.add_sub_cancel_left]
  by_contra! fail
  have qd : q ≤ 2 * d := by omega
  have cross := Nat.mul_le_mul ps qd
  nlinarith

/-- In the balanced search interval, equality of all small-prime power coordinates
with the product-derived target is equivalent to having the true factor sum. -/
theorem power_signature_iff_sum {p q s B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (pq : p < q) (balance : q ≤ 2 * p) (small : SmallPrimeOutside (p * q) B)
    (lower : 4 * (p * q) ≤ s ^ 2) (upper : 2 * s ^ 2 ≤ 9 * (p * q)) :
    (∀ a : ℕ, a.Prime → a ≤ B → ∀ ha : a.Coprime (p * q),
      (ZMod.unitOfCoprime a ha) ^ s = (ZMod.unitOfCoprime a ha) ^ (p * q + 1)) ↔
      s = p + q := by
  constructor
  · intro pass
    have ⟨trueLower, trueUpper⟩ := balanced_factorSum_bounds pq.le balance
    have qlarge : 2 < q := lt_of_le_of_lt hp.two_le pq
    have agree (a : ℕ) (prime : a.Prime) (bound : a ≤ B) (ha : a.Coprime (p * q)) :
        (ZMod.unitOfCoprime a ha) ^ s = (ZMod.unitOfCoprime a ha) ^ (p + q) :=
      (pass a prime bound ha).trans (unit_pow_factorSum hp hq pq.ne _).symm
    rcases lt_trichotomy s (p + q) with h | h | h
    · have short := balanced_window_difference_lt hp.pos qlarge pq.le lower trueUpper h.le
      obtain ⟨a, prime, bound, ha, diff⟩ := exists_separating_power_base (s := s) hp hq
        small (Nat.sub_pos_of_lt h) short
      rw [Nat.add_sub_of_le h.le] at diff
      exact (diff (agree a prime bound ha).symm).elim
    · exact h
    · have short := balanced_window_difference_lt hp.pos qlarge pq.le trueLower upper h.le
      obtain ⟨a, prime, bound, ha, diff⟩ := exists_separating_power_base (s := p + q) hp hq
        small (Nat.sub_pos_of_lt h) short
      rw [Nat.add_sub_of_le h.le] at diff
      exact (diff (agree a prime bound ha)).elim
  · rintro rfl a _ _ ha
    exact unit_pow_factorSum hp hq pq.ne _

/-- The collision checked by a baby-step/giant-step table is exactly the power
equation at the corresponding candidate. Applies coordinatewise or to a product group. -/
theorem power_table_match_iff {G : Type*} [CommGroup G] (u target : G) (L i m j : ℕ) :
    u ^ j = target / (u ^ L * (u ^ m) ^ i) ↔ u ^ (L + m * i + j) = target := by
  rw [eq_div_iff_mul_eq'', pow_add, pow_add, pow_mul]

/-- Filter the baby indices by the product modulo the stride before building the
power table. Both the residue test and the target use only the input product. -/
theorem sieved_power_table_iff_sum {p q B L m i j : ℕ} (hp : p.Prime) (hq : q.Prime)
    (pq : p < q) (balance : q ≤ 2 * p) (small : SmallPrimeOutside (p * q) B)
    (lower : 4 * (p * q) ≤ (L + m * i + j) ^ 2)
    (upper : 2 * (L + m * i + j) ^ 2 ≤ 9 * (p * q)) :
    (AdmissibleSum ((p * q : ℕ) : ZMod m) ((L + j : ℕ) : ZMod m) ∧
      ∀ a : ℕ, a.Prime → a ≤ B → ∀ ha : a.Coprime (p * q),
        let u := ZMod.unitOfCoprime a ha
        u ^ j = u ^ (p * q + 1) / (u ^ L * (u ^ m) ^ i)) ↔
      L + m * i + j = p + q := by
  have sigEq := power_signature_iff_sum hp hq pq balance small lower upper
  constructor
  · rintro ⟨_, matchAt⟩
    apply sigEq.mp
    intro a prime bound ha
    exact (power_table_match_iff _ _ _ _ _ _).mp (matchAt a prime bound ha)
  · intro eqn
    constructor
    · have localSum := admissibleSum_of_factor_pair m (p := p) (q := q) rfl
      rw [← eqn] at localSum
      simpa [ZMod.natCast_self] using localSum
    · intro a prime bound ha
      exact (power_table_match_iff _ _ _ _ _ _).mpr ((sigEq.mpr eqn) a prime bound ha)

end PrimeFactors
