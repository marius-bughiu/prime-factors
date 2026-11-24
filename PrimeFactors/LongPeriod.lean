import PrimeFactors.AdditiveCover
import PrimeFactors.FactorSumCRT
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.PrimesCongruentOne

namespace PrimeFactors

/-- At a prime congruent to one modulo eight and modulo d, every prime factor
of the nonnegative integer d is a square, by quadratic reciprocity. -/
theorem isSquare_of_prime_one_mod {ℓ : ℕ} [Fact ℓ.Prime]
    (eight : ℓ ≡ 1 [MOD 8]) (d : ℕ) (cong : ℓ ≡ 1 [MOD d]) :
    IsSquare (d : ZMod ℓ) := by
  have mod8 : ℓ % 8 = 1 := eight
  have mod4 : ℓ % 4 = 1 := eight.of_dvd (by decide : 4 ∣ 8)
  have odd : ℓ ≠ 2 := by omega
  induction d using Nat.recOnMul with
  | h0 => simp
  | h1 => simp
  | hp r hr =>
    by_cases two : r = 2
    · simpa [two] using (ZMod.exists_sq_eq_two_iff odd).mpr (Or.inl mod8)
    · letI : Fact r.Prime := ⟨hr⟩
      apply (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one mod4 two).mpr
      exact (ZMod.natCast_eq_natCast_iff ℓ 1 r).mpr cong ▸ (by simp)
  | h a b ha hb =>
    rw [Nat.cast_mul]
    exact (ha (cong.of_dvd (dvd_mul_right a b))).mul (hb (cong.of_dvd (dvd_mul_left b a)))

/-- Arbitrarily large primes let every candidate with nonnegative discriminant
through simultaneously, throughout any fixed finite search region. -/
theorem exists_prime_passing_interval (n upper threshold : ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ n < ℓ ∧ threshold < ℓ ∧
      ∀ s ≤ upper, 4 * n ≤ s ^ 2 → AdmissibleSum (n : ZMod ℓ) (s : ZMod ℓ) := by
  let f := (upper ^ 2).factorial
  have hf : f ≠ 0 := Nat.factorial_ne_zero _
  obtain ⟨ℓ, prime, large, cong⟩ := Nat.exists_prime_gt_modEq_one
    (max 2 (max n threshold)) (by simp [hf] : 8 * f ≠ 0)
  letI : Fact ℓ.Prime := ⟨prime⟩
  have eight : ℓ ≡ 1 [MOD 8] := cong.of_dvd (dvd_mul_right 8 f)
  have odd : ℓ ≠ 2 := by omega
  refine ⟨ℓ, prime, odd, by omega, by omega, ?_⟩
  intro s hs lower
  let d := s ^ 2 - 4 * n
  have sq : IsSquare (d : ZMod ℓ) := by
    by_cases zero : d = 0
    · simp [zero]
    · have le : d ≤ upper ^ 2 := (Nat.sub_le _ _).trans (Nat.pow_le_pow_left hs 2)
      have divides : d ∣ f := Nat.dvd_factorial (Nat.pos_of_ne_zero zero) le
      exact isSquare_of_prime_one_mod eight d (cong.of_dvd (dvd_mul_of_dvd_right divides 8))
  apply (admissibleSum_iff_isSquare odd _ _).mpr
  simpa [d, Nat.cast_sub lower] using sq

/-- The number of distinct prime tests alone gives no worst-case pruning bound
for a freely chosen set of auxiliary primes, even if all exceed the interval width. -/
theorem exists_prime_set_passing_interval (n upper threshold k : ℕ) :
    ∃ P : Finset ℕ, P.card = k ∧
      ∀ ℓ ∈ P, ℓ.Prime ∧ ℓ ≠ 2 ∧ n < ℓ ∧ threshold < ℓ ∧
        ∀ s ≤ upper, 4 * n ≤ s ^ 2 → AdmissibleSum (n : ZMod ℓ) (s : ZMod ℓ) := by
  induction k with
  | zero => exact ⟨∅, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨P, size, good⟩ := ih
    obtain ⟨ℓ, prime, odd, cop, large, pass⟩ :=
      exists_prime_passing_interval n upper (max threshold (P.sup id))
    have fresh : ℓ ∉ P := fun h => (not_le_of_gt large)
      (le_max_of_le_right (Finset.le_sup (f := id) h))
    refine ⟨insert ℓ P, by simp [fresh, size], ?_⟩
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | mem
    · exact ⟨prime, odd, cop, by omega, pass⟩
    · exact good r mem

private theorem prime_sum_density_bound {ℓ n : ℕ} (hp : ℓ.Prime) (odd : ℓ ≠ 2)
    (hn : 0 < n) (lt : n < ℓ) :
    3 * Nat.card {s : ZMod ℓ // AdmissibleSum (n : ZMod ℓ) s} ≤ 2 * ℓ := by
  letI : Fact ℓ.Prime := ⟨hp⟩
  have unit : (n : ZMod ℓ) ≠ 0 := fun h =>
    (Nat.not_dvd_of_pos_of_lt hn lt) ((ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mp h)
  rw [card_admissibleSum_eq ℓ _ unit]
  have := hp.two_le
  by_cases sq : IsSquare (n : ZMod ℓ)
  · rw [card_factorSumResidues_of_square ℓ odd _ unit sq]
    omega
  · rw [card_factorSumResidues_of_nonsquare ℓ _ unit sq]
    omega

/-- The same modulus can have arbitrarily low full-period density and accept the
entire fixed search interval. The construction successively uses distinct odd
primes, with no restriction that these be the first primes. -/
theorem exists_sparse_modulus_passing_interval {n : ℕ} (hn : 0 < n)
    (upper threshold k : ℕ) :
    ∃ m : ℕ, threshold < m ∧ m.Coprime n ∧
      3 ^ k * Nat.card {s : ZMod m // AdmissibleSum (n : ZMod m) s} ≤ 2 ^ k * m ∧
      ∀ s ≤ upper, 4 * n ≤ s ^ 2 → AdmissibleSum (n : ZMod m) (s : ZMod m) := by
  induction k with
  | zero =>
    obtain ⟨ℓ, prime, odd, lt, large, pass⟩ := exists_prime_passing_interval n upper threshold
    have localBound := prime_sum_density_bound prime odd hn lt
    refine ⟨ℓ, large, Nat.coprime_of_lt_prime hn lt prime, ?_, pass⟩
    simp only [pow_zero, one_mul]
    omega
  | succ k ih =>
    obtain ⟨m, large, cop, sparse, passM⟩ := ih
    obtain ⟨ℓ, prime, odd, lt, fresh, passL⟩ := exists_prime_passing_interval n upper m
    have hM : 0 < m := by omega
    have disjoint := (Nat.coprime_of_lt_prime hM fresh prime).symm
    have keep := (Nat.coprime_of_lt_prime hn lt prime)
    have dens := prime_sum_density_bound prime odd hn lt
    refine ⟨m * ℓ, large.trans_le (Nat.le_mul_of_pos_right m prime.pos), Nat.coprime_mul_iff_left.mpr ⟨cop, keep⟩, ?_, ?_⟩
    · rw [card_admissibleSum_crt disjoint n]
      calc
        _ = (3 ^ k * Nat.card {s : ZMod m // AdmissibleSum (n : ZMod m) s}) *
          (3 * Nat.card {s : ZMod ℓ // AdmissibleSum (n : ZMod ℓ) s}) := by ring
        _ ≤ (2 ^ k * m) * (2 * ℓ) := Nat.mul_le_mul sparse dens
        _ = _ := by ring
    · intro s hs lower
      apply (admissibleSum_crt_iff disjoint _ _).mpr
      simpa only [map_natCast, Prod.fst_natCast, Prod.snd_natCast] using
        And.intro (passM s hs lower) (passL s hs lower)

/-- Even with arbitrarily small full-period density and period exceeding the
width, some choices of modulus force explicit additive tables to cover *all*
W offsets. This gives the exact square-root barrier in a worst choice of primes. -/
theorem exists_long_period_full_cover_obstruction {n L : ℕ} (hn : 0 < n)
    (lower : 4 * n ≤ L ^ 2) (W k : ℕ) :
    ∃ m > W, m.Coprime n ∧
      3 ^ k * Nat.card {s : ZMod m // AdmissibleSum (n : ZMod m) s} ≤ 2 ^ k * m ∧
      ∀ A B : Finset ℤ,
        (∀ j : Fin W, AdmissibleSum (n : ZMod m) ((L + j.val : ℕ) : ZMod m) →
          ∃ a ∈ A, ∃ b ∈ B, a + b = (j.val : ℤ)) → 4 * W ≤ (A.card + B.card) ^ 2 := by
  obtain ⟨m, big, cop, sparse, pass⟩ := exists_sparse_modulus_passing_interval hn (L + W) W k
  refine ⟨m, big, cop, sparse, ?_⟩
  intro A B covered
  have allCovered := periodic_additive_cover_size (M := 1) (by decide) (fun _ => True)
    L W A B (fun j _ => covered j (pass (L + j.val) (by have := j.isLt; omega)
      (lower.trans (Nat.pow_le_pow_left (Nat.le_add_right L j.val) 2))))
  have one : Nat.card {x : ZMod 1 // True} = 1 := by
    rw [Nat.card_eq_fintype_card]
    simp
  simpa [one] using allCovered

private theorem pass_of_root_table (ℓ n start stride k : ℕ) (hp : ℓ.Prime)
    (odd : ℓ ≠ 2) (roots : List ℕ)
    (check : ∀ i : Fin k, ((roots.getD i.val 0 : ℕ) : ZMod ℓ) ^ 2 =
      ((start + stride * i.val : ℕ) : ZMod ℓ) ^ 2 - 4 * (n : ZMod ℓ))
    (i : Fin k) : AdmissibleSum (n : ZMod ℓ) ((start + stride * i.val : ℕ) : ZMod ℓ) := by
  letI : Fact ℓ.Prime := ⟨hp⟩
  apply (admissibleSum_iff_isSquare odd _ _).mpr
  exact ⟨_, by rw [← pow_two]; exact (check i).symm⟩

set_option maxRecDepth 2500 in
/-- For 59·83 every integer in the balanced sum interval [140,148] passes all
three primes. Their combined period is 13,376,591. -/
theorem long_period_example_4897 (i : Fin 9) :
    let s := 140 + i.val
    AdmissibleSum (4897 : ZMod 97) (s : ZMod 97) ∧
      AdmissibleSum (4897 : ZMod 239) (s : ZMod 239) ∧
      AdmissibleSum (4897 : ZMod 577) (s : ZMod 577) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa only [one_mul] using pass_of_root_table 97 4897 140 1 9 (by decide) (by decide)
      [20, 14, 24, 45, 9, 46, 46, 9, 45] (by decide) i
  · simpa only [one_mul] using pass_of_root_table 239 4897 140 1 9 (by decide) (by decide)
      [27, 66, 24, 12, 108, 106, 85, 78, 72] (by decide) i
  · simpa only [one_mul] using pass_of_root_table 577 4897 140 1 9 (by decide) (by decide)
      [276, 51, 24, 70, 93, 74, 150, 38, 68] (by decide) i

set_option maxRecDepth 2500 in
/-- At 251·293 the three auxiliary primes are smaller than both factors.
Every candidate in the balanced interval consistent with the known sum modulo
four passes all three primes, including seven incorrect sums. -/
theorem long_period_example_73543 (i : Fin 8) :
    let s := 544 + 4 * i.val
    AdmissibleSum (73543 : ZMod 139) (s : ZMod 139) ∧
      AdmissibleSum (73543 : ZMod 211) (s : ZMod 211) ∧
      AdmissibleSum (73543 : ZMod 227) (s : ZMod 227) := by
  dsimp only
  exact ⟨pass_of_root_table 139 73543 544 4 8 (by decide) (by decide)
      [42, 4, 61, 62, 61, 4, 42, 25] (by decide) i,
    pass_of_root_table 211 73543 544 4 8 (by decide) (by decide)
      [42, 60, 68, 48, 4, 9, 38, 27] (by decide) i,
    pass_of_root_table 227 73543 544 4 8 (by decide) (by decide)
      [42, 50, 35, 45, 70, 61, 109, 18] (by decide) i⟩

end PrimeFactors
