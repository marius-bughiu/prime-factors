import PrimeFactors.FactorSum

namespace PrimeFactors

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- For nonzero `n`, the sums of all pairs of residues with product `n`. -/
noncomputable def factorSumResidues (n : ZMod ℓ) : Finset (ZMod ℓ) :=
  (Finset.univ.erase 0).image fun x => x + n / x

/-- Nonzero square roots of the product. For nonzero `n` this includes every square root. -/
noncomputable def squareRootsMod (n : ZMod ℓ) : Finset (ZMod ℓ) :=
  (Finset.univ.erase 0).filter fun x => x ^ 2 = n

theorem mem_factorSumResidues_iff {n s : ZMod ℓ} (hn : n ≠ 0) :
    s ∈ factorSumResidues ℓ n ↔ AdmissibleSum n s := by
  constructor
  · rintro hs
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨x, n / x, mul_div_cancel₀ n (Finset.mem_erase.mp hx).1, rfl⟩
  · rintro ⟨x, y, prod, rfl⟩
    have hx : x ≠ 0 := fun h => hn (by rw [← prod, h, zero_mul])
    refine Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩, ?_⟩
    rw [← prod, mul_div_cancel_left₀ _ hx]

theorem card_admissibleSum_eq (n : ZMod ℓ) (hn : n ≠ 0) :
    Nat.card {s : ZMod ℓ // AdmissibleSum n s} = (factorSumResidues ℓ n).card := by
  let e := Equiv.subtypeEquivRight fun s => (mem_factorSumResidues_iff ℓ (s := s) hn).symm
  exact (Nat.card_congr e).trans (by rw [Nat.card_eq_fintype_card, Fintype.card_coe])

/-- The full fiber of a nonzero trace input consists of that input and its complementary factor. -/
theorem factorSum_fiber {n x : ZMod ℓ} (hn : n ≠ 0) (hx : x ≠ 0) :
    (Finset.univ.erase 0).filter (fun z => z + n / z = x + n / x) = {x, n / x} := by
  let y := n / x
  have hy : y ≠ 0 := div_ne_zero hn hx
  have prod : x * y = n := mul_div_cancel₀ n hx
  have swap : n / y = x := (div_eq_iff hy).mpr prod.symm
  ext z
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_insert, Finset.mem_singleton]
  change (z ≠ 0 ∧ z + n / z = x + y) ↔ z = x ∨ z = y
  constructor
  · rintro ⟨hz, hs⟩
    have roots : (z - x) * (z - y) = 0 := calc
      _ = z * (z + n / z - (x + y)) + (x * y - z * (n / z)) := by ring
      _ = 0 := by rw [hs, prod, mul_div_cancel₀ n hz]; ring
    simpa only [sub_eq_zero] using mul_eq_zero.mp roots
  · rintro (rfl | rfl)
    · exact ⟨hx, rfl⟩
    · exact ⟨hy, by rw [swap, add_comm]⟩

/-- A two-element fiber contributes twice to the count of inputs. A singleton
fiber contributes once as an input and once as a square root. -/
theorem two_mul_card_factorSumResidues (n : ZMod ℓ) (hn : n ≠ 0) :
    2 * (factorSumResidues ℓ n).card = ℓ - 1 + (squareRootsMod ℓ n).card := by
  let domain : Finset (ZMod ℓ) := Finset.univ.erase 0
  let f := fun x : ZMod ℓ => x + n / x
  let sums := factorSumResidues ℓ n
  let roots := squareRootsMod ℓ n
  have maps : Set.MapsTo f domain sums := fun x hx => Finset.mem_image_of_mem f hx
  have rootsMap : Set.MapsTo f roots sums :=
    fun x hx => maps (Finset.mem_filter.mp hx).1
  have hdom : domain.card = ℓ - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod ℓ)), Finset.card_univ, ZMod.card]
  change 2 * sums.card = ℓ - 1 + roots.card
  rw [← hdom, Finset.card_eq_sum_card_fiberwise maps,
    Finset.card_eq_sum_card_fiberwise rootsMap, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _s ∈ sums, 2 := by simp [Nat.mul_comm]
    _ = _ := Finset.sum_congr rfl fun s hs => by
      obtain ⟨x, hxmem, rfl⟩ := Finset.mem_image.mp hs
      have hx : x ≠ 0 := (Finset.mem_erase.mp hxmem).1
      let y := n / x
      have hy : y ≠ 0 := div_ne_zero hn hx
      have prod : x * y = n := mul_div_cancel₀ n hx
      have fiber : domain.filter (fun z => f z = f x) = {x, y} := factorSum_fiber ℓ hn hx
      have rootFiber : roots.filter (fun z => f z = f x) =
          ({x, y} : Finset _).filter (fun z => z ^ 2 = n) := by
        rw [← fiber]
        ext z
        simp [roots, squareRootsMod, domain, and_comm, and_left_comm]
      change 2 = (domain.filter fun z => f z = f x).card +
        (roots.filter fun z => f z = f x).card
      rw [fiber, rootFiber]
      have sx : x ^ 2 = n ↔ x = y := by rw [← prod, pow_two, mul_right_inj' hx]
      have sy : y ^ 2 = n ↔ x = y := by
        rw [← prod, pow_two, mul_left_inj' hy, eq_comm]
      by_cases same : x = y
      · simp [← same, sx.mpr same, Finset.filter_singleton]
      · simp [Finset.filter_insert, Finset.filter_singleton, Finset.card_pair same, sx, sy, same]

/-- A nonzero square modulo an odd prime has two distinct square roots. -/
theorem card_squareRootsMod_of_square (hodd : ℓ ≠ 2) (n : ZMod ℓ) (hn : n ≠ 0)
    (hs : IsSquare n) : (squareRootsMod ℓ n).card = 2 := by
  obtain ⟨x, rfl⟩ := hs
  have hx : x ≠ 0 := fun h => hn (by simp [h])
  have htwo : (2 : ZMod ℓ) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have distinct : x ≠ -x := by
    intro h
    apply mul_ne_zero htwo hx
    rw [two_mul, ← eq_neg_iff_add_eq_zero]
    exact h
  have e : squareRootsMod ℓ (x * x) = {x, -x} := by
    ext z
    simp only [squareRootsMod, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
      ← pow_two, sq_eq_sq_iff_eq_or_eq_neg, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨And.right, fun h => ⟨?_, h⟩⟩
    rcases h with rfl | rfl
    · exact hx
    · exact neg_ne_zero.mpr hx
  rw [e, Finset.card_pair distinct]

theorem card_squareRootsMod_of_nonsquare (n : ZMod ℓ) (hs : ¬ IsSquare n) :
    (squareRootsMod ℓ n).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  exact hs ⟨x, by simpa [pow_two] using (Finset.mem_filter.mp hx).2.symm⟩

theorem card_factorSumResidues_of_square (hodd : ℓ ≠ 2) (n : ZMod ℓ) (hn : n ≠ 0)
    (hs : IsSquare n) : (factorSumResidues ℓ n).card = (ℓ + 1) / 2 := by
  have count := two_mul_card_factorSumResidues ℓ n hn
  rw [card_squareRootsMod_of_square ℓ hodd n hn hs] at count
  have := (Fact.out : ℓ.Prime).two_le
  omega

theorem card_factorSumResidues_of_nonsquare (n : ZMod ℓ) (hn : n ≠ 0) (hs : ¬ IsSquare n) :
    (factorSumResidues ℓ n).card = (ℓ - 1) / 2 := by
  have count := two_mul_card_factorSumResidues ℓ n hn
  rw [card_squareRootsMod_of_nonsquare ℓ n hs] at count
  omega

end PrimeFactors
