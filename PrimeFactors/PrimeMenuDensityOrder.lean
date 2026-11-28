import PrimeFactors.EarlyPersistentMidpoints

/-! Comparing a finite prime menu with an initial segment of primes. Cancel the
common primes. Every omitted prime is at most the cutoff and every added prime
is larger. Products of the common factors need never be evaluated. -/
namespace PrimeFactors.PrimeMenuDensityOrder

open Finset

noncomputable def core (b : ℕ) : Finset ℕ :=
  (PersistentLocalSurvivors.smallPrimes b).filter (5 ≤ ·)

noncomputable def density (p : ℕ) : ℚ := ((p : ℚ)-3)/(2*p)

theorem mem_core {p b : ℕ} : p ∈ core b ↔ p.Prime ∧ 5 ≤ p ∧ p ≤ b := by
  simp only [core,PersistentLocalSurvivors.smallPrimes,mem_filter,mem_range]
  constructor
  · rintro ⟨⟨small,prime⟩,low⟩
    exact ⟨prime,low,by omega⟩
  · rintro ⟨prime,low,small⟩
    exact ⟨⟨by omega,prime⟩,low⟩

theorem core_card : (core 643).card = 115 := by
  let C := PersistentLocalSurvivors.smallPrimes 643
  have eq : core 643 = (C.erase 2).erase 3 := by
    ext p
    simp only [core,mem_filter,mem_erase,C]
    constructor
    · rintro ⟨hp,low⟩
      exact ⟨by omega,by omega,hp⟩
    · rintro ⟨three,two,hp⟩
      have prime := (mem_filter.mp hp).2
      have lb := prime.two_le
      have four : p ≠ 4 := fun e => (by decide : ¬Nat.Prime 4) (e ▸ prime)
      exact ⟨hp,by omega⟩
  have two : 2 ∈ C := by
    exact mem_filter.mpr ⟨mem_range.mpr (by decide),Nat.prime_two⟩
  have three : 3 ∈ C.erase 2 := mem_erase.mpr ⟨by decide,
    mem_filter.mpr ⟨mem_range.mpr (by decide),Nat.prime_three⟩⟩
  rw [eq,card_erase_of_mem three,card_erase_of_mem two]
  change (PersistentLocalSurvivors.smallPrimes 643).card - 1 - 1 = 115
  rw [EarlyPersistentMidpoints.prime_count]

private theorem split_product {R : Type*} [CommMonoid R] (C S : Finset ℕ) (f : ℕ → R) :
    (∏ p ∈ C \ S, f p) * (∏ p ∈ C ∩ S, f p) = ∏ p ∈ C, f p := by
  simpa only [sdiff_inter_self_left] using
    (prod_sdiff (f:=f) (inter_subset_left : C ∩ S ⊆ C))

private theorem counts (C S : Finset ℕ) :
    (C \ S).card + (C ∩ S).card = C.card ∧ (S \ C).card + (C ∩ S).card = S.card :=
  ⟨card_sdiff_add_card_inter C S,by simpa only [inter_comm S C] using card_sdiff_add_card_inter S C⟩

/-- A surplus prime costs at least one extra factor of the separating threshold. -/
theorem budget_card {C S : Finset ℕ} {b : ℕ} (pos : 0 < b)
    (omitted : ∀ p ∈ C \ S, p ≤ b) (added : ∀ p ∈ S \ C, b ≤ p)
    (budget : (∏ p ∈ S, p) < b * ∏ p ∈ C, p) : S.card ≤ C.card := by
  by_contra! surplus
  obtain ⟨a,c⟩ := counts C S
  have extra : (C \ S).card + 1 ≤ (S \ C).card := by omega
  have small : (∏ p ∈ C \ S,p) ≤ b ^ (C \ S).card := by
    simpa only [prod_const] using prod_le_prod (fun p (_ : p ∈ C \ S) => Nat.zero_le p) omitted
  have big : b ^ (S \ C).card ≤ ∏ p ∈ S \ C,p := by
    simpa only [prod_const] using prod_le_prod (fun _ (_ : _ ∈ S \ C) => Nat.zero_le b) added
  have bound : b * (∏ p ∈ C \ S,p) ≤ ∏ p ∈ S \ C,p := calc
    _ ≤ b * b ^ (C \ S).card := Nat.mul_le_mul_left _ small
    _ = b ^ ((C \ S).card+1) := (pow_succ' _ _).symm
    _ ≤ _ := (Nat.pow_le_pow_right pos extra).trans big
  rw [← split_product S C (fun p => p),← split_product C S (fun p => p), inter_comm S C, ← mul_assoc] at budget
  exact (not_lt_of_ge (Nat.mul_le_mul_right _ bound)) budget

theorem density_mono {a b : ℕ} (pos : 0<a) (h : a≤b) : density a≤density b := by
  have hp : (0:ℚ)<a := by exact_mod_cast pos
  have hq : (a:ℚ)≤b := by exact_mod_cast h
  unfold density
  apply (div_le_div_iff₀ (by positivity) (by have := hp.trans_le hq; positivity)).mpr
  nlinarith

private theorem density_nonneg {p : ℕ} (hp : 5≤p) : 0≤density p := by
  have h : (5:ℚ)≤p := by exact_mod_cast hp
  exact div_nonneg (by linarith) (by positivity)

private theorem two_density_le {p : ℕ} (hp : 5≤p) : 2*density p≤1 := by
  have h : (5:ℚ)≤p := by exact_mod_cast hp
  unfold density
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

/-- Omitting at least k more primes than are added gains at least 2^k in
the product of the guaranteed local densities. -/
theorem density_of_card_gap {C S : Finset ℕ} {b k : ℕ}
    (sep : 5≤b) (valid : ∀ p ∈ C, 5≤p) (omitted : ∀ p ∈ C \ S, p ≤ b)
    (added : ∀ p ∈ S \ C, b ≤ p) (gap : S.card+k≤C.card) :
    (2:ℚ)^k * (∏ p ∈ C,density p) ≤ ∏ p ∈ S,density p := by
  let d := density b
  have d0 : 0≤d := density_nonneg sep
  have d2 : 2*d≤1 := two_density_le sep
  have d1 : d≤1 := by linarith
  obtain ⟨a,c⟩ := counts C S
  have diff : (S \ C).card+k≤(C \ S).card := by omega
  have small : (∏ p ∈ C \ S,density p) ≤ d^(C \ S).card := by
    simpa only [prod_const] using prod_le_prod
      (fun p hp => density_nonneg (valid p (mem_sdiff.mp hp).1))
      (fun p hp => density_mono (by have := valid p (mem_sdiff.mp hp).1; omega) (omitted p hp))
  have big : d^(S \ C).card ≤ ∏ p ∈ S \ C,density p := by
    simpa only [prod_const] using prod_le_prod (fun _ (_ : _ ∈ S \ C) => d0)
      (fun p hp => density_mono (by omega) (added p hp))
  have power : (2*d)^k≤1 := by simpa only [one_pow] using
      (pow_le_pow_left₀ (by positivity : 0≤2*d) d2 k)
  have bound : (2:ℚ)^k * (∏ p ∈ C \ S,density p) ≤ ∏ p ∈ S \ C,density p := calc
    _ ≤ 2^k * d^((S \ C).card+k) := mul_le_mul_of_nonneg_left
      (small.trans (pow_le_pow_of_le_one d0 d1 diff)) (by positivity)
    _ = d^(S \ C).card * (2*d)^k := by rw [pow_add,mul_pow]; ring
    _ ≤ d^(S \ C).card * 1 := mul_le_mul_of_nonneg_left power (pow_nonneg d0 _)
    _ ≤ _ := by simpa only [mul_one] using big
  rw [← split_product C S density,← split_product S C density,inter_comm S C,← mul_assoc]
  exact mul_le_mul_of_nonneg_right bound
    (prod_nonneg (fun p hp => density_nonneg (valid p (mem_inter.mp hp).1)))

/-- With equally many members, any monotone nonnegative integral weight gives
the smaller product on the initial segment. -/
theorem raw_of_same {C S : Finset ℕ} {b : ℕ} (f : ℕ → ℕ) (mono : Monotone f)
    (omitted : ∀ p ∈ C \ S, p ≤ b) (added : ∀ p ∈ S \ C, b ≤ p)
    (size : S.card=C.card) : (∏ p ∈ C, f p) ≤ ∏ p ∈ S, f p := by
  obtain ⟨a,c⟩ := counts C S
  have eq : (C \ S).card=(S \ C).card := by omega
  have small : (∏ p ∈ C \ S,f p) ≤ (f b)^(C \ S).card := by
    simpa only [prod_const] using prod_le_prod (fun p (_ : p ∈ C \ S) => Nat.zero_le (f p))
      (fun p hp => mono (omitted p hp))
  have big : (f b)^(S \ C).card ≤ ∏ p ∈ S \ C,f p := by
    simpa only [prod_const] using prod_le_prod (fun _ (_ : _ ∈ S \ C) => Nat.zero_le (f b))
      (fun p hp => mono (added p hp))
  rw [eq] at small
  rw [← split_product S C f,← split_product C S f, inter_comm S C]
  exact Nat.mul_le_mul_right _ (small.trans big)

private theorem sides (S : Finset ℕ) (valid : ∀ p ∈ S, p.Prime ∧ 5≤p) :
    (∀ p ∈ core 643 \ S, p≤647) ∧ (∀ p ∈ S \ core 643, 647≤p) := by
  constructor
  · intro p hp
    have := (mem_core.mp (mem_sdiff.mp hp).1).2.2
    omega
  · intro p hp
    obtain ⟨hS,hC⟩ := mem_sdiff.mp hp
    obtain ⟨prime,low⟩ := valid p hS
    have gt : 643<p := by simpa [mem_core,prime,low] using hC
    by_contra! bad
    interval_cases p <;> norm_num at prime

theorem order643 (S : Finset ℕ) (valid : ∀ p ∈ S, p.Prime ∧ 5≤p)
    (budget : (∏ p ∈ S,p) < 647 * ∏ p ∈ core 643,p) :
    S.card≤115 ∧ (∏ p ∈ core 643,density p) ≤ ∏ p ∈ S,density p := by
  obtain ⟨missing,outside⟩ := sides S valid
  have card := budget_card (by decide) missing outside budget
  refine ⟨card.trans core_card.le,?_⟩
  simpa only [pow_zero,one_mul] using density_of_card_gap (b:=647) (k:=0) (by decide)
    (fun _ h => (mem_core.mp h).2.1) missing outside (by simpa only [Nat.add_zero] using card)

theorem lanes_of_same (S : Finset ℕ) (valid : ∀ p ∈ S, p.Prime ∧ 5≤p)
    (size : S.card=115) : (∏ p ∈ core 643,(p-3)/2) ≤ ∏ p ∈ S,(p-3)/2 := by
  obtain ⟨missing,outside⟩ := sides S valid
  exact raw_of_same _ (fun _ _ le => Nat.div_le_div_right (Nat.sub_le_sub_right le _))
    missing outside (size.trans core_card.symm)

theorem double_density_of_fewer (S : Finset ℕ) (valid : ∀ p ∈ S, p.Prime ∧ 5≤p)
    (fewer : S.card<115) : 2*(∏ p ∈ core 643,density p) ≤ ∏ p ∈ S,density p := by
  obtain ⟨missing,outside⟩ := sides S valid
  simpa only [pow_one] using density_of_card_gap (k:=1) (by decide)
    (fun _ h => (mem_core.mp h).2.1) missing outside (by rw [core_card]; omega)

end PrimeFactors.PrimeMenuDensityOrder
