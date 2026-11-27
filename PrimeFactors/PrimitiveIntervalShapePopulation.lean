import PrimeFactors.PrimitiveIntervalShape
import PrimeFactors.FixedRatioSumPopulation

/-! Finite prevalence bounds for fixed multiples of the product as estimates
of the signed interval aggregate. A fixed menu may choose any entry per input. -/
namespace PrimeFactors.PrimitiveIntervalShapePopulation

open Finset MixedPrefixSample PrimitiveIntervalMoment PrimitiveIntervalShape
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
attribute [local irreducible] X primes eligible ordered

noncomputable def successes (c : ℝ) : Finset (ℕ×ℕ) := by
  classical exact eligible.filter fun z => hit c z.1 z.2

noncomputable def menu (C : Finset ℝ) : Finset (ℕ×ℕ) := C.biUnion successes

private theorem facts {p q : ℕ} (ok : (p,q)∈eligible) :
    0<p ∧ p<q ∧ q<2*p ∧ 2^2047≤p*q := by
  rw [eligible,sample,mem_filter] at ok
  obtain ⟨pm,qm,_,full,_⟩ := mem_ordered.mp ok.1
  rw [primes,mem_filter,mem_Ico] at pm qm
  have lower : X≤p := pm.1.1
  have upper : q<2*X := qm.1.2
  have size : 2*X^2=2^2047 := by unfold X; decide +kernel
  exact ⟨pm.2.pos,ok.2,by omega,size ▸ full⟩

theorem mem_menu {p q : ℕ} {C : Finset ℝ} : (p,q)∈menu C ↔
    (p,q)∈eligible ∧ ∃ c∈C, hit c p q := by
  classical
  constructor
  · intro h
    obtain ⟨c,hc,hp⟩ := mem_biUnion.mp h
    obtain ⟨ok,good⟩ := mem_filter.mp hp
    exact ⟨ok,c,hc,good⟩
  · rintro ⟨ok,c,hc,good⟩
    exact mem_biUnion.mpr ⟨c,hc,mem_filter.mpr ⟨ok,good⟩⟩

/-- Each real coefficient fixed independently of the input has success
fraction strictly below 2^(-482), at aggregate error 4B. -/
theorem frequency (c : ℝ) : 2^482*(successes c).card < eligible.card := by
  classical
  obtain ⟨r,hr,shape⟩ := exists_ratio c
  have sub : successes c ⊆ FixedRatioSumPopulation.fits r 8 := by
    rintro ⟨p,q⟩ h
    obtain ⟨ok,good⟩ := mem_filter.mp h
    obtain ⟨pos,ord,bal,_⟩ := facts ok
    exact FixedRatioSumPopulation.mem_fits.mpr ⟨ok,shape pos ord bal good⟩
  exact (Nat.mul_le_mul_left _ (card_le_card sub)).trans_lt (FixedRatioSumPopulation.frequency hr)

/-- For any fixed nonempty coefficient menu the sum of the individual
bounds controls its union, without assumptions on which entry gets selected. -/
theorem menu_frequency {C : Finset ℝ} (ne : C.Nonempty) :
    2^482*(menu C).card < C.card*eligible.card := by
  classical
  calc
    _ ≤ 2^482*∑ c∈C, (successes c).card := Nat.mul_le_mul_left _ card_biUnion_le
    _ = ∑ c∈C, 2^482*(successes c).card := mul_sum ..
    _ < ∑ _c∈C, eligible.card := sum_lt_sum_of_nonempty ne fun c _ => frequency c
    _ = _ := by simp

/-- A menu with at most 2^64 fixed entries, including the empty menu. -/
theorem menu_64 {C : Finset ℝ} (size : C.card≤2^64) : 2^418*(menu C).card < eligible.card := by
  classical
  by_cases ne : C.Nonempty
  · have sum := (menu_frequency ne).trans_le (Nat.mul_le_mul_right _ size)
    apply Nat.lt_of_mul_lt_mul_left (a:=2^64)
    rwa [←Nat.mul_assoc,←pow_add]
  · have empty := not_nonempty_iff_eq_empty.mp ne
    rw [empty,menu]
    simpa using (Nat.zero_le _).trans_lt (frequency 0)

noncomputable def coarse (c : ℝ) : Finset (ℕ×ℕ) := by
  classical exact eligible.filter fun z => |(reading z.1 z.2:ℝ)-c*((z.1:ℝ)*z.2)|≤(2:ℝ)^1450

/-- Even absolute aggregate error 2^1450 gives fraction below 2^(-269)
for one fixed real coefficient. -/
theorem coarse_frequency (c : ℝ) : 2^269*(coarse c).card < eligible.card := by
  obtain ⟨r,hr,shape⟩ := exists_ratio_budget c
  have sub : coarse c ⊆ FixedRatioSumPopulation.fits r (2^428) := by
    rintro ⟨p,q⟩ h
    obtain ⟨ok,good⟩ := mem_filter.mp h
    obtain ⟨pos,ord,bal,full⟩ := facts ok
    have width : (2:ℝ)^1023 ≤ (cutoff (p*q):ℝ) := by exact_mod_cast full_width_cutoff full
    have budget : (2:ℝ)^1450 ≤ 2^427*(cutoff (p*q):ℝ) := calc
      _ = (2:ℝ)^427*2^1023 := by rw [←pow_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left width (by positivity)
    have read : |(reading p q:ℝ)-c*((p:ℝ)*q)|≤(2:ℝ)^1450 := good
    have sum := shape pos ord bal (by positivity : (0:ℝ)≤2^427) (read.trans budget)
    have correction : (2:ℝ)^427+4 ≤ 2^428 := by norm_num
    exact FixedRatioSumPopulation.mem_fits.mpr ⟨ok,sum.trans correction⟩
  exact (Nat.mul_le_mul_left _ (card_le_card sub)).trans_lt (FixedRatioSumPopulation.coarse_fraction hr)

end PrimeFactors.PrimitiveIntervalShapePopulation
