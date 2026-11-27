import PrimeFactors.SampledSieve
import PrimeFactors.AffinePrimeSign
import Mathlib.Tactic

/-! Independent panels of finite, one-sided tests. The bounds count all ordered
draws with replacement. Membership assumes the candidate is already supplied. -/
namespace PrimeFactors.PrimeSignIsolation
open Finset

variable {α β : Type*}

/-- Uniform ordered panels of k independent draws from S. -/
noncomputable def panels (S : Finset β) (k : ℕ) : Finset (Fin k → β) :=
  Fintype.piFinset fun _ : Fin k => S

theorem panels_card (S : Finset β) (k : ℕ) : (panels S k).card=S.card^k := by
  simp only [panels,Fintype.card_piFinset_const,Fintype.card_fin]

/-- Return all supplied candidates which pass every coordinate. -/
noncomputable def surviving (C : Finset α) (keep : α → Finset β) {k : ℕ} (w : Fin k → β) :
    Finset α := by
  classical
  exact C.filter fun c => ∀ i, w i ∈ keep c

/-- A bad panel leaves at least one false candidate. -/
noncomputable def bad (falseCases : Finset α) (keep : α → Finset β) (k : ℕ) :
    Finset (Fin k → β) := by
  classical
  exact falseCases.biUnion fun c => panels (keep c) k

theorem mem_bad {C : Finset α} {keep : α → Finset β} {k : ℕ} {w : Fin k → β} :
    w∈bad C keep k ↔ ∃ c∈C, ∀ i, w i∈keep c := by
  classical
  simp only [bad,panels,mem_biUnion,Fintype.mem_piFinset]

/-- For a valid panel, the union bound counts exactly the failures to recover
the genuine candidate set, provided every true candidate passes every draw. -/
theorem exact_iff [DecidableEq α] {C T : Finset α} {S : Finset β} {keep : α → Finset β}
    {k : ℕ} {w : Fin k → β} (subset : T⊆C) (truePass : ∀ c∈T, S⊆keep c)
    (valid : w∈panels S k) :
    surviving C keep w=T ↔ w∉bad (C\T) keep k := by
  classical
  have hw := Fintype.mem_piFinset.mp valid
  constructor
  · intro out happens
    obtain ⟨c,hc,pass⟩ := mem_bad.mp happens
    have member : c∈surviving C keep w := mem_filter.mpr ⟨(mem_sdiff.mp hc).1,pass⟩
    exact (mem_sdiff.mp hc).2 (out ▸ member)
  · intro absent
    ext c
    constructor
    · intro hc
      obtain ⟨here,pass⟩ := mem_filter.mp hc
      by_contra no
      exact absent (mem_bad.mpr ⟨c,mem_sdiff.mpr ⟨here,no⟩,pass⟩)
    · intro hc
      exact mem_filter.mpr ⟨subset hc,fun i => truePass c hc (hw i)⟩

/-- The bad-panel union is an event inside the uniform draw space whenever
each single-coordinate passing set is contained in that space. -/
theorem bad_subset {C : Finset α} {keep : α → Finset β} {S : Finset β} (k : ℕ)
    (sub : ∀ c∈C, keep c⊆S) : bad C keep k ⊆ panels S k := by
  intro w hw
  obtain ⟨c,hc,pass⟩ := mem_bad.mp hw
  exact Fintype.mem_piFinset.mpr fun i => sub c hc (pass i)

/-- An integer form of the probability bound. No independence assumption on
the candidates is required; the independent coordinates form the product set. -/
theorem count (C : Finset α) (keep : α → Finset β) (N k : ℕ)
    (half : ∀ c∈C, 2*(keep c).card≤N) :
    2^k*(bad C keep k).card ≤ C.card*N^k := by
  classical
  have base := surviving_sample_count C keep (N/2) k (fun c hc => by
    have h := half c hc
    omega)
  change (bad C keep k).card ≤ C.card*(N/2)^k at base
  calc
    _ ≤ 2^k*(C.card*(N/2)^k) := Nat.mul_le_mul_left _ base
    _ = C.card*(2*(N/2))^k := by rw [mul_pow]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)

theorem chance_bound (C : Finset α) (keep : α → Finset β) {N : ℕ} (pos : 0<N) (k : ℕ)
    (half : ∀ c∈C, 2*(keep c).card≤N) :
    ((bad C keep k).card:ℚ)/(N:ℚ)^k ≤ (C.card:ℚ)/(2:ℚ)^k := by
  rw [div_le_div_iff₀ (by positivity) (by positivity),mul_comm ((bad C keep k).card:ℚ)]
  exact_mod_cast count C keep N k half

/-- k=bits+s independent tests lose at most one in 2^s panels whenever
there are at most 2^bits false candidates. -/
theorem bit_margin (C : Finset α) (keep : α → Finset β) {N bits : ℕ} (s : ℕ)
    (half : ∀ c∈C, 2*(keep c).card≤N) (size : C.card≤2^bits) :
    2^s*(bad C keep (bits+s)).card ≤ N^(bits+s) := by
  have bound := (count C keep N (bits+s) half).trans (Nat.mul_le_mul_right _ size)
  rw [pow_add,mul_assoc] at bound
  exact Nat.le_of_mul_le_mul_left bound (by positivity)

/-- The exact rational proportion uses the full draw space as denominator. -/
theorem chance (C : Finset α) (keep : α → Finset β) {N bits : ℕ} (pos : 0<N) (s : ℕ)
    (half : ∀ c∈C, 2*(keep c).card≤N) (size : C.card≤2^bits) :
    ((bad C keep (bits+s)).card : ℚ)/(N:ℚ)^(bits+s) ≤ 1/(2:ℚ)^s := by
  rw [div_le_div_iff₀ (by positivity) (by positivity),one_mul,mul_comm]
  exact_mod_cast bit_margin C keep s half size

/-- The possible odd smaller primes, using only the product and a strict
public upper bound of 2^bits. This finset is a mathematical search space. -/
noncomputable def candidates (N bits : ℕ) : Finset ℕ :=
  (range (2^bits)).filter fun ℓ => ℓ.Prime ∧ ℓ≠2 ∧ ℓ^2≤N

/-- Baseline set for stating exactly what successful isolation means. -/
noncomputable def genuine (N bits : ℕ) : Finset ℕ :=
  (candidates N bits).filter fun ℓ => ℓ∣N

theorem candidates_card (N bits : ℕ) : (candidates N bits).card≤2^bits :=
  (card_filter_le ..).trans_eq (card_range _)

theorem genuine_semiprime {p q bits : ℕ} (pp : p.Prime) (qp : q.Prime) (odd : p≠2)
    (order : p<q) (bounded : p<2^bits) : genuine (p*q) bits = {p} := by
  ext ℓ
  simp only [genuine,candidates,mem_filter,mem_range,mem_singleton]
  constructor
  · rintro ⟨⟨_,prime,_,fits⟩,div⟩
    rcases prime.dvd_mul.mp div with hp|hq
    · exact (Nat.prime_dvd_prime_iff_eq prime pp).mp hp
    · have eq := (Nat.prime_dvd_prime_iff_eq prime qp).mp hq
      rw [eq,pow_two] at fits
      exact False.elim (not_le_of_gt (Nat.mul_lt_mul_of_pos_right order qp.pos) fits)
  · intro same
    subst ℓ
    exact ⟨⟨bounded,pp,odd,by rw [pow_two]; exact Nat.mul_le_mul_left p order.le⟩,dvd_mul_right p q⟩

theorem false_conditions {N bits ℓ : ℕ} (hf : ℓ∈candidates N bits \ genuine N bits) :
    ℓ.Prime ∧ ℓ≠2 ∧ ¬ℓ∣N ∧ ℓ^2≤N := by
  obtain ⟨candidate,falseCase⟩ := mem_sdiff.mp hf
  obtain ⟨_,prime,odd,fit⟩ := mem_filter.mp candidate
  exact ⟨prime,odd,fun yes => falseCase (mem_filter.mpr ⟨candidate,yes⟩),fit⟩

/-- Failure event for the product-only affine signs on all eligible primes. -/
noncomputable def exceptional (N bits k : ℕ) : Finset (Fin k → ℕ) :=
  bad (candidates N bits \ genuine N bits) (AffinePrimeSign.seeds N) k

theorem exceptional_subset (N bits k : ℕ) : exceptional N bits k ⊆ panels (range N) k :=
  bad_subset k fun _ _ _ h => mem_range.mpr (AffinePrimeSign.mem_seeds.mp h).1

theorem affine_exact {N bits k : ℕ} {w : Fin k → ℕ} (valid : w∈panels (range N) k) :
    surviving (candidates N bits) (AffinePrimeSign.seeds N) w = genuine N bits ↔
      w∉exceptional N bits k := by
  apply exact_iff (filter_subset ..) _ valid
  intro ℓ hl r hr
  obtain ⟨eligible,div⟩ := mem_filter.mp hl
  obtain ⟨_,prime,_,_⟩ := mem_filter.mp eligible
  exact AffinePrimeSign.mem_seeds.mpr ⟨mem_range.mp hr,AffinePrimeSign.true_pass prime div r⟩

theorem affine_count (N bits s : ℕ) :
    2^s*(exceptional N bits (bits+s)).card ≤ N^(bits+s) := by
  apply bit_margin
  · intro ℓ h
    obtain ⟨prime,odd,miss,fit⟩ := false_conditions h
    exact AffinePrimeSign.false_bound prime odd miss fit
  · exact (card_le_card sdiff_subset).trans (candidates_card N bits)

/-- The exception fraction over all ordered public panels sampled with replacement. -/
theorem affine_fraction {N : ℕ} (positive : 0<N) (bits s : ℕ) :
    ((exceptional N bits (bits+s)).card:ℚ)/(N:ℚ)^(bits+s) ≤ 1/(2:ℚ)^s := by
  rw [div_le_div_iff₀ (by positivity) (by positivity),one_mul,mul_comm]
  exact_mod_cast affine_count N bits s

set_option exponentiation.threshold 2048 in
theorem full_size_1088 {N : ℕ} (positive : 0<N) :
    ((exceptional N 1024 1088).card:ℚ)/(N:ℚ)^1088 ≤ 1/(2:ℚ)^64 :=
  affine_fraction positive 1024 64

set_option exponentiation.threshold 2048 in
theorem full_size_1100 {N : ℕ} (positive : 0<N) :
    ((exceptional N 1024 1100).card:ℚ)/(N:ℚ)^1100 ≤ 1/(2:ℚ)^76 :=
  affine_fraction positive 1024 76

/-- With any strictly positive safety margin, some public panel isolates the
true set. This existence statement does not enumerate its surviving candidates. -/
theorem exists_isolating {N bits s : ℕ} (pos : 0<N) (margin : 0<s) :
    ∃ w∈panels (range N) (bits+s),
      surviving (candidates N bits) (AffinePrimeSign.seeds N) w = genuine N bits := by
  have upper := affine_count N bits s
  have two : 2≤(2:ℕ)^s := by simpa using (Nat.pow_le_pow_right (by decide : 0<2) margin)
  have doubled := (Nat.mul_le_mul_right _ two).trans upper
  have allPositive : 0<N^(bits+s) := pow_pos pos _
  have less : (exceptional N bits (bits+s)).card < (panels (range N) (bits+s)).card := by
    rw [panels_card,card_range]
    omega
  obtain ⟨w,valid,good⟩ := exists_mem_not_mem_of_card_lt_card less
  exact ⟨w,valid,(affine_exact valid).mpr good⟩

/-- On a semiprime with bounded smaller factor, every nonexceptional panel recognizes just its
smaller prime among all the admissible candidates. -/
theorem recognize_smaller {p q bits k : ℕ} (pp : p.Prime) (qp : q.Prime) (odd : p≠2)
    (order : p<q) (bounded : p<2^bits) {w : Fin k → ℕ}
    (valid : w∈panels (range (p*q)) k) (good : w∉exceptional (p*q) bits k) :
    surviving (candidates (p*q) bits) (AffinePrimeSign.seeds (p*q)) w = {p} :=
  ((affine_exact valid).mpr good).trans (genuine_semiprime pp qp odd order bounded)

end PrimeFactors.PrimeSignIsolation
