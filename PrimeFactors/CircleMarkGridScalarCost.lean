import PrimeFactors.CircleMarkPublicDiskRate

/-! Uniform coverage of a fixed scalar menu at a single product. A subset
chosen from the public grid may depend on the product and its ordering. Every
eligible target is evaluated against the same subset. -/
namespace PrimeFactors.CircleMarkGridScalarCost

open Finset CircleMarkTargetFrequency CircleMarkRationalFrequency
open CircleMarkPublicGridRate RecognizingQuarticProducts

set_option exponentiation.threshold 2048

/-- Each fixed coordinate covers at most one square class at each prime. -/
theorem quarter {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (lo : 2^1023≤p) (order : p<q) (C : Finset ℕ) (budget : C.card≤2^1020) :
    rate (p*q) C < 1/4 := by
  have big := (by decide +kernel : 2<2^1023).trans_le lo
  obtain ⟨k,odd⟩ := hp.out.odd_of_ne_two big.ne'
  have even : (2:ℕ)^1023=2*2^1022 := by decide +kernel
  have width : (8:ℕ)*2^1020=2^1023 := by decide +kernel
  have pl : 8*(2:ℚ)^1020+1≤p := by exact_mod_cast (show 8*(2:ℕ)^1020+1≤p by omega)
  have ql : 8*(2:ℚ)^1020+1<q := pl.trans_lt (by exact_mod_cast order)
  have bound (r : ℕ) : ((covered r C).card:ℚ)≤2^1020 := by
    have u : (covered r C).card ≤ C.card := (card_le_card (erase_subset ..)).trans card_image_le
    exact_mod_cast u.trans budget
  have P : (0:ℚ)<p-1 := sub_pos.mpr (by exact_mod_cast hp.out.one_lt)
  have Q : (0:ℚ)<q-1 := sub_pos.mpr (by exact_mod_cast hp.out.one_lt.trans order)
  have a : (covered p C).card/((p:ℚ)-1) ≤ 1/8 :=
    (div_le_iff₀ P).mpr (by linarith only [bound p,pl])
  have b : (covered q C).card/((q:ℚ)-1) < 1/8 :=
    (div_lt_iff₀ Q).mpr (by linarith only [bound q,ql])
  rw [rate_eq order.ne big.ne' (big.trans order).ne']
  linarith only [a,b]

/-- The full menu is determined by the input product. -/
noncomputable abbrev publicMenu (n : ℕ) := menu n (fourthRoot n) (fourthRoot n)

/-- Targets detected by the full public grid that the fixed menu misses. -/
noncomputable def missed (n : ℕ) [NeZero n] (C : Finset ℕ) : Finset (ZMod n) :=
  hits n (publicMenu n) \ hits n C

/-- The missed targets exceed 13/20 of all eligible targets and 13/18 of
the targets detected by the full grid. C may be any fixed set of representatives. -/
theorem scalar_cost {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lo : 2^1023≤p) (order : p<q) (hi : q<2^1024)
    (C : Finset ℕ) (budget : C.card≤2^1020) :
    13/20 < ((missed (p*q) C).card:ℚ)/(targets (p*q)).card ∧
      13/18 < ((missed (p*q) C).card:ℚ)/(hits (p*q) (publicMenu (p*q))).card := by
  let T : ℚ := (targets (p*q)).card
  let F : ℚ := (hits (p*q) (publicMenu (p*q))).card
  let E : ℚ := (hits (p*q) C).card
  let D : ℚ := (missed (p*q) C).card
  have full : 9/10 < F/T := CircleMarkPublicDiskRate.nine_tenths lo order hi
  have early : E/T < 1/4 := quarter lo order C budget
  have tp : 0<T := by
    by_contra! h
    have z : T=0 := le_antisymm h (Nat.cast_nonneg _)
    norm_num [z] at full
  have f := (lt_div_iff₀ tp).mp full
  have e := (div_lt_iff₀ tp).mp early
  have fp : 0<F := by linarith only [tp,f]
  have pieces : F ≤ D+E := by
    have count : (hits (p*q) (publicMenu (p*q))).card ≤ (missed (p*q) C).card+(hits (p*q) C).card :=
      card_le_card_sdiff_add_card
    dsimp only [F,D,E]
    exact_mod_cast count
  change 13/20 < D/T ∧ 13/18 < D/F
  constructor
  · exact (lt_div_iff₀ tp).mpr (by linarith only [f,e,pieces])
  · exact (lt_div_iff₀ fp).mpr (by linarith only [f,e,pieces])

/-- Distinct standard representatives contributed by any selected cells. -/
noncomputable def representatives (n : ℕ) (S : Finset (ℕ×ℕ)) : Finset ℕ :=
  S.image fun z => ((z.1:ZMod n)*(z.2:ZMod n)⁻¹).val

/-- Applies to any fixed grid subset, including the distinct cells in a
prefix of a product-dependent ordering. Duplicate representatives cost no coverage. -/
theorem cell_cost {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lo : 2^1023≤p) (order : p<q) (hi : q<2^1024) {S : Finset (ℕ×ℕ)}
    (sub : S⊆rectangle (side p q) (side p q)) (budget : S.card≤2^1020) :
    representatives (p*q) S ⊆ publicMenu (p*q) ∧
      rate (p*q) (representatives (p*q) S) < 1/4 ∧
      13/20 < ((missed (p*q) (representatives (p*q) S)).card:ℚ)/(targets (p*q)).card ∧
      13/18 < ((missed (p*q) (representatives (p*q) S)).card:ℚ)/(hits (p*q) (publicMenu (p*q))).card := by
  have size : (representatives (p*q) S).card≤2^1020 := card_image_le.trans budget
  exact ⟨image_subset_image sub,quarter lo order _ size,scalar_cost lo order hi _ size⟩

end PrimeFactors.CircleMarkGridScalarCost
