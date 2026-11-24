import PrimeFactors.RandomRelationSigns
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace PrimeFactors.SharedRootSigns

abbrev F := ZMod 2

/-- Write the reduced convergent candidate as k/a. The reconstruction
equation ar-kN=b and its strict height bound are precisely strong enough
for Legendre's theorem, including when r/N is rational. -/
theorem short_fraction_convergent {N r : ℕ} (positive : 0<N) {u : ℚ} {b : ℤ}
    (represented : (u.den : ℤ)*r-u.num*N=b)
    (short : 2*(u.den : ℤ)*|b|<N) :
    ∃ i, u = ((r : ℝ)/N).convergent i := by
  have npos : 0<(N : ℝ) := by exact_mod_cast positive
  have apos : 0<(u.den : ℝ) := by exact_mod_cast u.den_pos
  have value : (u : ℝ)*u.den = u.num := by rw [Rat.cast_def, div_mul_cancel₀ _ apos.ne']
  have diff : ((r : ℝ)/N-u)*((N : ℝ)*u.den)=(b : ℝ) := by
    calc
      _ = (u.den : ℝ)*((r : ℝ)/N*N)-((u : ℝ)*u.den)*N := by ring
      _ = _ := by rw [div_mul_cancel₀ _ npos.ne', value]; exact_mod_cast represented
  have absolute := congrArg abs diff
  rw [abs_mul, abs_of_pos (mul_pos npos apos)] at absolute
  apply Real.exists_rat_eq_convergent
  apply (lt_div_iff₀ (by positivity)).mpr
  apply (mul_lt_mul_iff_of_pos_right npos).mp
  rw [one_mul]
  calc
    _ = 2*(u.den : ℝ)*(|(r : ℝ)/N-u| * ((N : ℝ)*u.den)) := by ring
    _ < _ := by rw [absolute]; exact_mod_cast short

/-- Add the selection bits of all rows produced by each original draw. The
restriction of this linear map to square dependencies is the source map. -/
noncomputable def sourceParities {ι σ : Type*} [Fintype ι] [DecidableEq σ] (source : ι → σ) :
    (ι → F) →ₗ[F] (σ → F) where
  toFun v j := ∑ i ∈ Finset.univ.filter (fun i => source i = j), v i
  map_add' v w := by ext j; simp [Finset.sum_add_distrib]
  map_smul' c v := by ext j; simp [Finset.mul_sum, smul_eq_mul]

/-- If every draw is used an even number of times, the product of row roots
can be computed from the observed squares without selecting any hidden roots. -/
theorem even_source_product {ι σ G : Type*} [Fintype σ] [DecidableEq σ] [CommMonoid G]
    (s : Finset ι) (source : ι → σ) (a : ι → G) (x : σ → G) (k : σ → ℕ)
    (counts : ∀ j, (s.filter (fun i => source i = j)).card = 2*k j) :
    (∏ i ∈ s, a i*x (source i)) = (∏ i ∈ s, a i) * ∏ j, (x j^2)^(k j) := by
  rw [Finset.prod_mul_distrib, ← Finset.prod_fiberwise' s source x]
  simp only [Finset.prod_const, counts, pow_mul]

/-- Every prime of odd valuation in one selected norm must divide some other
selected norm. When this row is its source's only contribution, the witness
necessarily belongs to a different draw. -/
theorem odd_prime_requires_other_row {ι : Type*} (others : Finset ι) (norm : ι → ℕ)
    {v p : ℕ} (prime : p.Prime) (nonzero : v≠0) (rest : ∀ i ∈ others, norm i ≠ 0)
    (odd : Odd (v.factorization p)) (square : IsSquare (v * ∏ i ∈ others, norm i)) :
    ∃ i ∈ others, p ∣ norm i := by
  apply (prime.prime.dvd_finset_prod_iff norm).mp
  by_contra absent
  obtain ⟨k, hk⟩ := odd
  obtain ⟨s, hs⟩ := (isSquare_iff_exists_sq _).mp square
  have eq := congrArg (fun n : ℕ => n.factorization p) hs
  simp only [Nat.factorization_mul nonzero (Finset.prod_ne_zero_iff.mpr rest),
    Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
    Nat.factorization_eq_zero_of_not_dvd absent, add_zero] at eq
  omega

/-- Count a covered set of transcripts by the sum of each source's upper
bound. One transcript can have several witness sources. -/
theorem source_union_bound {ω σ : Type*} [DecidableEq ω] (transcripts : Finset ω)
    (sources : Finset σ) (event : σ → Finset ω) (bound : σ → ℕ)
    (cover : ∀ t ∈ transcripts, ∃ s ∈ sources, t ∈ event s)
    (perSource : ∀ s ∈ sources, (event s).card ≤ bound s) :
    transcripts.card ≤ ∑ s ∈ sources, bound s :=
  (Finset.card_le_card (fun t ht => Finset.mem_biUnion.mpr (cover t ht))).trans
    (Finset.card_biUnion_le.trans (Finset.sum_le_sum perSource))

variable {D V : Type*} [AddCommGroup D] [Module F D] [AddCommGroup V] [Module F V]

/-- A target split pattern is attainable exactly when it agrees with the
reference pattern on dependencies with zero source parity. -/
theorem reachable (P : D →ₗ[F] V) (reference target : Module.Dual F D) :
    (∃ h : Module.Dual F V, P.dualMap h + reference = target) ↔
      target-reference ∈ (LinearMap.ker P).dualAnnihilator := by
  rw [← P.range_dualMap_eq_dualAnnihilator_ker]
  change _ ↔ ∃ h, P.dualMap h = target-reference
  exact exists_congr fun _ => eq_sub_iff_add_eq.symm

open Classical in
/-- Counting equally likely source disagreement vectors, every attainable
pattern has 2^(m-rank P) preimages and every other pattern has none. -/
theorem outcome_count [FiniteDimensional F V] (P : D →ₗ[F] V)
    (reference target : Module.Dual F D) :
    Nat.card {h : Module.Dual F V // P.dualMap h + reference = target} =
      if target-reference ∈ (LinearMap.ker P).dualAnnihilator then
        2^(Module.finrank F V - Module.finrank F (LinearMap.range P)) else 0 := by
  classical
  split_ifs with h
  · obtain ⟨u, hu⟩ := (reachable P reference target).mpr h
    have shift : P.dualMap u = target-reference := eq_sub_iff_add_eq.mpr hu
    let e : {h : Module.Dual F V // P.dualMap h + reference = target} ≃
        LinearMap.ker P.dualMap := {
      toFun := fun v => ⟨v.val-u, by
        change P.dualMap _ = 0
        rw [map_sub, shift, eq_sub_iff_add_eq.mpr v.property, sub_self]⟩
      invFun := fun k => ⟨k.val+u, by
        rw [map_add, (show P.dualMap k.val = 0 from k.property), zero_add, hu]⟩
      left_inv := fun _ => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun _ => Subtype.ext (add_sub_cancel_right _ _) }
    rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := F),
      Nat.card_eq_fintype_card, ZMod.card]
    congr 1
    have dims := P.dualMap.finrank_range_add_finrank_ker
    rw [P.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq] at dims
    omega
  · haveI : IsEmpty {h : Module.Dual F V // P.dualMap h + reference = target} :=
      ⟨fun v => h ((reachable P reference target).mp ⟨v.val, v.property⟩)⟩
    exact Nat.card_of_isEmpty

open Classical in
/-- The exact all-failure probability under independent uniform source signs. -/
theorem failure_probability [FiniteDimensional F V] (P : D →ₗ[F] V)
    (reference : Module.Dual F D) :
    (Nat.card {h : Module.Dual F V // P.dualMap h + reference = 0} : ℚ) /
      2^(Module.finrank F V) =
      if reference ∈ (LinearMap.ker P).dualAnnihilator then
        1 / 2^(Module.finrank F (LinearMap.range P)) else 0 := by
  classical
  rw [outcome_count]
  simp only [zero_sub, Submodule.neg_mem_iff]
  split_ifs
  · push_cast
    have total : (2 : ℚ)^Module.finrank F V =
        2^(Module.finrank F V - Module.finrank F (LinearMap.range P)) *
        2^Module.finrank F (LinearMap.range P) := by
      rw [← pow_add, Nat.sub_add_cancel (LinearMap.range P).finrank_le]
    rw [total]
    field_simp
  · simp

/-- One residue gives two negative rows. Their combined left root uses the
sample twice, so the gcd outcome is independent of its two local signs. -/
theorem same_draw_437 :
    Nat.sqrt ((437-1)/2)=14 ∧ 60^2%437=104 ∧
    (4*104+21)%437=0 ∧ (21*104+1)%437=0 ∧
    2*4*21<437 ∧ 2*21*1<437 ∧ 14<21 ∧
    (4*21)*(21*1)=42^2 ∧ 4*21*104%437=433 ∧
    Nat.gcd (433-42) 437=23 ∧ Nat.gcd (433+42) 437=19 ∧
    19*23=437 ∧ Nat.Prime 19 ∧ Nat.Prime 23 := by decide +kernel

/-- The same residue has no signed fraction in the balanced box. -/
theorem balanced_box_437 :
    ∀ a b : Fin 15, a.val≠0 → b.val≠0 →
      (a.val*104)%437≠b.val ∧ (a.val*104+b.val)%437≠0 := by decide +kernel

end PrimeFactors.SharedRootSigns
