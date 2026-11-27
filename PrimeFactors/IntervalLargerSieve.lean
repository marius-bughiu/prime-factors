import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-! The finite collision inequality underlying the prime-modulus case of
P. X. Gallagher, *A larger sieve*, Acta Arithmetica 18 (1971), Theorem 1,
pp. 77–78, doi:10.4064/aa-18-1-77-81. This form uses the diameter rather
than the number of integer positions, and needs no estimates for primes. -/
namespace PrimeFactors.IntervalLargerSieve

open Finset

private def collisions (S : Finset ℕ) (p : ℕ) :=
  S.offDiag.filter fun z => z.1%p=z.2%p

/-- Occupying at most ν residue classes forces many ordered collisions
when the diagonal is removed. -/
private theorem collision_lower (S : Finset ℕ) {p ν : ℕ} (pos : 0 < ν)
    (occupied : (S.image (fun x => x%p)).card ≤ ν) :
    (S.card:ℝ)^2/ν-S.card ≤ (collisions S p).card := by
  let bins := S.image (fun x => x%p)
  let row (r : ℕ) := S.filter fun x => x%p=r
  let allPairs := (S ×ˢ S).filter fun z => z.1%p=z.2%p
  have maps : Set.MapsTo (fun x => x%p) S bins := fun _ hx => mem_image_of_mem _ hx
  have pairMaps : Set.MapsTo (fun z : ℕ×ℕ => z.1%p) allPairs bins :=
    fun _ hz => maps (mem_product.mp (mem_filter.mp hz).1).1
  have fiber (r : ℕ) : allPairs.filter (fun z => z.1%p=r) = row r ×ˢ row r := by
    ext z
    simp only [allPairs,row,mem_filter,mem_product]
    aesop
  have size := card_eq_sum_card_fiberwise maps
  change S.card = ∑ r ∈ bins, (row r).card at size
  have pairs := card_eq_sum_card_fiberwise pairMaps
  simp_rw [fiber,card_product,←sq] at pairs
  have energy : S.card^2 ≤ ν*allPairs.card := by
    calc
      _ = (∑ r ∈ bins, (row r).card)^2 := congrArg (·^2) size
      _ ≤ bins.card*(∑ r ∈ bins, (row r).card^2) := sq_sum_le_card_mul_sum_sq
      _ ≤ _ := by rw [←pairs]; exact Nat.mul_le_mul_right _ occupied
  have partition : allPairs = S.diag ∪ collisions S p := by
    ext z
    simp only [allPairs,collisions,mem_union,mem_diag,mem_filter,mem_product,mem_offDiag]
    by_cases eq : z.1=z.2 <;> simp [eq,and_assoc]
  have disjoint : Disjoint S.diag (collisions S p) :=
    (disjoint_diag_offDiag S).mono_right (filter_subset ..)
  rw [partition,card_union_of_disjoint disjoint,diag_card] at energy
  have re : (S.card:ℝ)^2 ≤ ν*((S.card:ℝ)+(collisions S p).card) := by exact_mod_cast energy
  rw [sub_le_iff_le_add,div_le_iff₀ (by exact_mod_cast pos)]
  linarith only [re]

/-- Distinct primes at which a single ordered pair collides all divide its
nonzero distance, so their log weights sum to at most log H. -/
private theorem pair_price (P : Finset ℕ) {x y H : ℕ} (hH : 1 ≤ H)
    (prime : ∀ p ∈ P, p.Prime) (ne : x ≠ y)
    (xy : x ≤ y+H) (yx : y ≤ x+H) :
    (∑ p ∈ P, if x%p=y%p then Real.log p else 0) ≤ Real.log H := by
  let D := P.filter fun p => x%p=y%p
  have pp {p : ℕ} (hp : p ∈ D) : p.Prime := prime p (mem_filter.mp hp).1
  have dvd : ∏ p ∈ D, p ∣ Nat.dist x y := by
    apply prod_primes_dvd _ (fun p hp => (pp hp).prime)
    intro p hp
    have eq : x ≡ y [MOD p] := (mem_filter.mp hp).2
    rcases le_total x y with h|h
    · rw [Nat.dist_eq_sub_of_le h]
      exact (Nat.modEq_iff_dvd' h).mp eq
    · rw [Nat.dist_eq_sub_of_le_right h]
      exact (Nat.modEq_iff_dvd' h).mp eq.symm
  have dpos : 0 < Nat.dist x y := by
    rcases lt_or_gt_of_ne ne with h|h
    · rw [Nat.dist_eq_sub_of_le h.le]; omega
    · rw [Nat.dist_eq_sub_of_le_right h.le]; omega
  have bound : Nat.dist x y ≤ H := by
    rcases le_total x y with h|h
    · rw [Nat.dist_eq_sub_of_le h]; omega
    · rw [Nat.dist_eq_sub_of_le_right h]; omega
  have product := (Nat.le_of_dvd dpos dvd).trans bound
  have productPos : 0 < ∏ p ∈ D, p := prod_pos (fun _ hp => (pp hp).pos)
  rw [←sum_filter]
  change (∑ p ∈ D, Real.log p) ≤ _
  rw [←Real.log_prod D (fun p : ℕ => (p:ℝ)) (fun p hp => by
      change (p:ℝ) ≠ 0
      exact_mod_cast (pp hp).ne_zero),
    ←Nat.cast_prod]
  exact Real.strictMonoOn_log.monotoneOn (show (0:ℝ) < _ by exact_mod_cast productPos)
    (show (0:ℝ) < H by exact_mod_cast (show 0 < H by omega)) (by exact_mod_cast product)

/-- Gallagher's finite larger-sieve inequality for a set of distinct
primes and any positive upper bound on the number of residues at each.
It also holds for the empty set and for singletons. -/
theorem finite_bound (S P : Finset ℕ) (ν : ℕ → ℕ) {H : ℕ} (hH : 1 ≤ H)
    (prime : ∀ p ∈ P, p.Prime) (diam : ∀ x ∈ S, ∀ y ∈ S, x ≤ y+H)
    (pos : ∀ p ∈ P, 0 < ν p)
    (occupancy : ∀ p ∈ P, (S.image (fun x => x%p)).card ≤ ν p) :
    (∑ p ∈ P, Real.log p*((S.card:ℝ)^2/(ν p)-S.card)) ≤
      (S.card:ℝ)*(S.card-1)*Real.log H := by
  have weight (p : ℕ) : Real.log p*((collisions S p).card:ℝ) =
      ∑ z ∈ S.offDiag, if z.1%p=z.2%p then Real.log p else 0 := by
    rw [←sum_filter,sum_const,nsmul_eq_mul,mul_comm]
    rfl
  have size : (S.offDiag.card:ℝ) = (S.card:ℝ)*(S.card-1) := by
    have le : S.card ≤ S.card*S.card := by nlinarith [Nat.mul_self_le_mul_self (Nat.zero_le S.card)]
    rw [offDiag_card,Nat.cast_sub le,Nat.cast_mul]
    ring
  calc
    _ ≤ ∑ p ∈ P, Real.log p*(collisions S p).card := by
      apply sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (collision_lower S (pos p hp) (occupancy p hp))
        (Real.log_nonneg (by exact_mod_cast (prime p hp).one_le))
    _ = ∑ z ∈ S.offDiag, ∑ p ∈ P, if z.1%p=z.2%p then Real.log p else 0 := by
      simp_rw [weight]; rw [sum_comm]
    _ ≤ ∑ _z ∈ S.offDiag, Real.log H := by
      apply sum_le_sum
      intro z hz
      obtain ⟨x,y,ne⟩ := mem_offDiag.mp hz
      exact pair_price P hH prime ne (diam _ x _ y) (diam _ y _ x)
    _ = _ := by rw [sum_const,nsmul_eq_mul,size]

/-- Cancelling a positive cardinality leaves the coefficient of K explicit,
without requiring that this coefficient be positive. -/
theorem linear_bound (S P : Finset ℕ) (ν : ℕ → ℕ) {H : ℕ} (hH : 1 ≤ H)
    (prime : ∀ p ∈ P, p.Prime) (diam : ∀ x ∈ S, ∀ y ∈ S, x ≤ y+H)
    (pos : ∀ p ∈ P, 0 < ν p)
    (occupancy : ∀ p ∈ P, (S.image (fun x => x%p)).card ≤ ν p)
    (nonempty : S.Nonempty) :
    (S.card:ℝ)*((∑ p ∈ P, Real.log p/ν p)-Real.log H) ≤
      (∑ p ∈ P, Real.log p)-Real.log H := by
  let K : ℝ := S.card
  have kp : 0 < K := by
    change (0:ℝ) < S.card
    exact_mod_cast card_pos.mpr nonempty
  have bound := finite_bound S P ν hH prime diam pos occupancy
  change (∑ p ∈ P, Real.log p*(K^2/ν p-K)) ≤ K*(K-1)*Real.log H at bound
  have term (p : ℕ) : Real.log p*(K^2/ν p-K) = K^2*(Real.log p/ν p)-K*Real.log p := by ring
  simp_rw [term] at bound
  rw [sum_sub_distrib,←mul_sum,←mul_sum] at bound
  apply le_of_mul_le_mul_left (a:=K) _ kp
  change K*(K*((∑ p ∈ P, Real.log p/ν p)-Real.log H)) ≤ _
  nlinarith only [bound]

/-- The usual numerical bound when the larger-sieve denominator is
positive. An interval of any integer origin may be translated into ℕ. -/
theorem ratio_bound (S P : Finset ℕ) (ν : ℕ → ℕ) {H : ℕ} (hH : 1 ≤ H)
    (prime : ∀ p ∈ P, p.Prime) (diam : ∀ x ∈ S, ∀ y ∈ S, x ≤ y+H)
    (pos : ∀ p ∈ P, 0 < ν p)
    (occupancy : ∀ p ∈ P, (S.image (fun x => x%p)).card ≤ ν p)
    (nonempty : S.Nonempty) (den : Real.log H < ∑ p ∈ P, Real.log p/ν p) :
    (S.card:ℝ) ≤ ((∑ p ∈ P, Real.log p)-Real.log H) /
      ((∑ p ∈ P, Real.log p/ν p)-Real.log H) :=
  (le_div_iff₀ (sub_pos.mpr den)).mpr (linear_bound S P ν hH prime diam pos occupancy nonempty)

end PrimeFactors.IntervalLargerSieve
