import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- With a unit normalized weight, multiplication by that weight identifies
the stationary-root equation with an ordinary square-root equation. -/
theorem actualSigns_normalize {R : Type*} [CommRing R] (u n σ : R) (v : Rˣ) :
    (v : R)*σ^2 = u*n ↔ ((v : R)*σ)^2 = u*(v : R)*n := by
  rw [show ((v : R)*σ)^2 = (v : R)*((v : R)*σ^2) by ring,
    show u*(v : R)*n = (v : R)*(u*n) by ring, v.isUnit.mul_right_inj]

/-- The leading coefficient and the normalized signed root differ by the
square of the unit σ. This identity preserves the actual square predicate. -/
theorem actualSigns_leading {R : Type*} [CommRing R] (d v : R) (σ : Rˣ) :
    IsSquare (d*v*(↑σ⁻¹ : R)) ↔ IsSquare (d*(v*(σ : R))) := by
  have changeRoot (a : R) (s : Rˣ) : IsSquare (a*(↑s⁻¹ : R)) → IsSquare (a*(s : R)) := by
    rintro ⟨r,hr⟩
    refine ⟨r*(s : R), ?_⟩
    calc
      a*(s : R) = (a*(↑s⁻¹ : R))*(s : R)*(s : R) := by rw [mul_assoc a, s.inv_mul, mul_one]
      _ = _ := by rw [hr]; ring
  rw [← mul_assoc]
  exact ⟨changeRoot _ σ, by simpa using changeRoot (d*v) σ⁻¹⟩

/-- If ψ is the square of the character χ (for example a quadratic
character with a quartic lift), then the sign is independent of which
stationary square root is chosen and factors through both weights. -/
theorem actualSigns_quartic {R K : Type*} [CommRing R] [CommMonoid K]
    (ψ χ : R →* K) (lift : ∀ x, ψ x = (χ x)^2) (d u v n σ : R)
    (stationary : v*σ^2 = u*n) :
    ψ (d*(v*σ)) = ψ d * (χ n * (χ u * χ v)) := by
  have square : (v*σ)^2 = u*v*n := by
    calc
      _ = v*(v*σ^2) := by ring
      _ = _ := by rw [stationary]; ring
  rw [map_mul ψ, lift (v*σ), ← map_pow, square, map_mul, map_mul]
  ac_rfl

/-- A character sees both square roots of a nondegenerate target with
total weight χ(dz)(1+χ(-1)). In particular the two signs cancel when
χ(-1) is negative one and the values are taken in a ring. -/
theorem actualSigns_root_sum {F K : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CommSemiring K] (χ : F →* K) (d t z : F) (root : z^2 = t) (distinct : z ≠ -z) :
    (∑ x ∈ Finset.univ.filter (fun x : F => x^2 = t), χ (d*x)) =
      χ (d*z)*(1+χ (-1)) := by
  have roots : Finset.univ.filter (fun x : F => x^2 = t) = {z,-z} := by
    ext x
    simp [← root,sq_eq_sq_iff_eq_or_eq_neg]
  rw [roots, Finset.sum_pair distinct, show d*(-z) = (d*z)*(-1) by ring,
    map_mul χ (d*z) (-1)]
  ring

/-- The character sum over the full weight rectangle is the product of
two one-dimensional sums even when some character values are zero. -/
theorem actualSigns_rectangle {R K : Type*} [CommMonoid R] [CommSemiring K]
    (χ : R →* K) (n : R) (U V : Finset R) :
    (∑ w ∈ U ×ˢ V, χ (w.1*w.2*n)) = χ n * (∑ u ∈ U, χ u) * (∑ v ∈ V, χ v) := by
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  simp only [map_mul]
  ac_rfl

/-- Per-pattern bounds on compatible weights transfer to the actual support
of the observed rows. Different rows may use the same weight, and a weight
may be compatible with several patterns. -/
theorem actualSigns_support {ι β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (rows : Finset ι) (weight : ι → β) (sign : ι → γ) (allowed : γ → Finset β)
    (H K : ℕ) (compatible : ∀ x ∈ rows, weight x ∈ allowed (sign x))
    (perWeight : ∀ w, (rows.filter fun x => weight x = w).card ≤ K)
    (perPattern : ∀ t ∈ rows.image sign, (allowed t).card ≤ H) :
    rows.card ≤ (rows.image sign).card*(H*K) := by
  classical
  rw [Finset.card_eq_sum_card_image sign rows]
  calc
    _ ≤ ∑ _t ∈ rows.image sign, H*K := by
      apply Finset.sum_le_sum
      intro t ht
      let S := rows.filter fun x => sign x = t
      have maps : S.toSet.MapsTo weight (allowed t) := by
        intro x hx
        obtain ⟨member,sgn⟩ := Finset.mem_filter.mp hx
        simpa [sgn] using compatible x member
      change S.card ≤ _
      rw [Finset.card_eq_sum_card_fiberwise maps]
      calc
        _ ≤ ∑ _w ∈ allowed t, K := Finset.sum_le_sum fun w _ =>
          (Finset.card_le_card (show (S.filter fun x => weight x = w) ⊆
            rows.filter (fun x => weight x = w) from fun x hx =>
              Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1,
                (Finset.mem_filter.mp hx).2⟩)).trans (perWeight w)
        _ ≤ H*K := by simpa using Nat.mul_le_mul_right K (perPattern t ht)
    _ = _ := by simp

end PrimeFactors
