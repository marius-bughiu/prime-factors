import PrimeFactors.ExceptionalWeights
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace PrimeFactors

/-- Allowing up to h failed local tests fills a union of coordinate boxes.
This finite bound retains the actual sizes of all the local retained sets. -/
theorem shortBasis_thick_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (keep : ∀ i, Finset (A i)) (h : ℕ) :
    (Finset.univ.filter (fun x : ∀ i, A i =>
      (Finset.univ.filter (fun i => x i ∉ keep i)).card ≤ h)).card ≤
    ∑ b ∈ (Finset.univ : Finset ι).powerset.filter (fun b => b.card ≤ h),
      ∏ i, (if i ∈ b then Fintype.card (A i) else (keep i).card) := by
  classical
  let F := (Finset.univ : Finset ι).powerset.filter (fun b => b.card ≤ h)
  let box (b : Finset ι) := Fintype.piFinset (fun i => if i ∈ b then Finset.univ else keep i)
  have subset : (Finset.univ.filter (fun x : ∀ i, A i =>
      (Finset.univ.filter (fun i => x i ∉ keep i)).card ≤ h)) ⊆ F.biUnion box := by
    intro x hx
    let b := Finset.univ.filter (fun i => x i ∉ keep i)
    apply Finset.mem_biUnion.mpr
    refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
      (Finset.mem_filter.mp hx).2⟩, ?_⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    by_cases hi : x i ∈ keep i <;> simp [b, hi]
  apply (Finset.card_le_card subset).trans
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro b _
  rw [show (box b).card = _ from Fintype.card_piFinset _]
  apply le_of_eq
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ b <;> simp [hi]

/-- If every failed selected prime is at least y and their product divides d,
then the number of failed positions costs a corresponding power of y. -/
theorem shortBasis_bad_product (P : Finset ℕ) {y d : ℕ} (pos : 0<d)
    (large : ∀ p ∈ P, y≤p) (divides : (∏ p ∈ P, p) ∣ d) : y^P.card ≤ d := by
  calc y^P.card = ∏ _ ∈ P, y := by simp
       _ ≤ ∏ p ∈ P, p := Finset.prod_le_prod' large
       _ ≤ d := Nat.le_of_dvd pos divides

/-- The transported slope at the actual smaller factor. The first term is
the geometric derivative at the public interval endpoint and the second term
charges moving the endpoint to the unknown factor. -/
theorem shortBasis_slope_transport {p q a b center err gap : ℝ}
    (pp : 0<p) (atCenter : |b-a*center| ≤ err)
    (move : |center-q/p| ≤ gap) :
    |a*q-b*p| ≤ p*(err+|a| * gap) := by
  have eq : a*q-b*p = -p*((b-a*center)+a*(center-q/p)) := by
    field_simp [pp.ne']
    ring
  rw [eq, abs_mul, abs_neg, abs_of_pos pp]
  apply mul_le_mul_of_nonneg_left _ pp.le
  apply (abs_add_le ..).trans
  rw [abs_mul]
  exact add_le_add atCenter (mul_le_mul_of_nonneg_left move (abs_nonneg _))

/-- Once the actual trace differs from its minimum by at most c/(d²u),
dividing by the progression modulus (m/d)² cancels the whole d². -/
theorem shortBasis_divided_slack {error c d r u : ℝ}
    (dpos : 0<d) (rpos : 0<r) (upos : 0<u) (h : error*(d^2*u) ≤ c) :
    error/r^2 ≤ c/((d*r)^2*u) := by
  apply (div_le_div_iff₀ (sq_pos_of_pos rpos) (mul_pos (sq_pos_of_pos (mul_pos dpos rpos)) upos)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right h (sq_nonneg r)]

/-- The actual trace span in units of r² is independent of the common
divisor once X=(dr)m₀ is fixed. This combines the geometric error with the
lower bound q≥√N used for a balanced exceptional sweep. -/
theorem shortBasis_exceptional_window {u v p q s w d r m₀ : ℝ}
    (hu : 0<u) (hv : 0<v) (hp : 0<p) (hs : 0<s) (large : s≤q)
    (hd : 0<d) (hr : 0<r) (hm : 0<m₀) (weight : w^2=d*r*m₀)
    (gap : |u*q-v*p| ≤ 40*s*w/(m₀*d)) :
    (u*q+v*p-2*Real.sqrt (u*v*p*q))/r^2 ≤ 1600*s/(d*r*m₀*u) := by
  have hq := hs.trans_le large
  have slack := (exceptionalWeight_slack hu hv hp hq gap).2.1
  calc
    _ ≤ (40*s*w/(m₀*d))^2/(u*q)/r^2 :=
      div_le_div_of_nonneg_right slack (sq_nonneg r)
    _ ≤ (40*s*w/(m₀*d))^2/(u*s)/r^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg r)
      exact div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hu hs)
        (mul_le_mul_of_nonneg_left large hu.le)
    _ = _ := by
      field_simp [hd.ne', hr.ne', hm.ne', hu.ne', hs.ne']
      ring_nf
      rw [weight]
      ring

/-- For each normalized first weight u, counting at most 3u second weights
cancels the reciprocal u in the number of trace chunks. This bound includes
the unit overhead per weight and per root class. -/
theorem shortBasis_chunk_sum {U P Z : ℕ} (entries : ℕ → ℕ)
    (bound : ∀ i < U, entries (i+1) ≤ 3*(i+1)*P*(1+Z/(i+1))) :
    (∑ i ∈ Finset.range U, entries (i+1)) ≤ U*(3*P*(U+Z)) := by
  calc
    _ ≤ ∑ _i ∈ Finset.range U, 3*P*(U+Z) := by
      apply Finset.sum_le_sum
      intro i hi
      have iu := Finset.mem_range.mp hi
      apply (bound i iu).trans
      have count := Nat.div_mul_le_self Z (i+1)
      calc 3*(i+1)*P*(1+Z/(i+1)) = 3*P*((i+1)+(Z/(i+1))*(i+1)) := by ring
           _ ≤ 3*P*(U+Z) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by simp

end PrimeFactors
