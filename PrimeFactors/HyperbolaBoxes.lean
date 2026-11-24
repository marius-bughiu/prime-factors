import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

namespace PrimeFactors

/-- Number of local product witnesses in a half-open integer rectangle. -/
noncomputable def hyperbolaBoxCount (N m a b H K : ℕ) : ℕ :=
  (((Finset.Ico a (a+H)) ×ˢ (Finset.Ico b (b+K))).filter
    (fun xy => (xy.1 * xy.2) % m = N % m)).card

/-- All starts of a smaller rectangle wholly contained in a larger rectangle,
when its side lengths are at most those of the larger rectangle. -/
noncomputable def innerBoxStarts (a b H K h k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc a (a + (H-h))) ×ˢ (Finset.Icc b (b + (K-k)))

theorem innerBoxStarts_card (a b H K h k : ℕ) :
    (innerBoxStarts a b H K h k).card = (H-h+1)*(K-k+1) := by
  simp only [innerBoxStarts,Finset.card_product,Nat.card_Icc]
  congr 1 <;> omega

theorem hyperbolaBoxCount_mono {N m a b H K h k : ℕ} {s : ℕ × ℕ}
    (rows : h ≤ H) (cols : k ≤ K) (inside : s ∈ innerBoxStarts a b H K h k) :
    hyperbolaBoxCount N m s.1 s.2 h k ≤ hyperbolaBoxCount N m a b H K := by
  obtain ⟨⟨ha,ha'⟩,⟨hb,hb'⟩⟩ :
      (a ≤ s.1 ∧ s.1 ≤ a + (H-h)) ∧ (b ≤ s.2 ∧ s.2 ≤ b + (K-k)) := by
    simpa [innerBoxStarts] using inside
  apply Finset.card_le_card
  intro xy hxy
  obtain ⟨⟨⟨_,_⟩,⟨_,_⟩⟩,hit⟩ := (by
    simpa only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] using hxy :
    ((s.1 ≤ xy.1 ∧ xy.1 < s.1+h) ∧ (s.2 ≤ xy.2 ∧ xy.2 < s.2+k)) ∧
      (xy.1*xy.2)%m=N%m)
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico]
  exact ⟨⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩,hit⟩

/-- Empty rectangles with disjoint row intervals contribute disjoint families
of empty smaller windows; the columns may coincide or depend on the rows. -/
theorem hyperbola_empty_box_packing {ι : Type*} (boxes : Finset ι) (a b : ι → ℕ)
    {N m H K h k : ℕ} (rowPos : 0 < h) (colPos : 0 < k) (rows : h ≤ H) (cols : k ≤ K)
    (fits : ∀ i ∈ boxes, a i + H ≤ m ∧ b i + K ≤ m)
    (apart : ∀ i ∈ boxes, ∀ j ∈ boxes, i ≠ j → a i + H ≤ a j ∨ a j + H ≤ a i)
    (empty : ∀ i ∈ boxes, hyperbolaBoxCount N m (a i) (b i) H K = 0) :
    boxes.card * ((H-h+1)*(K-k+1)) ≤
      (((Finset.range m) ×ˢ (Finset.range m)).filter
        (fun s => hyperbolaBoxCount N m s.1 s.2 h k = 0)).card := by
  classical
  let starts (i : ι) := innerBoxStarts (a i) (b i) H K h k
  have disjoint : (↑boxes : Set ι).PairwiseDisjoint starts := by
    intro i hi j hj hne
    apply Finset.disjoint_left.mpr
    intro s si sj
    have row (l : ι) (mem : s ∈ starts l) : a l ≤ s.1 ∧ s.1 ≤ a l + (H-h) :=
      Finset.mem_Icc.mp (Finset.mem_product.mp mem).1
    obtain ⟨_,_⟩ := row i si
    obtain ⟨_,_⟩ := row j sj
    rcases apart i hi j hj hne with _ | _ <;> omega
  rw [show boxes.card * ((H-h+1)*(K-k+1)) = (boxes.biUnion starts).card by
    rw [Finset.card_biUnion disjoint]
    simp [starts,innerBoxStarts_card]]
  apply Finset.card_le_card
  intro s hs
  obtain ⟨i,hi,si⟩ := Finset.mem_biUnion.mp hs
  have bound := hyperbolaBoxCount_mono (N := N) (m := m) rows cols si
  rw [empty i hi] at bound
  obtain ⟨fitRow,fitCol⟩ := fits i hi
  obtain ⟨⟨_,_⟩,⟨_,_⟩⟩ :
      (a i ≤ s.1 ∧ s.1 ≤ a i + (H-h)) ∧ (b i ≤ s.2 ∧ s.2 ≤ b i + (K-k)) := by
    simpa [starts,innerBoxStarts] using si
  simpa only [Finset.mem_filter,Finset.mem_product,Finset.mem_range] using
    (show (s.1<m ∧ s.2<m) ∧ hyperbolaBoxCount N m s.1 s.2 h k=0 from
      ⟨⟨by omega,by omega⟩,by omega⟩)

/-- A missing window contributes the full squared mean to the translated
second moment. This form makes the external analytic estimate replaceable. -/
theorem empty_windows_charge {ι : Type*} (s : Finset ι) (count : ι → ℕ) (μ : ℝ) :
    ((s.filter (fun i => count i = 0)).card : ℝ) * μ^2 ≤ ∑ i ∈ s, ((count i : ℝ)-μ)^2 := by
  classical
  calc
    _ = ∑ i ∈ s.filter (fun i => count i = 0), ((count i : ℝ)-μ)^2 := by
      rw [Finset.sum_congr rfl (g := fun _ => μ^2) (by
        intro i hi
        simp [(Finset.mem_filter.mp hi).2])]
      simp
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
      (by intros; positivity)

/-- Every positive difference strictly below the square of the prime cutoff
can keep at most one of the auxiliary primes. Distinct differences may keep
the same prime. -/
theorem hyperbola_false_prime_count (primes differences : Finset ℕ) (cutoff : ℕ)
    (pool : ∀ l ∈ primes, l.Prime ∧ cutoff ≤ l)
    (bounded : ∀ d ∈ differences, 0 < d ∧ d < cutoff*cutoff) :
    (differences.biUnion (fun d => primes.filter (fun l => l ∣ d))).card ≤ differences.card := by
  classical
  calc
    _ ≤ ∑ d ∈ differences, (primes.filter (fun l => l ∣ d)).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ differences, 1 := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.card_le_one.mpr
      intro l hl m hm
      obtain ⟨hl,ld⟩ := Finset.mem_filter.mp hl
      obtain ⟨hm,md⟩ := Finset.mem_filter.mp hm
      obtain ⟨lp,lb⟩ := pool l hl
      obtain ⟨mp,mb⟩ := pool m hm
      by_contra ne
      have large := Nat.mul_le_mul lb mb
      have small := Nat.le_of_dvd (bounded d hd).1 (Nat.Prime.dvd_mul_of_dvd_ne ne lp mp ld md)
      exact (Nat.not_le_of_lt (bounded d hd).2) (large.trans small)
    _ = _ := by simp

/-- A modular product witness supplies precisely a prime divisor of the
absolute difference, also when its integer product lies above the target. -/
theorem hyperbola_modEq_iff_dvd_error (x y N m : ℕ) :
    x*y ≡ N [MOD m] ↔ m ∣ ((N : ℤ)-(x*y : ℕ)).natAbs := by
  rw [Nat.modEq_iff_dvd, ← Int.natCast_dvd_natCast, Int.dvd_natAbs]

/-- Different primes can leave different local witnesses in the same false
box. The third prime removes all of them. -/
example :
    hyperbolaBoxCount 15049 251 94 151 7 10 = 2 ∧
    hyperbolaBoxCount 15049 257 94 151 7 10 = 1 ∧
    hyperbolaBoxCount 15049 263 94 151 7 10 = 0 := by decide

end PrimeFactors
