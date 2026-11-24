import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Fintype.BigOperators

namespace PrimeFactors

/-- A binary square-status coordinate suffices for constructing a passing product.
If either input vanishes modulo the test prime, the product is automatically square. -/
private theorem isSquare_product_of_matching_bits {p a b : ℕ} [Fact p.Prime]
    (matchBits : IsSquare (a : ZMod p) ↔ IsSquare (b : ZMod p)) :
    IsSquare ((a * b : ℕ) : ZMod p) := by
  by_cases za : (a : ZMod p) = 0
  · simp [za]
  by_cases zb : (b : ZMod p) = 0
  · simp [zb]
  have nz : ((a * b : ℕ) : ZMod p) ≠ 0 := by simpa using mul_ne_zero za zb
  apply (legendreSym.eq_one_iff' p nz).mp
  rw [Nat.cast_mul, legendreSym.mul]
  by_cases sa : IsSquare (a : ZMod p)
  · rw [(legendreSym.eq_one_iff' p za).mpr sa,
        (legendreSym.eq_one_iff' p zb).mpr (matchBits.mp sa), one_mul]
  · have neg {u : ℕ} (h : (u : ZMod p) ≠ 0) (hn : ¬IsSquare (u : ZMod p)) :
        legendreSym p u = -1 := by
      rcases legendreSym.eq_one_or_neg_one p (by simpa using h : ((u : ℤ) : ZMod p) ≠ 0)
          with one | minus
      · exact (hn ((legendreSym.eq_one_iff' p h).mp one)).elim
      · exact minus
    rw [neg za sa, neg zb (fun h => sa (matchBits.mpr h))]
    decide

/-- Among squarefree natural numbers a square product forces equality. -/
theorem eq_of_squarefree_product_square {a b : ℕ} (ha : Squarefree a)
    (hb : Squarefree b) (product : IsSquare (a * b)) : a = b := by
  obtain ⟨z, sq⟩ := product
  have nz : z ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at sq
    exact (Nat.mul_ne_zero ha.ne_zero hb.ne_zero) sq
  have hza : a ∣ z := (ha.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp (by
    rw [pow_two, ← sq]; exact dvd_mul_right a b)
  have hzb : b ∣ z := (hb.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp (by
    rw [pow_two, ← sq]; exact dvd_mul_left b a)
  have az := Nat.le_of_dvd (Nat.pos_of_ne_zero nz) hza
  have bz := Nat.le_of_dvd (Nat.pos_of_ne_zero nz) hzb
  apply le_antisymm
  · have bound : a * a ≤ a * b := sq ▸ Nat.mul_le_mul az az
    exact Nat.le_of_mul_le_mul_left bound (Nat.pos_of_ne_zero ha.ne_zero)
  · have bound : b * b ≤ a * b := sq ▸ Nat.mul_le_mul bz bz
    exact Nat.le_of_mul_le_mul_right bound (Nat.pos_of_ne_zero hb.ne_zero)

/-- A set of prime tests recognizing every integer square up to Y² must encode
every squarefree marker up to Y by a distinct binary word. No coprimality
assumption on test primes and markers is necessary. -/
theorem squarefree_markers_le_signature_count (Y : ℕ) (tests markers : Finset ℕ)
    (primes : ∀ p ∈ tests, p.Prime)
    (valid : ∀ a ∈ markers, a ≤ Y ∧ Squarefree a)
    (detect : ∀ d ≤ Y ^ 2, (∀ p ∈ tests, IsSquare (d : ZMod p)) → IsSquare d) :
    markers.card ≤ 2 ^ tests.card := by
  classical
  let bits (u : markers) (p : tests) := decide (IsSquare (u.val : ZMod p.val))
  have inj : Function.Injective bits := by
    intro u v eqn
    obtain ⟨ule, usq⟩ := valid _ u.property
    obtain ⟨vle, vsq⟩ := valid _ v.property
    apply Subtype.ext
    apply eq_of_squarefree_product_square usq vsq
    apply detect (u.val * v.val) (by simpa [pow_two] using Nat.mul_le_mul ule vle)
    intro p hp
    letI : Fact p.Prime := ⟨primes p hp⟩
    apply isSquare_product_of_matching_bits
    simpa [bits] using congrFun eqn ⟨p, hp⟩
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective bits inj

/-- Prime markers are a useful special case with a purely finite counting statement. -/
theorem primes_le_signature_count (Y : ℕ) (tests : Finset ℕ)
    (primes : ∀ p ∈ tests, p.Prime)
    (detect : ∀ d ≤ Y ^ 2, (∀ p ∈ tests, IsSquare (d : ZMod p)) → IsSquare d) :
    ((Finset.range (Y + 1)).filter Nat.Prime).card ≤ 2 ^ tests.card := by
  apply squarefree_markers_le_signature_count Y tests _ primes _ detect
  intro a ha
  obtain ⟨bound, prime⟩ := Finset.mem_filter.mp ha
  exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp bound), prime.squarefree⟩

private theorem square_divisor_count (Y j : ℕ) :
    (∑ i ∈ Finset.range j, Y / (i + 3)^2) + Y / (j + 2) ≤ Y / 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have pos : 0 < j + 3 := by omega
    let w := Y / (j + 3)^2
    let v := Y / (j + 3)
    have wle : w * (j + 3) ≤ v := by
      apply (Nat.le_div_iff_mul_le pos).mpr
      rw [Nat.mul_assoc, ← pow_two]
      exact Nat.div_mul_le_self Y _
    have wle' : w * (j + 2) ≤ v := (Nat.mul_le_mul_left w (by omega : j + 2 ≤ j + 3)).trans wle
    have step : w + v ≤ Y / (j + 2) := by
      apply (Nat.le_div_iff_mul_le (by omega)).mpr
      calc
        _ = w * (j + 2) + v * (j + 2) := Nat.add_mul ..
        _ ≤ v + v * (j + 2) := Nat.add_le_add_right wle' _
        _ = v * (j + 3) := by rw [Nat.mul_succ v (j + 2), Nat.add_comm]
        _ ≤ Y := Nat.div_mul_le_self _ _
    change (∑ i ∈ Finset.range j, Y / (i + 3)^2) + w + v ≤ _
    omega

/-- At least one quarter of 1 through Y is squarefree. Counting multiples of
all possible square divisors gives this coarse bound with no asymptotic input. -/
theorem four_mul_squarefree_count_ge (Y : ℕ) :
    Y ≤ 4 * ((Finset.Icc 1 Y).filter Squarefree).card := by
  classical
  let good := (Finset.Icc 1 Y).filter Squarefree
  let bad := (Finset.Icc 1 Y).filter (fun a => ¬Squarefree a)
  let hits (i : ℕ) := (Finset.Icc 1 (Y/(i+2)^2)).image (fun v => (i+2)^2 * v)
  have cover : bad ⊆ (Finset.range (Y + 1)).biUnion hits := by
    intro a ha
    obtain ⟨range, fails⟩ := Finset.mem_filter.mp ha
    obtain ⟨apos, bound⟩ := Finset.mem_Icc.mp range
    rw [Nat.squarefree_iff_prime_squarefree] at fails
    push_neg at fails
    obtain ⟨p, prime, z, eqn⟩ := fails
    have ppos := prime.two_le
    have pDvd : p ∣ a := dvd_trans (dvd_mul_right p p) ⟨z, eqn⟩
    have boundP := (Nat.le_of_dvd apos pDvd).trans bound
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le ppos
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
    have eqn' : a = (i + 2)^2 * z := by simpa [pow_two, Nat.add_comm i 2] using eqn
    have zpos : 1 ≤ z := by
      by_contra! small
      have hz : z = 0 := by omega
      simp [hz] at eqn'
      omega
    refine Finset.mem_image.mpr ⟨z, Finset.mem_Icc.mpr ⟨zpos, ?_⟩, eqn'.symm⟩
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    simpa [Nat.mul_comm, eqn'] using bound
  have ub : bad.card ≤ ∑ i ∈ Finset.range (Y+1), Y / (i+2)^2 := calc
    _ ≤ _ := Finset.card_le_card cover
    _ ≤ ∑ i ∈ Finset.range (Y + 1), (hits i).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      simpa [hits] using (Finset.card_image_le :
        ((Finset.Icc 1 (Y/(i+2)^2)).image (fun v => (i+2)^2 * v)).card ≤ _)
  rw [Finset.sum_range_succ'] at ub
  have tail := square_divisor_count Y Y
  have total : good.card + bad.card = Y := by
    simpa [good,bad] using (Finset.filter_card_add_filter_neg_card_eq_card
      (s := Finset.Icc 1 Y) (p := Squarefree))
  change _ ≤ 4 * good.card
  change bad.card ≤ (∑ i ∈ Finset.range Y, Y / (i+3)^2) + Y / 4 at ub
  have tailBound : (∑ i ∈ Finset.range Y, Y / (i+3)^2) ≤ Y / 2 := (Nat.le_add_right ..).trans tail
  have badBound := ub.trans (Nat.add_le_add_right tailBound (Y / 4))
  have half := Nat.div_mul_le_self Y 2
  have quarter := Nat.div_mul_le_self Y 4
  have estimate : 4 * (Y / 2 + Y / 4) ≤ 3 * Y := by omega
  have finalBound := (Nat.mul_le_mul_left 4 badBound).trans estimate
  omega

/-- To recognize all positive integer squares through 2^b using only square
tests at prime moduli, at least floor(b/2)−2 distinct primes are required. -/
theorem universal_square_detector_length (b : ℕ) (tests : Finset ℕ)
    (primes : ∀ p ∈ tests, p.Prime)
    (detect : ∀ d ≤ 2 ^ b, (∀ p ∈ tests, IsSquare (d : ZMod p)) → IsSquare d) :
    b / 2 ≤ tests.card + 2 := by
  let Y := 2 ^ (b / 2)
  have scale : Y ^ 2 ≤ 2 ^ b := by
    dsimp [Y]
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have words := squarefree_markers_le_signature_count Y tests
    ((Finset.Icc 1 Y).filter Squarefree) primes (by
      intro a ha
      obtain ⟨range, sq⟩ := Finset.mem_filter.mp ha
      exact ⟨(Finset.mem_Icc.mp range).2, sq⟩)
    (fun d size => detect d (size.trans scale))
  have bound := (four_mul_squarefree_count_ge Y).trans (Nat.mul_le_mul_left 4 words)
  apply (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp
  simpa [Y, pow_add, Nat.mul_comm] using bound

end PrimeFactors
