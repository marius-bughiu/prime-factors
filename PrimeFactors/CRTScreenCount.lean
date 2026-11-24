import PrimeFactors.CRTSquareNorm
import PrimeFactors.PrimePowerCount
import PrimeFactors.RareRows
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith

namespace PrimeFactors

/-- Sum of the path weights at which the requested number of primes is first
accepted within the remaining tests. Skipping a prime costs a factor of two. -/
noncomputable def crtScreenMass : ℕ → ℕ → ℚ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | j + 1, r + 1 => crtScreenMass j r + crtScreenMass j (r + 1) / 2

theorem crtScreenMass_le (j r : ℕ) : crtScreenMass j r ≤ 2^r := by
  induction j generalizing r with
  | zero => cases r <;> simp [crtScreenMass]
  | succ j ih =>
    cases r with
    | zero => simp [crtScreenMass]
    | succ r =>
      rw [crtScreenMass, pow_succ]
      have h := ih (r+1)
      rw [pow_succ] at h
      linarith [ih r]

/-- For fixed t and nonzero a, exactly (p-1)/2 quotients have a nonsquare
value of t²-aQ. -/
theorem crtScreen_nonsquare_count (p : ℕ) [Fact p.Prime] (odd : p ≠ 2)
    (t a : ZMod p) (ha : a ≠ 0) :
    Nat.card {Q : ZMod p // ¬ IsSquare (t^2-a*Q)} = (p-1)/2 := by
  classical
  let e : ZMod p ≃ ZMod p :=
    { toFun := fun Q => t^2-a*Q
      invFun := fun d => (t^2-d)/a
      left_inv := by intro Q; field_simp
      right_inv := by intro d; field_simp }
  let perm := e.subtypeEquiv (p := fun Q => ¬ IsSquare (t^2-a*Q))
    (q := fun d => ¬ IsSquare d) (fun _ => Iff.rfl)
  rw [Nat.card_congr perm, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ZMod.card]
  have squares : Fintype.card {d : ZMod p // IsSquare d} = (p-1)/2+1 := by
    rw [← Nat.card_eq_fintype_card]
    have h := card_primePower_squares (p := p) odd 1
    rw [pow_one] at h
    exact h
  obtain ⟨i,hi⟩ := (Fact.out : p.Prime).odd_of_ne_two odd
  omega

/-- In a window, any translated set of classes of density at most 2^(-s)
has at most (W+M)/2^s representatives. The allowed residues can depend on
the fixed root candidate and on the lower endpoint of the window. -/
theorem crtScreen_window (W M s : ℕ) (positive : 0 < M) (roots : Finset ℕ)
    (density : roots.card * 2^s ≤ M) :
    ((Finset.range W).filter fun q => q % M ∈ roots).card * 2^s ≤ W+M := by
  let blocks := W / M + 1
  have cover : W ≤ blocks*M := by
    dsimp [blocks]
    have h := Nat.mod_add_div W M
    have h' := Nat.mod_lt W positive
    rw [Nat.add_mul, one_mul, Nat.mul_comm (W / M) M]
    omega
  have enlarge := Finset.card_le_card (Finset.filter_subset_filter
    (p := fun q => q % M ∈ roots) (Finset.range_mono cover))
  have rows := enlarge.trans (rareRows_lift_count blocks M positive roots)
  calc
    _ ≤ (blocks * roots.card) * 2^s := Nat.mul_le_mul_right _ rows
    _ = blocks * (roots.card * 2^s) := Nat.mul_assoc ..
    _ ≤ blocks * M := Nat.mul_le_mul_left _ density
    _ ≤ W+M := by
      dsimp [blocks]
      rw [Nat.add_mul, one_mul]
      exact Nat.add_le_add_right (Nat.div_mul_le_self W M) M

/-- Double count subsets of k skipped primes. If every bad input skips at
least m of J primes, lower and upper incidence bounds can be compared directly. -/
theorem crtScreen_skipped_subsets {α β : Type*} [DecidableEq α] [DecidableEq β]
    (inputs : Finset α) (primes : Finset β) (skips : α → Finset β) (m k K : ℕ)
    (inside : ∀ x ∈ inputs, skips x ⊆ primes)
    (many : ∀ x ∈ inputs, m ≤ (skips x).card)
    (fiber : ∀ S ∈ primes.powersetCard k, (inputs.filter fun x => S ⊆ skips x).card ≤ K) :
    inputs.card * m.choose k ≤ primes.card.choose k * K := by
  classical
  let subsets := primes.powersetCard k
  have row (x : α) (hx : x ∈ inputs) :
      ((skips x).powersetCard k) = subsets.filter (fun S => S ⊆ skips x) := by
    ext S
    simp only [subsets, Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨⟨h.1.trans (inside x hx), h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  calc
    inputs.card * m.choose k = ∑ _x ∈ inputs, m.choose k := by simp
    _ ≤ ∑ x ∈ inputs, ((skips x).powersetCard k).card := by
      apply Finset.sum_le_sum
      intro x hx
      rw [Finset.card_powersetCard]
      exact Nat.choose_le_choose k (many x hx)
    _ = ∑ x ∈ inputs, ∑ S ∈ subsets, if S ⊆ skips x then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [row x hx, Finset.card_filter]
    _ = ∑ S ∈ subsets, ∑ x ∈ inputs, if S ⊆ skips x then 1 else 0 := Finset.sum_comm
    _ ≤ ∑ _S ∈ subsets, K := by
      apply Finset.sum_le_sum
      intro S hS
      simpa only [Finset.card_filter] using fiber S hS
    _ = primes.card.choose k * K := by simp [subsets]

/-- Exact numerical check of the finite 2,048-bit estimate. B bounds the
period of the first 104 skipped tests, and T the period of any 99-test sample.
The first fraction counts products before the 256th prime. The second
bounds the probability that the screen has not stopped by then. -/
theorem crtScreen_2048_constants :
    let primes := ((List.range 1622).filter (fun p => decide (p.Prime ∧ 2 < p)))
    let X := 2^1023
    let W := 2^901-1
    let B := ((primes.drop 32).take 104).prod
    let T := (primes.drop (256-99)).prod
    let nearNum := 6*(W+B)*(2^(32+104)+Nat.choose 256 32)*710^2*10000
    let nearDen := 2^104*22^2*X
    let tailNum := (X+T)*Nat.choose 256 99*1511*710*10000
    let tailDen := X*1000*22^2*2^99*Nat.choose 225 99
    primes.length = 256 ∧ 1621^64 * 2^900 < X^2 ∧
      2^60*(nearNum*tailDen+tailNum*nearDen) < nearDen*tailDen := by
  rw [crtOddPrimes_trial 1622 (by decide)]
  dsimp only
  rw [Nat.choose_eq_factorial_div_factorial (by decide : 32 ≤ 256),
    Nat.choose_eq_factorial_div_factorial (by decide : 99 ≤ 256),
    Nat.choose_eq_factorial_div_factorial (by decide : 99 ≤ 225)]
  set_option maxRecDepth 65536 in
  set_option maxHeartbeats 3500000 in
  decide +kernel

end PrimeFactors
