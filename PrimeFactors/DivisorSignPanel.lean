import PrimeFactors.ReciprocalDivisorClasses

/-! Linear verification of a long list of public negative-square witnesses.
The running product replaces one gcd for every pair by one gcd per entry. -/

namespace PrimeFactors.DivisorSignPanel

/-- Each entry consists of the modulus followed by its public negative root. -/
abbrev Entry := ℕ × ℕ

noncomputable def check (n bound previous : ℕ) : List Entry → Bool
  | [] => true
  | (d,a) :: rest =>
    decide (d % 4 = 3 ∧ d < bound ∧ n.Coprime d ∧ n ∣ a^2+d ∧ d.Coprime previous) &&
      check n bound (previous*d) rest

theorem properties {n bound : ℕ} (entries : List Entry) (previous : ℕ)
    (h : check n bound previous entries = true) :
    (∀ e ∈ entries, e.1 % 4 = 3 ∧ e.1 < bound ∧ n.Coprime e.1 ∧
      n ∣ e.2^2+e.1 ∧ e.1.Coprime previous) ∧
    entries.Pairwise (fun e f => e.1.Coprime f.1) := by
  induction entries generalizing previous with
  | nil => simp
  | cons e tail ih =>
    obtain ⟨d,a⟩ := e
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rest, pairs⟩ := ih (previous*d) h.2
    constructor
    · intro e he
      rcases List.mem_cons.mp he with rfl | ht
      · exact h.1
      · obtain ⟨m,b,c,s,g⟩ := rest e ht
        exact ⟨m,b,c,s,g.of_dvd_right (dvd_mul_right previous d)⟩
    · exact List.pairwise_cons.mpr ⟨fun e he =>
        ((rest e he).2.2.2.2.of_dvd_right (dvd_mul_left d previous)).symm, pairs⟩

/-- Every odd divisor of the public product satisfies every certified sign. -/
theorem divisor_signs {n bound : ℕ} (entries : List Entry)
    (h : check n bound 1 entries = true) {p : ℕ} (odd : Odd p) (div : p ∣ n) :
    ∀ e ∈ entries, jacobiSym (p : ℤ) e.1 = 1 := by
  intro e he
  obtain ⟨m,_,c,s,_⟩ := (properties entries 1 h).1 e he
  apply ReciprocalDivisorClasses.divisor_of_witness (a := (e.2 : ℤ)) m odd div c
  exact_mod_cast s

/-- The ordinary primes in an inclusive interval satisfying every selected sign. -/
noncomputable def primes (lo hi : ℕ) (entries : List Entry) : Finset ℕ := by
  classical
  exact (Finset.Icc lo hi).filter (fun p => p.Prime ∧ ∀ e ∈ entries, jacobiSym (p : ℤ) e.1 = 1)

theorem smaller_prime_mem {n p q B bound : ℕ} (entries : List Entry)
    (h : check n bound 1 entries = true) (eq : n = p*q) (prime : p.Prime)
    (odd : Odd p) (ordered : p ≤ q) (capped : q ≤ B) :
    p ∈ primes ((n-1)/B+1) n.sqrt entries := by
  have pos := prime.pos
  have qp := pos.trans_le ordered
  have bp := qp.trans_le capped
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,prime,?_⟩
  · apply (Nat.div_lt_iff_lt_mul bp).mpr
    rw [eq]
    exact (Nat.sub_lt (Nat.mul_pos pos qp) (by decide)).trans_le (Nat.mul_le_mul_left p capped)
  · rw [eq]
    exact Nat.le_sqrt.mpr (Nat.mul_le_mul_left p ordered)
  · exact divisor_signs entries h odd (eq ▸ dvd_mul_right p q)

/-- Integer form of the upper and lower weighted bounds after applying an
external prime-ideal estimate to the specific set of candidate primes. -/
def weightedBounds (m width error hits : ℕ) : Prop :=
  m*708*hits ≤ width+m*error ∧ width ≤ m*710*hits+m*error

/-- Validate rounded whole-number endpoints while keeping the enormous set of
candidate primes symbolic. A lower bound of zero needs no rounding witness. -/
theorem rounded {m w e h lo hi : ℕ} (b : weightedBounds m w e h)
    (l : lo = 0 ∨ m*710*(lo-1)+m*e < w)
    (u : w+m*e < m*708*(hi+1)) : lo ≤ h ∧ h ≤ hi := by
  constructor
  · rcases l with rfl | l
    · exact Nat.zero_le _
    · by_contra! lt
      exact (not_lt_of_ge (b.2.trans (Nat.add_le_add_right
        (Nat.mul_le_mul_left _ (show h ≤ lo-1 by omega)) _))) l
  · by_contra! lt
    exact (not_lt_of_ge ((Nat.mul_le_mul_left (m*708) lt).trans b.1)) u

end PrimeFactors.DivisorSignPanel
