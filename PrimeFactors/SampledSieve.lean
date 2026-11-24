import Mathlib.Data.Fintype.BigOperators
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.Prime

namespace PrimeFactors

/-- Count ordered samples of t tests leaving any false candidate. A candidate
survives a tuple precisely when all coordinates lie in its passing set. -/
theorem surviving_sample_count {δ α : Type*} [DecidableEq α] (falseCases : Finset δ)
    (passes : δ → Finset α) (T t : ℕ) (bound : ∀ d ∈ falseCases, (passes d).card ≤ T) :
    (falseCases.biUnion (fun d => Fintype.piFinset (fun _ : Fin t => passes d))).card ≤
      falseCases.card * T ^ t := by
  classical
  calc
    _ ≤ ∑ d ∈ falseCases, (Fintype.piFinset (fun _ : Fin t => passes d)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ falseCases, T ^ t := by
      apply Finset.sum_le_sum
      intro d hd
      rw [Fintype.card_piFinset_const]
      exact Nat.pow_le_pow_left (bound d hd) t
    _ = _ := by simp

private theorem nonsquare_of_euler_value {p : ℕ} [Fact p.Prime] (d : ℕ)
    (h : d % p ≠ 0 ∧ d ^ (p / 2) % p ≠ 1) : ¬ IsSquare (d : ZMod p) := by
  intro hs
  have nonzero : (d : ZMod p) ≠ 0 := by
    intro zero
    apply h.1
    simpa using congrArg ZMod.val zero
  letI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have eqn := congrArg ZMod.val ((ZMod.euler_criterion p nonzero).mp hs)
  rw [← Nat.cast_pow, ZMod.val_natCast, ZMod.val_one] at eqn
  exact h.2 eqn

private def misses (p x : ℕ) : Bool := x % p != 0 && x ^ (p / 2) % p != 1
private def eightBitTest (x : ℕ) : Bool :=
  x.sqrt ^ 2 == x || misses 89 x || misses 37 x || misses 23 x || misses 47 x || misses 3 x

private theorem eightBitTest_checked : (List.range 256).all eightBitTest = true := by decide +kernel

/-- A concrete universal sieve. These five odd primes detect every positive
nonsquare below 256, even when some of them divide the candidate. -/
theorem universal_square_sieve_8bit (d : Fin 256) :
    d.val.sqrt ^ 2 = d.val ∨
      ¬ IsSquare (d.val : ZMod 89) ∨ ¬ IsSquare (d.val : ZMod 37) ∨
      ¬ IsSquare (d.val : ZMod 23) ∨ ¬ IsSquare (d.val : ZMod 47) ∨
      ¬ IsSquare (d.val : ZMod 3) := by
  have hit : eightBitTest d.val = true :=
    List.all_eq_true.mp eightBitTest_checked d.val (List.mem_range.mpr d.isLt)
  simp only [eightBitTest, misses, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true, bne_iff_ne, or_assoc] at hit
  letI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 47) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rcases hit with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (nonsquare_of_euler_value d.val h))
  · exact Or.inr (Or.inr (Or.inl (nonsquare_of_euler_value d.val h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (nonsquare_of_euler_value d.val h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (nonsquare_of_euler_value d.val h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (nonsquare_of_euler_value d.val h)))))

end PrimeFactors
