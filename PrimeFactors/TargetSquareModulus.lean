import PrimeFactors.GapStride
import PrimeFactors.Pratt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

namespace PrimeFactors.TargetSquareModulus

set_option exponentiation.threshold 2048
set_option maxRecDepth 8192

private def first : ℕ := 6308*3^638+1
private def second : ℕ := 3066*5^436+1

private theorem first_prime : first.Prime := by
  apply prime_of_lucas_cover (7 : ZMod first) (ps := [2,3,19,83])
  · exact Covers.cons 2 Nat.prime_two (Covers.cons 638 Nat.prime_three
      (Covers.cons 1 (by norm_num : Nat.Prime 19) (Covers.cons 1 (by norm_num : Nat.Prime 83) covers_one)))
  · simp only [first, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;>
      simp only [first,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,Nat.reduceDiv] <;>
      reduce_mod_char <;> decide

private theorem second_prime : second.Prime := by
  apply prime_of_lucas_cover (3 : ZMod second) (ps := [2,3,5,7,73])
  · exact Covers.cons 1 Nat.prime_two (Covers.cons 1 Nat.prime_three
      (Covers.cons 436 (by norm_num : Nat.Prime 5) (Covers.cons 1 (by norm_num : Nat.Prime 7)
        (Covers.cons 1 (by norm_num : Nat.Prime 73) covers_one))))
  · simp only [second,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      simp only [second,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,Nat.reduceDiv] <;>
      reduce_mod_char <;> decide

/-- A real target-size pair realizes the least possible common divisor
of the two prime-square predecessors. -/
theorem exists_sharp_pair :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧
      2^1023≤p ∧ p<2^1024 ∧ 2^1023≤q ∧ q<2^1024 ∧
      2^2047≤p*q ∧ p*q<2^2048 ∧ Nat.gcd (p^2-1) (q^2-1)=24 :=
  ⟨first,second,first_prime,second_prime,by decide +kernel⟩

/-- Exactly the divisors of 24 work on both primes of every promised
2,048-bit input. This restricts the universal square identity. -/
theorem uniform_iff (m : ℕ) :
    (∀ p q : ℕ, p.Prime → q.Prime → p≠q →
      2^1023≤p → p<2^1024 → 2^1023≤q → q<2^1024 →
      2^2047≤p*q → p*q<2^2048 → m ∣ p^2-1 ∧ m ∣ q^2-1) ↔ m ∣ 24 := by
  constructor
  · intro all
    obtain ⟨p,q,pp,qp,ne,pl,ph,ql,qh,low,high,gcd⟩ := exists_sharp_pair
    obtain ⟨a,b⟩ := all p q pp qp ne pl ph ql qh low high
    exact gcd ▸ Nat.dvd_gcd a b
  · intro dvd p q pp qp _ pl _ ql _ _ _
    have unit (r : ℕ) (rp : r.Prime) (big : 2^1023≤r) : m ∣ r^2-1 := by
      have six : 6<r := lt_of_lt_of_le (by decide +kernel : 6<(2:ℕ)^1023) big
      have cop := rp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide : 0<6) six)
      exact dvd.trans ((Nat.modEq_iff_dvd' (by nlinarith [rp.one_lt] : 1≤r^2)).mp
        (square_mod_twentyfour cop).symm)
    exact ⟨unit p pp pl,unit q qp ql⟩

end PrimeFactors.TargetSquareModulus
