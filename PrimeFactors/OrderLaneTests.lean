import PrimeFactors.PowerSignature
import Mathlib.RingTheory.Coprime.Lemmas
import PrimeFactors.Pratt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

namespace PrimeFactors.OrderLaneTests

/-- On a residue pair with product N, the candidate sum 2h is equivalent to
a square condition on either factor. Cancellation uses only its being a unit. -/
theorem trace_iff_square {R N u v h : ℤ} (unit : IsCoprime R u)
    (prod : u*v ≡ N [ZMOD R]) :
    u+v ≡ 2*h [ZMOD R] ↔ (u-h)^2 ≡ h^2-N [ZMOD R] := by
  rw [Int.modEq_iff_dvd] at prod ⊢
  rw [Int.modEq_iff_dvd]
  have identity : h^2-N-(u-h)^2 = u*(2*h-(u+v))-(N-u*v) := by ring
  rw [identity, dvd_sub_left prod]
  exact ⟨fun d => dvd_mul_of_dvd_right d u, unit.dvd_of_dvd_mul_left⟩

/-- At a public square root of N modulo m² an entire congruence class
modulo m shares one sum modulo m². -/
theorem square_center_block {m N u v h : ℤ} (unit : IsCoprime (m^2) u)
    (prod : u*v ≡ N [ZMOD m^2]) (center : h^2 ≡ N [ZMOD m^2]) :
    u+v ≡ 2*h [ZMOD m^2] ↔ u ≡ h [ZMOD m] := by
  rw [trace_iff_square unit prod]
  have zero : h^2-N ≡ 0 [ZMOD m^2] := by simpa using center.sub_right N
  have changeTarget : (u-h)^2 ≡ h^2-N [ZMOD m^2] ↔ (u-h)^2 ≡ 0 [ZMOD m^2] :=
    ⟨fun x => x.trans zero, fun x => x.trans zero.symm⟩
  rw [changeTarget, Int.modEq_zero_iff_dvd, Int.pow_dvd_pow_iff two_ne_zero]
  exact (Int.modEq_iff_dvd (a := h) (b := u)).symm.trans Int.modEq_comm

/-- Number of distinct remainders modulo m² in this centered block. -/
theorem square_center_card (m h : ℕ) (pos : 0 < m) :
    ((Finset.range (m^2)).filter (fun u => u ≡ h [MOD m])).card = m := by
  conv_rhs => rw [← Finset.card_range m]
  apply Finset.card_bij (fun u _ => u/m)
  · intro u hu
    have bound := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
    exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul pos).mpr (by simpa [pow_two] using bound))
  · intro u hu v hv div
    have rem := (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
    change u%m = v%m at rem
    have fromU := Nat.mod_add_div u m
    rwa [rem,div,Nat.mod_add_div,eq_comm] at fromU
  · intro t ht
    have small := Finset.mem_range.mp ht
    have rem := Nat.mod_lt h pos
    have bounded := Nat.mul_le_mul_left m (Nat.succ_le_of_lt small)
    refine ⟨h%m+m*t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩, ?_⟩
    · rw [pow_two]
      rw [Nat.mul_succ] at bounded
      omega
    · simp [Nat.ModEq]
    · simp [Nat.add_mul_div_left _ _ pos, Nat.div_eq_of_lt rem]

/-- A single table look-up tests the factor sum at stride R, irrespective of
how many residue pairs have the same sum modulo R. -/
theorem strided_match_iff {G : Type*} [CommGroup G] (a target : G) (L R i b j : ℕ) :
    (a^R)^j = target / (a^L * ((a^R)^b)^i) ↔ a^(L+R*(b*i+j)) = target := by
  simp only [eq_div_iff_mul_eq'', pow_mul, pow_add]
  simp only [mul_assoc, mul_left_comm, mul_comm]

/-- Every balanced pair whose sum occurs in a searched block produces the
public power match at the corresponding table coordinates. -/
theorem true_pair_hits {p q L R i b j : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (a : (ZMod (p*q))ˣ) (index : p+q = L+R*(b*i+j)) :
    (a^R)^j = a^(p*q+1) / (a^L * ((a^R)^b)^i) := by
  rw [strided_match_iff, ← index]
  exact unit_pow_factorSum hp hq hne a

private noncomputable def passesSquareSieve (D : ℕ) : Bool :=
  [3,5,7,11,13,17,23].all fun m => (List.range m).any fun r => r^2%m == D%m

private theorem passesSquareSieve_square (r : ℕ) : passesSquareSieve (r^2) = true := by
  apply List.all_eq_true.mpr
  intro m hm
  have pos : 0 < m := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact List.any_eq_true.mpr ⟨r%m, List.mem_range.mpr (Nat.mod_lt _ pos),
    beq_iff_eq.mpr ((Nat.mod_modEq r m).pow 2)⟩

private noncomputable def exampleCandidates (L : ℕ) : List ℕ :=
  (List.range 38).filter fun j => passesSquareSieve ((L+65536*j)^2-4*422240038488377)

set_option maxRecDepth 8192 in
/-- A small square-residue sieve rejects every incorrect index in these two blocks.
The remaining index has the displayed square discriminant and the correct product. -/
theorem example_blocks :
    811^2 % 65536 = 422240038488377 % 65536 ∧
    31957^2 % 65536 = 422240038488377 % 65536 ∧
    exampleCandidates 41158230 = [12] ∧ exampleCandidates 41154986 = [] ∧
    41944662^2-4*422240038488377 = 8390144^2 ∧
    16777259*25167403 = 422240038488377 ∧ 16777259+25167403 = 41158230+12*65536 := by
  decide +kernel

private theorem prime_2 : Nat.Prime 2 := by
  norm_num

private theorem prime_23 : Nat.Prime 23 := by
  norm_num

private theorem prime_103 : Nat.Prime 103 := by
  norm_num

private theorem prime_3 : Nat.Prime 3 := by
  norm_num

private theorem prime_3541 : Nat.Prime 3541 := by norm_num

private theorem prime_16777259 : Nat.Prime 16777259 := by
  apply prime_of_lucas_cover (2 : ZMod 16777259) (ps := [2, 23, 103, 3541])
  · exact (Covers.cons 1 prime_2 (Covers.cons 1 prime_23 (Covers.cons 1 prime_103 (Covers.cons 1 prime_3541 covers_one))))
  · change (2 : ZMod 16777259) ^ 16777258 = 1
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16777259) ^ 8388629 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 16777259) ^ 729446 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 16777259) ^ 162886 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 16777259) ^ 4738 ≠ 1
      reduce_mod_char
      decide

private theorem prime_13 : Nat.Prime 13 := by
  norm_num

private theorem prime_35851 : Nat.Prime 35851 := by norm_num

private theorem prime_25167403 : Nat.Prime 25167403 := by
  apply prime_of_lucas_cover (2 : ZMod 25167403) (ps := [2, 3, 13, 35851])
  · exact (Covers.cons 1 prime_2 (Covers.cons 3 prime_3 (Covers.cons 1 prime_13 (Covers.cons 1 prime_35851 covers_one))))
  · change (2 : ZMod 25167403) ^ 25167402 = 1
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25167403) ^ 12583701 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 25167403) ^ 8389134 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 25167403) ^ 1935954 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 25167403) ^ 702 ≠ 1
      reduce_mod_char
      decide

theorem example_primes : Nat.Prime 16777259 ∧ Nat.Prime 25167403 :=
  ⟨prime_16777259,prime_25167403⟩

end PrimeFactors.OrderLaneTests
