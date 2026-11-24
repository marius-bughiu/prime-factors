import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- Natural encodings of x, y and k for xy = 1 + N*k. The canonical residue
representatives and the quotient all lie in [0,N). -/
abbrev InverseTriple (N : ℕ) :=
  {w : (ZMod N × ZMod N) × Fin N // w.1.1.val * w.1.2.val = 1 + N * w.2.val}

private noncomputable def tripleUnit {N : ℕ} [NeZero N] (w : InverseTriple N) : (ZMod N)ˣ := by
  have h := congrArg (fun t : ℕ => (t : ZMod N)) w.property
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, ZMod.natCast_val,
    ZMod.natCast_self, ZMod.cast_id, zero_mul, add_zero] at h
  exact ⟨w.1.1.1, w.1.1.2, h, (mul_comm ..).trans h⟩

private noncomputable def unitTriple (N : ℕ) [Fact (1 < N)] (u : (ZMod N)ˣ) : InverseTriple N := by
  let x := (u : ZMod N).val
  let y := (↑u⁻¹ : ZMod N).val
  have hp : 0 < N := by have := Fact.out (p := 1 < N); omega
  have hx : x < N := ZMod.val_lt _
  have hy : y < N := ZMod.val_lt _
  have small : x * y < N * N :=
    (Nat.mul_le_mul_right y hx.le).trans_lt (Nat.mul_lt_mul_of_pos_left hy hp)
  have rem : x*y % N = 1 := by
    change (u : ZMod N).val * (↑u⁻¹ : ZMod N).val % N = 1
    rw [← ZMod.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, ZMod.val_one]
  refine ⟨((u, ↑u⁻¹), ⟨x*y/N, (Nat.div_lt_iff_lt_mul hp).mpr small⟩), ?_⟩
  exact (Nat.mod_add_div (x*y) N).symm.trans (by rw [rem])

/-- An inverse and the quotient are forced by x. Thus auxiliary wires for
integer multiplication and division introduce no witness multiplicity. -/
noncomputable def inverseTripleEquivUnits (N : ℕ) [Fact (1 < N)] :
    InverseTriple N ≃ (ZMod N)ˣ where
  toFun := tripleUnit
  invFun := unitTriple N
  left_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change (w.1.1.1.val * w.1.1.2.val) / N = w.1.2.val
      rw [w.property, Nat.add_mul_div_left _ _ (by have := Fact.out (p := 1 < N); omega),
        Nat.div_eq_of_lt (Fact.out (p := 1 < N)), Nat.zero_add]
  right_inv _ := Units.ext rfl

/-- One unweighted exact count yields the classical Euler totient. -/
theorem card_inverseTriples (N : ℕ) [Fact (1 < N)] :
    Fintype.card (InverseTriple N) = N.totient :=
  (Fintype.card_congr (inverseTripleEquivUnits N)).trans (ZMod.card_units_eq_totient N)

/-- For distinct primes, the sum follows by one subtraction from the public
product once the count is available. -/
theorem factorSum_from_inverseTriples {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (different : p ≠ q) [Fact (1 < p*q)] :
    p*q + 1 - Fintype.card (InverseTriple (p*q)) = p+q := by
  rw [card_inverseTriples, Nat.totient_mul ((Nat.coprime_primes hp hq).mpr different),
    Nat.totient_prime hp, Nat.totient_prime hq]
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne_zero
  rw [ha, hb]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  have eqn : (a+1)*(b+1)+1 = (a+1+(b+1)) + a*b := by ring
  rw [eqn, Nat.add_sub_cancel]

set_option maxRecDepth 4096 in
/-- This count enumerates the bounded triples for 15 in the kernel. -/
theorem inverseTriples_15 : Fintype.card (InverseTriple 15) = 8 := by decide +kernel

end PrimeFactors
