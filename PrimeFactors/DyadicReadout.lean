import PrimeFactors.LowFactorBits
import Mathlib.NumberTheory.Multiplicity

/-! The classical decomposition of odd residues modulo 2^k into a sign and a power of 5
makes a single ordinary scalar a reversible tag for the ordered multiplier. Mathlib’s
`Int.two_pow_sub_pow'` supplies the dyadic lifting-the-exponent identity. The digit
lift only squares and multiplies residues and requires no auxiliary counting wires. -/

namespace PrimeFactors

private theorem five_dvd_exp (j d : ℕ) : 2^(j+2) ∣ 5^d-1 ↔ 2^j ∣ d := by
  have lte := Int.two_pow_sub_pow' (x := 5) (y := 1) d (by decide) (by decide)
  have cast : (↑(5^d-1 : ℕ) : ℤ) = 5^d-1 := by
    rw [Nat.cast_sub (Nat.pow_pos (by decide : 0 < 5))]; push_cast; rfl
  have twoVal : emultiplicity (2:ℤ) 4 = 2 := by
    simpa using emultiplicity_pow_self_of_prime Int.prime_two 2
  simp only [one_pow, show (5:ℤ)-1 = 4 by decide, twoVal, ← cast] at lte
  change emultiplicity (↑(2:ℕ):ℤ) ↑(5^d-1 : ℕ) = 2 + emultiplicity (↑(2:ℕ):ℤ) ↑d at lte
  simp only [Int.natCast_emultiplicity] at lte
  rw [pow_dvd_iff_le_emultiplicity, pow_dvd_iff_le_emultiplicity, lte, Nat.cast_add,
    Nat.cast_ofNat, add_comm (j : ℕ∞)]
  exact WithTop.add_le_add_iff_left (by simp)

/-- The exponent's exact period at scalar width j+2. -/
theorem five_power_modEq_iff (j x y : ℕ) : 5^x ≡ 5^y [MOD 2^(j+2)] ↔ x ≡ y [MOD 2^j] := by
  wlog order : x ≤ y generalizing x y
  · rw [Nat.ModEq.comm, Nat.ModEq.comm (a := x), this y x (by omega)]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [pow_add (5:ℕ) x d]
  have cop := Nat.Coprime.pow (j+2) x (by decide : Nat.Coprime 2 5)
  have cancel : 5^x ≡ 5^x*5^d [MOD 2^(j+2)] ↔ 1 ≡ 5^d [MOD 2^(j+2)] :=
    ⟨fun h => Nat.ModEq.cancel_left_of_coprime cop (by simpa using h), fun h => by simpa using h.mul_left (5^x)⟩
  rw [cancel, Nat.modEq_iff_dvd' (Nat.pow_pos (by decide : 0 < 5)), five_dvd_exp,
    Nat.modEq_iff_dvd' (Nat.le_add_right x d), Nat.add_sub_cancel_left]

private structure LiftState where
  exponent : ℕ
  value : ℕ
  jump : ℕ

/-- At stage j the state contains the exponent prefix and the modular powers
5^prefix and 5^(2^j). A mismatch sets exactly the next exponent bit. -/
private def liftFive (m target : ℕ) : ℕ → LiftState
  | 0 => ⟨0, 1%m, 5%m⟩
  | j+1 =>
    let prev := liftFive m target j
    let nextJump := prev.jump*prev.jump % m
    if prev.value % 2^(j+3) = target % 2^(j+3) then
      ⟨prev.exponent, prev.value, nextJump⟩
    else
      ⟨prev.exponent+2^j, prev.value*prev.jump % m, nextJump⟩

private theorem liftFive_spec (m target h j : ℕ) (precision : 2^(j+2) ∣ m)
    (valid : target ≡ 5^h [MOD m]) :
    let state := liftFive m target j
    state.exponent = h % 2^j ∧ state.value = 5^(h % 2^j) % m ∧ state.jump = 5^(2^j) % m := by
  induction j with
  | zero => simp [liftFive, Nat.mod_one]
  | succ j ih =>
    have divides : 2^(j+2) ∣ 2^(j+3) := by rw [pow_succ _ (j+2)]; exact dvd_mul_right _ _
    obtain ⟨prevExp, value, jump⟩ := ih (divides.trans precision)
    have test : 5^(h % 2^j) % m % 2^(j+3) = target % 2^(j+3) ↔ h%2^j = h%2^(j+1) := by
      rw [Nat.mod_mod_of_dvd _ precision, (valid.of_dvd precision : target % _ = _)]
      change Nat.ModEq (2^(j+1+2)) (5^(h % 2^j)) (5^h) ↔ _
      rw [five_power_modEq_iff]
      exact (show h%2^j % 2^(j+1) = h%2^(j+1) ↔ _ by
        rw [Nat.mod_eq_of_lt ((Nat.mod_lt h (by positivity : 0 < 2^j)).trans_le
          (Nat.pow_le_pow_right (by decide) (Nat.le_succ j)))])
    have nextJump : 5^(2^j) % m * (5^(2^j) % m) % m = 5^(2^(j+1)) % m := by
      rw [Nat.mul_mod_mod, Nat.mod_mul_mod, ← pow_add, pow_succ 2 j]; congr 2; omega
    dsimp only; unfold liftFive; simp only [prevExp, value, jump, test]
    split_ifs with bit
    · exact ⟨bit, by rw [bit], nextJump⟩
    · have digit := Nat.mod_two_eq_zero_or_one (h / 2^j)
      have repr := Nat.mod_pow_succ (x := h) (b := 2) (k := j)
      rcases digit with d | d <;> rw [d] at repr <;> simp at repr
      · exact (bit repr.symm).elim
      · exact ⟨repr.symm, by rw [repr, pow_add, Nat.mul_mod_mod, Nat.mod_mul_mod], nextJump⟩

/-- The sign wire is the second bit of the larger input. Its high bits supply
ordinary powers of 5 independently, and bit zero has weight one. -/
noncomputable def signedFiveWeight (k q : ℕ) : ZMod (2^k) :=
  let places := ((2 : ℕ).digits (q/4)).mapIdx (fun i d => d*2^i)
  (if (q/2)%2 = 1 then -1 else 1) * (places.map ((5 : ZMod (2^k)) ^ ·)).prod

private theorem signedFiveWeight_eq (k q : ℕ) : signedFiveWeight k q =
    (if (q/2)%2 = 1 then -1 else 1) * (5 : ZMod (2^k))^(q/4) := by
  have collect (places : List ℕ) : (places.map ((5 : ZMod (2^k)) ^ ·)).prod = 5^places.sum := by
    induction places with
    | nil => simp
    | cons i places ih => simp [ih, pow_add]
  rw [signedFiveWeight, collect, ← Nat.ofDigits_eq_sum_mapIdx, Nat.ofDigits_digits]

/-- No slack register is required after enforcing the order on the two inputs. -/
noncomputable def orderedDyadicReadout (n B k : ℕ) : ℕ :=
  (∑ xy ∈ orderedNontrivialBox n B, signedFiveWeight k xy.2).val

/-- Invert the sign and the high-bit power using only the k-bit scalar. -/
def decodeDyadicWord (k signal : ℕ) : ℕ :=
  let m := 2^k
  let w := signal % m
  let negative := w%4 = 3
  let target := if negative then m-w else w
  let high := (liftFive m target (k-2)).exponent
  ((if negative then 3 else 1) + 4*high) % m

theorem decodeDyadicWord_correct {q k : ℕ} (odd : Odd q) (width : 2 ≤ k) :
    decodeDyadicWord k (signedFiveWeight k q).val = q % 2^k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le width
  rw [Nat.add_comm 2 j]
  let m := 2^(j+2)
  let v := 5^(q/4) % m
  have mEq : m = 4*2^j := by dsimp [m]; rw [pow_add]; ring
  have mp : 0 < m := by dsimp [m]; positivity
  have vl : v < m := Nat.mod_lt _ mp
  have four : 4 ∣ m := mEq ▸ dvd_mul_right _ _
  have vr : v % 4 = 1 := by
    rw [show v = 5^(q/4) % m by rfl, Nat.mod_mod_of_dvd _ four]
    simpa only [Nat.ModEq, one_pow] using (show 5 ≡ 1 [MOD 4] by decide).pow (q/4)
  have mr : m % 4 = 0 := Nat.mod_eq_zero_of_dvd four
  have cast : ((5 : ZMod m) ^ (q/4)).val = v := by
    change _ = 5^(q/4) % m
    rw [← ZMod.val_natCast]; push_cast; rfl
  have log := (liftFive_spec m v (q/4) j (dvd_refl _) (Nat.mod_modEq _ _)).1
  have reconstruct : q % m = q%4 + 4*((q/4)%2^j) := by rw [mEq, Nat.mod_mul]
  have qOdd : q%2=1 := Nat.odd_iff.mp odd
  have val_lt : q%4+4*((q/4)%2^j) < m := reconstruct ▸ Nat.mod_lt _ mp
  rw [decodeDyadicWord, signedFiveWeight_eq]
  change ((if _ then 3 else 1) + 4*(liftFive m _ (j+2-2)).exponent) % m = q%m
  by_cases neg : (q/2)%2=1
  · have low : q%4=3 := by omega
    have wsmall : m-v < m := by omega
    have sign : (m-v)%4=3 := by omega
    simp only [neg, ↓reduceIte, neg_one_mul, ZMod.neg_val', cast, ← show m = 2^(j+2) by rfl, Nat.mod_eq_of_lt wsmall,
      sign, Nat.add_sub_cancel, Nat.sub_sub_self vl.le, log]
    rw [← low, Nat.mod_eq_of_lt val_lt, ← reconstruct]
  · have low : q%4=1 := by omega
    simp only [neg, ↓reduceIte, one_mul, cast, ← show m = 2^(j+2) by rfl, Nat.mod_eq_of_lt vl, vr,
      show ¬ (1:ℕ)=3 by decide, Nat.add_sub_cancel, log]
    rw [← low, Nat.mod_eq_of_lt val_lt, ← reconstruct]

/-- The k-bit ordinary scalar from the ordered multiplier recovers all k low bits. -/
theorem orderedDyadicReadout_decodes {p q B k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p ≤ q) (inside : q < B) (odd : Odd q) (width : 2 ≤ k) :
    decodeDyadicWord k (orderedDyadicReadout (p*q) B k) = q % 2^k := by
  rw [orderedDyadicReadout, orderedNontrivialBox_semiprime hp hq ordered inside,
    Finset.sum_singleton, decodeDyadicWord_correct odd width]

set_option maxRecDepth 10000 in
/-- Check both signs on input-only multiplication boxes. The codes differ from
both decoded words, including the positive-sign example 29 modulo 32. -/
theorem orderedDyadicReadout_examples : orderedDyadicReadout 77 16 4 = 7 ∧ decodeDyadicWord 4 7 = 11 ∧
    orderedDyadicReadout 203 32 5 = 13 ∧ decodeDyadicWord 5 13 = 29 := by
  have box₁ : orderedNontrivialBox 77 16 = {(7,11)} := by decide +kernel
  have box₂ : orderedNontrivialBox 203 32 = {(7,29)} := by decide +kernel
  simp only [orderedDyadicReadout, box₁, box₂, Finset.sum_singleton, signedFiveWeight_eq]
  decide +kernel

end PrimeFactors
