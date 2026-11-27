import PrimeFactors.ResidueCount
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! For odd factors of N, an odd anchor a with a² < 4N gives the positive
modulus D = 4N − a². Both Jacobi symbols (S−a | D) and (S+a | D) for the
true sum S are nonnegative. Over a full period this halves the rows of a
symmetric square-discriminant wheel except where both symbols vanish. -/

namespace PrimeFactors.ReciprocalSumCharacter

open ZMod

private theorem reciprocity {d n : ℕ} (hd : d % 4 = 3) (hn : Odd n) :
    jacobiSym (n : ℤ) d = jacobiSym (-(d : ℤ)) n := by
  rw [jacobiSym.neg _ hn]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn) with h | h
  · rw [χ₄_nat_one_mod_four h, one_mul]
    exact jacobiSym.quadratic_reciprocity_one_mod_four h (Nat.odd_iff.mpr (by omega))
  · rw [χ₄_nat_three_mod_four h, neg_one_mul]
    exact jacobiSym.quadratic_reciprocity_three_mod_four h hd

theorem from_norm {d n : ℕ} {u : ℤ} (hd : d % 4 = 3) (hn : Odd n)
    (divides : (n : ℤ) ∣ u^2 + d) : 0 ≤ jacobiSym (n : ℤ) d := by
  rw [reciprocity hd hn]
  have modEq : (-(d : ℤ)) % n = (u^2) % n := by
    apply (ZMod.intCast_eq_intCast_iff' _ _ _).mp
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
    simpa using divides
  rw [jacobiSym.mod_left' modEq, jacobiSym.pow_left]
  exact sq_nonneg _

/-- An even integer sum with square discriminant satisfies both public signs,
including after scaling the sum and its square root by any positive multiplier. -/
theorem square_sum {N s a : ℕ} {u : ℤ} (hs : Even s) (ha : Odd a)
    (below : a^2 < 4*N) (disc : (s : ℤ)^2 - 4*N = u^2) :
    0 ≤ jacobiSym ((s-a : ℕ) : ℤ) (4*N-a^2) ∧
    0 ≤ jacobiSym ((s+a : ℕ) : ℤ) (4*N-a^2) := by
  have bound : (a:ℤ)^2 < 4*N := by exact_mod_cast below
  have le : a ≤ s := by
    zify
    nlinarith [sq_nonneg u, (Nat.cast_nonneg a : 0 ≤ (a:ℤ)), (Nat.cast_nonneg s : 0 ≤ (s:ℤ))]
  have hd : (4*N-a^2) % 4 = 3 := by
    obtain ⟨k,hk⟩ := ha
    have e : a^2 = 4*(k*k+k)+1 := by rw [hk]; ring
    omega
  have oddMinus : Odd (s-a) := by
    simp only [Nat.even_iff, Nat.odd_iff] at hs ha ⊢
    omega
  have oddPlus : Odd (s+a) := by
    simp only [Nat.even_iff, Nat.odd_iff] at hs ha ⊢
    omega
  have eqn : u^2 + ((4*N-a^2 : ℕ) : ℤ) =
      ((s-a : ℕ) : ℤ) * ((s+a : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub below.le, Nat.cast_sub le]
    nlinarith
  constructor
  · apply from_norm (u := u) hd oddMinus
    rw [eqn]
    exact dvd_mul_right ..
  · apply from_norm (u := u) hd oddPlus
    rw [eqn]
    exact dvd_mul_left ..

/-- Product-only necessary test at both offsets. It applies to any odd
factorization, without primality, size balance or a factorization of D. -/
theorem factor_sum {p q a : ℕ} (hp : Odd p) (hq : Odd q) (ha : Odd a)
    (below : a^2 < 4*(p*q)) :
    0 ≤ jacobiSym ((p+q-a : ℕ) : ℤ) (4*(p*q)-a^2) ∧
    0 ≤ jacobiSym ((p+q+a : ℕ) : ℤ) (4*(p*q)-a^2) := by
  apply square_sum (u := (p:ℤ)-q) (hp.add_odd hq) ha below
  push_cast
  ring

/-- Jacobi character on residue classes. -/
noncomputable def sign {d : ℕ} (x : ZMod d) : ℤ := jacobiSym x.valMinAbs d

theorem sign_cast {d : ℕ} (x : ℤ) : sign (x : ZMod d) = jacobiSym x d := by
  apply jacobiSym.mod_left'
  exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp (ZMod.coe_valMinAbs _)

theorem sign_mul {d : ℕ} (x y : ZMod d) : sign (x*y) = sign x * sign y := by
  conv_lhs => rw [← x.coe_valMinAbs, ← y.coe_valMinAbs, ← Int.cast_mul, sign_cast]
  exact jacobiSym.mul_left ..

theorem sign_neg {d : ℕ} (hd : d % 4 = 3) (x : ZMod d) :
    sign (-x) = -sign x := by
  conv_lhs => rw [← x.coe_valMinAbs, ← Int.cast_neg, sign_cast]
  rw [jacobiSym.neg _ (Nat.odd_iff.mpr (by omega)), χ₄_nat_three_mod_four hd, neg_one_mul]
  rfl

/-- The test retains possible zeros of either Jacobi symbol. -/
def Passes {d : ℕ} (a s : ZMod d) : Prop := 0 ≤ sign (s-a) ∧ 0 ≤ sign (s+a)

/-- Both symbols vanish. These rows and their negatives pass the new test. -/
def BothZero {d : ℕ} (a s : ZMod d) : Prop := sign (s-a) = 0 ∧ sign (s+a) = 0

noncomputable instance {d : ℕ} (a s : ZMod d) : Decidable (Passes a s) :=
  Classical.propDecidable _
noncomputable instance {d : ℕ} (a s : ZMod d) : Decidable (BothZero a s) :=
  Classical.propDecidable _

private theorem signs {d : ℕ} {a s : ZMod d} (sq : IsSquare (s^2-a^2)) :
    0 ≤ sign (s-a) * sign (s+a) := by
  rw [← sign_mul, show (s-a)*(s+a) = s^2-a^2 by ring]
  obtain ⟨u,hu⟩ := sq
  rw [hu, sign_mul]
  exact mul_self_nonneg _

private theorem reflection {d : ℕ} (hd : d % 4 = 3) {a s : ZMod d}
    (sq : IsSquare (s^2-a^2)) :
    ¬ Passes a (-s) ↔ Passes a s ∧ ¬ BothZero a s := by
  have prod := signs sq
  simp only [Passes, BothZero, show -s-a = -(s+a) by ring,
    show -s+a = -(s-a) by ring, sign_neg hd]
  rcases jacobiSym.trichotomy (s-a).valMinAbs d with h | h | h <;>
    rcases jacobiSym.trichotomy (s+a).valMinAbs d with k | k | k <;>
    change sign (s-a) = _ at h <;> change sign (s+a) = _ at k <;>
    simp_all

/-- Exact count for any negation-symmetric wheel of square-discriminant
candidates modulo D. Under 4N ≡ a² mod D the old discriminant is s²−a².
The count concerns a whole wheel, without a distribution hypothesis. -/
theorem wheel_count {d : ℕ} (hd : d % 4 = 3) (a : ZMod d) (W : Finset (ZMod d))
    (symm : ∀ s ∈ W, -s ∈ W) (square : ∀ s ∈ W, IsSquare (s^2-a^2)) :
    2 * (W.filter (Passes a)).card = W.card + (W.filter (BothZero a)).card := by
  classical
  have paired : ((W.filter (Passes a)).filter (fun s => ¬ BothZero a s)).card =
      (W.filter (fun t => ¬ Passes a t)).card := by
    refine Finset.card_bij' (fun s _ => -s) (fun t _ => -t) ?_ ?_ ?_ ?_
    · intro s hs
      obtain ⟨⟨hs, hpass⟩, hzero⟩ := (Finset.mem_filter.mp hs).imp_left Finset.mem_filter.mp
      exact Finset.mem_filter.mpr ⟨symm s hs, (reflection hd (square s hs)).mpr ⟨hpass,hzero⟩⟩
    · intro t ht
      obtain ⟨ht, hbad⟩ := Finset.mem_filter.mp ht
      have h := (reflection hd (square (-t) (symm t ht))).mp (by simpa using hbad)
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨symm t ht,h.1⟩,h.2⟩
    · simp
    · simp
  have zz : (W.filter (Passes a)).filter (BothZero a) = W.filter (BothZero a) := by
    ext s
    simp only [Finset.mem_filter, Passes, BothZero]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · rintro ⟨hw,h₁,h₂⟩
      exact ⟨⟨hw,by omega,by omega⟩,h₁,h₂⟩
  have h₁ := Finset.filter_card_add_filter_neg_card_eq_card (s := W) (Passes a)
  have h₂ := Finset.filter_card_add_filter_neg_card_eq_card (s := W.filter (Passes a)) (BothZero a)
  rw [zz, paired] at h₂
  omega

/-- No exceptional row occurs for a prime modulus when the anchor is nonzero. -/
theorem prime_wheel_count {d : ℕ} [Fact d.Prime] (hd : d % 4 = 3)
    {a : ZMod d} (ha : a ≠ 0) (W : Finset (ZMod d)) (symm : ∀ s ∈ W, -s ∈ W)
    (square : ∀ s ∈ W, IsSquare (s^2-a^2)) :
    2 * (W.filter (Passes a)).card = W.card := by
  have vanishes (x : ZMod d) : sign x = 0 ↔ x = 0 := by
    rw [sign, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff, ZMod.coe_valMinAbs]
  have two : (2 : ZMod d) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
  have empty : W.filter (BothZero a) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro s _ ⟨h,k⟩
    have eq := sub_eq_zero.mp ((vanishes _).mp h)
    subst s
    exact (mul_ne_zero two ha) (by simpa [two_mul] using (vanishes _).mp k)
  simpa [empty] using wheel_count hd a W symm square

/-- The ordinary prime sum wheel has (d+1)/2 classes, since the product
is a nonzero square. Adding the two reciprocal signs leaves (d+1)/4. -/
theorem prime_sum_count {d : ℕ} [Fact d.Prime] (hd : d % 4 = 3)
    {a n : ZMod d} (ha : a ≠ 0) (anchor : 4*n = a^2) :
    ((factorSumResidues d n).filter (Passes a)).card = (d+1)/4 := by
  have odd : d ≠ 2 := by omega
  have two : (2 : ZMod d) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have hn : n ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at anchor
    exact (pow_ne_zero 2 ha) anchor.symm
  have nsq : IsSquare n := by
    refine ⟨a/2, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero two two)]
    linear_combination anchor
  have mem (s : ZMod d) : s ∈ factorSumResidues d n ↔ IsSquare (s^2-a^2) := by
    rw [mem_factorSumResidues_iff _ hn, admissibleSum_iff_isSquare odd, anchor]
  have half := prime_wheel_count hd ha (factorSumResidues d n)
    (fun s hs => (mem _).mpr (by simpa only [neg_sq] using (mem s).mp hs))
    (fun s hs => (mem s).mp hs)
  rw [card_factorSumResidues_of_square d odd n hn nsq] at half
  omega

/-- For a prime, the two signs can be tabulated as two translations of the
same quadratic-residue mask. Their conjunction implies the old square test. -/
theorem prime_passes_iff {d : ℕ} [Fact d.Prime] (a s : ZMod d) :
    Passes a s ↔ IsSquare (s-a) ∧ IsSquare (s+a) := by
  have criterion (x : ZMod d) : 0 ≤ sign x ↔ IsSquare x := by
    have h := ZMod.nonsquare_iff_jacobiSym_eq_neg_one (p := d) (a := x.valMinAbs)
    rw [ZMod.coe_valMinAbs] at h
    change 0 ≤ jacobiSym x.valMinAbs d ↔ _
    rcases jacobiSym.trichotomy x.valMinAbs d with hz | hz | hz <;>
      simp_all
  exact and_congr (criterion _) (criterion _)

/-- Cardinality when evaluating only the two new signs on an entire prime
period. The ordinary discriminant test at this prime can be omitted. -/
theorem prime_period {d : ℕ} [Fact d.Prime] (hd : d % 4 = 3)
    {a : ZMod d} (ha : a ≠ 0) :
    (Finset.univ.filter (Passes a)).card = (d+1)/4 := by
  have odd : d ≠ 2 := by omega
  have two : (2 : ZMod d) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  let n := (a/2)^2
  have anchor : 4*n = a^2 := by dsimp [n]; field_simp; ring
  have hn : n ≠ 0 := pow_ne_zero _ (div_ne_zero ha two)
  have same : Finset.univ.filter (Passes a) = (factorSumResidues d n).filter (Passes a) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun hs => ⟨?_,hs⟩, And.right⟩
    rw [mem_factorSumResidues_iff d hn, admissibleSum_iff_isSquare odd, anchor,
      show s^2-a^2 = (s-a)*(s+a) by ring]
    exact ((prime_passes_iff a s).mp hs).1.mul ((prime_passes_iff a s).mp hs).2
  rw [same, prime_sum_count hd ha anchor]

/-- In the repository's 34387 example, the earlier 3,5,7 and mod-4 wheel
admits both 388 and 392. The closest odd anchor below 2√34387 is 369.
The true sum passes with a zero on its lower offset; the false sum fails
on its upper offset. All four symbol values are checked by reciprocity. -/
theorem worked_example :
    137 * 251 = (34387 : ℕ) ∧ 137 + 251 = (388 : ℕ) ∧
    4 * 34387 - 369^2 = (1387 : ℕ) ∧ 4 * 34387 < (371^2 : ℕ) ∧
    jacobiSym (388-369) 1387 = 0 ∧ jacobiSym (388+369) 1387 = 1 ∧
    jacobiSym (392-369) 1387 = 1 ∧ jacobiSym (392+369) 1387 = -1 := by
  norm_num

/-- An 18-bit product with two nine-bit primes. Among parity-compatible sums
738, 742, …, 774, the wheel modulo 105 retains exactly these three. Each even
passes the ordinary square test modulo 105·691. The two-offset test at the
closest odd anchor 735 leaves only the true sum 770. -/
theorem strict_example :
    Nat.Prime 271 ∧ Nat.Prime 499 ∧ 271*499 = (135229 : ℕ) ∧
    4*135229-735^2 = (691 : ℕ) ∧ 4*135229 < (737^2 : ℕ) ∧ Nat.Prime 691 ∧
    (((List.range 10).map (fun i => 738+4*i)).filter (fun s =>
      (List.range 105).any (fun x => x^2 % 105 == (s^2-4*135229) % 105)))
        = [746,766,770] ∧
    8325^2 % (105*691) = (746^2-4*135229 : ℕ) % (105*691) ∧
    8115^2 % (105*691) = (766^2-4*135229 : ℕ) % (105*691) ∧
    228^2 = (770^2-4*135229 : ℕ) ∧ 271+499 = (770 : ℕ) ∧
    jacobiSym (746-735) 691 = -1 ∧ jacobiSym (746+735) 691 = -1 ∧
    jacobiSym (766-735) 691 = -1 ∧ jacobiSym (766+735) 691 = -1 ∧
    jacobiSym (770-735) 691 = 1 ∧ jacobiSym (770+735) 691 = 1 := by
  have candidates : (((List.range 10).map (fun i => 738+4*i)).filter (fun s =>
      (List.range 105).any (fun x => x^2 % 105 == (s^2-4*135229) % 105))) =
      [746,766,770] := by decide +kernel
  rw [candidates]
  norm_num
  decide +kernel

end PrimeFactors.ReciprocalSumCharacter
