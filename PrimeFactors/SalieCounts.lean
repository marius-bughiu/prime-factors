import PrimeFactors.DivisorSample
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace PrimeFactors

/-- A public test selecting one orientation of a mixed square root at frequency `t`. -/
def salieSelected {N : ℕ} (t y : ZMod N) : Prop :=
  y ^ 2 = t ^ 2 ∧ y ≠ t ∧ y ≠ -t ∧ y.val < (-y).val

noncomputable instance {N : ℕ} (t y : ZMod N) : Decidable (salieSelected t y) :=
  Classical.propDecidable _

private theorem salieUnit_ne_neg {ℓ : ℕ} [Fact ℓ.Prime] (odd : ℓ ≠ 2) {x : ZMod ℓ} (unit : IsUnit x) :
    x ≠ -x := by
  have neq : (-1 : ZMod ℓ) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two
    (by simpa only [ZMod.ringChar_zmod_n] using odd)
  intro h
  apply neq
  exact unit.mul_right_cancel (by simpa using h.symm : (-1 : ZMod ℓ) * x = 1 * x)

/-- The scaling frequency and modulus specify a unique oriented, nonpublic root. -/
theorem salieSelected_unique {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (cp : p.Coprime q)
    (pOdd : p ≠ 2) (qOdd : q ≠ 2) [NeZero (p*q)] (t : (ZMod (p*q))ˣ) :
    ∃! y, salieSelected (t : ZMod (p*q)) y := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  let e := ZMod.chineseRemainder cp
  let T := e (t : ZMod (p*q))
  let r := e.symm (T.1, -T.2)
  have er : e r = (T.1, -T.2) := e.apply_symm_apply _
  have eT : e (t : ZMod (p*q)) = T := rfl
  have P : T.1 ≠ -T.1 := salieUnit_ne_neg pOdd
    (t.isUnit.map (((RingHom.fst (ZMod p) (ZMod q)).comp e.toRingHom).toMonoidHom))
  have Q : T.2 ≠ -T.2 := salieUnit_ne_neg qOdd
    (t.isUnit.map (((RingHom.snd (ZMod p) (ZMod q)).comp e.toRingHom).toMonoidHom))
  have square_iff (y : ZMod (p*q)) : y^2 = (t : ZMod (p*q))^2 ↔
      y = t ∨ y = -↑t ∨ y = r ∨ y = -r := by
    simp only [← e.injective.eq_iff, map_pow, map_neg, er, eT, Prod.ext_iff,
      Prod.fst_neg, Prod.snd_neg, neg_neg]
    change ((e y).1 ^ 2 = T.1 ^ 2 ∧ (e y).2 ^ 2 = T.2 ^ 2) ↔ _
    simp only [sq_eq_sq_iff_eq_or_eq_neg]
    tauto
  have rt : r ≠ t := fun h => Q (by simpa only [er, eT] using (congrArg Prod.snd (congrArg e h)).symm)
  have rnt : r ≠ -↑t := fun h => P (by simpa only [er, map_neg, eT] using congrArg Prod.fst (congrArg e h))
  have rnr : r ≠ -r := fun h => P (by simpa only [er, map_neg] using congrArg Prod.fst (congrArg e h))
  have poss (y : ZMod (p*q)) : salieSelected (↑t) y ↔
      (y = r ∨ y = -r) ∧ y.val < (-y).val := by
    rw [salieSelected, square_iff]
    have nrt : -r ≠ ↑t := fun h => rnt (neg_eq_iff_eq_neg.mp h)
    have nrnt : -r ≠ -↑t := fun h => rt (neg_inj.mp h)
    constructor
    · rintro ⟨h | h | h | h, a, b, v⟩
      · exact (a h).elim
      · exact (b h).elim
      · exact ⟨Or.inl h, v⟩
      · exact ⟨Or.inr h, v⟩
    · rintro ⟨rfl | rfl, v⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), rt, rnt, v⟩
      · exact ⟨Or.inr (Or.inr (Or.inr rfl)), nrt, nrnt, v⟩
  have diff : r.val ≠ (-r).val := fun h => rnr (ZMod.val_injective _ h)
  rcases lt_or_gt_of_ne diff with h | h
  · refine ⟨r, (poss _).2 ⟨Or.inl rfl, h⟩, ?_⟩
    intro y hy
    rcases (poss y).1 hy with ⟨h' | h', hy⟩
    · exact h'
    · subst y; simp only [neg_neg] at hy; omega
  · refine ⟨-r, (poss _).2 ⟨Or.inr rfl, by simpa using h⟩, ?_⟩
    intro y hy
    rcases (poss y).1 hy with ⟨h' | h', hy⟩
    · subst y; omega
    · exact h'

/-- The orientation is a comparison with a public integer threshold. -/
theorem salieSelected_half {N : ℕ} [NeZero N] (t y : ZMod N) :
    salieSelected t y ↔ y^2 = t^2 ∧ y ≠ t ∧ y ≠ -t ∧ 0 < y.val ∧ 2*y.val < N := by
  by_cases hy : y = 0
  · subst y; simp [salieSelected]
  letI : NeZero y := ⟨hy⟩
  have positive : 0 < y.val := Nat.pos_of_ne_zero (fun h => hy (ZMod.val_injective _ (by simpa using h)))
  have lt := ZMod.val_lt y
  have cmp : y.val < N - y.val ↔ 0 < y.val ∧ 2*y.val < N := by omega
  rw [salieSelected, ZMod.val_neg_of_ne_zero, cmp]

/-- All tests can be carried out on ordinary nonnegative representatives. -/
theorem salieSelected_nat {N t y : ℕ} [NeZero N] (ht : t < N) (unitPos : 0 < t) (hy : y < N) :
    salieSelected (t : ZMod N) (y : ZMod N) ↔
      y^2 % N = t^2 % N ∧ y ≠ min t (N-t) ∧ 0 < y ∧ 2*y < N := by
  rw [salieSelected_half]
  have htval := ZMod.val_natCast_of_lt ht
  have hyval := ZMod.val_natCast_of_lt hy
  letI : NeZero (t : ZMod N) := ⟨fun h => by
    have e := congrArg ZMod.val h
    simp only [htval, ZMod.val_zero] at e
    omega⟩
  have eq : (y : ZMod N) = t ↔ y = t := by
    rw [← (ZMod.val_injective N).eq_iff, hyval, htval]
  have neg : (y : ZMod N) = - (t : ZMod N) ↔ y = N-t := by
    rw [← (ZMod.val_injective N).eq_iff, hyval, ZMod.val_neg_of_ne_zero, htval]
  rw [← Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff]
  simp only [ne_eq, eq, neg, hyval]
  change (_ % _ = _ % _ ∧ _) ↔ _
  rcases le_total t (N-t) with h | h
  · rw [min_eq_left h]; omega
  · rw [min_eq_right h]; omega

/-- On the selected fibre, a local weight returns its value on the sole witness. -/
theorem salieSelected_sum {N : ℕ} [NeZero N] {t x : ZMod N}
    (unique : ∃! y, salieSelected t y) (hx : salieSelected t x)
    {A : Type*} [AddCommMonoid A] (f : ZMod N → A) :
    (∑ y : ZMod N, if salieSelected t y then f y else 0) = f x := by
  have iff (y : ZMod N) : salieSelected t y ↔ y = x :=
    ⟨fun h => unique.unique h hx, fun h => h ▸ hx⟩
  simp_rw [iff]
  simp

/-- A further public predicate can be queried with just a parity count. -/
theorem salieSelected_parity {N : ℕ} [NeZero N] {t x : ZMod N}
    (unique : ∃! y, salieSelected t y) (hx : salieSelected t x)
    (P : ZMod N → Prop) [DecidablePred P] :
    (∑ y : ZMod N, if salieSelected t y ∧ P y then (1 : ZMod 2) else 0) =
      if P x then 1 else 0 := by
  simpa only [ite_and] using salieSelected_sum unique hx (fun y => if P y then (1 : ZMod 2) else 0)

/-- Free slack values below the selected prefix return its exact digits in one contraction. -/
theorem salieSelected_prefix {N : ℕ} [NeZero N] {t x : ZMod N}
    (unique : ∃! y, salieSelected t y) (hx : salieSelected t x)
    (width cap : ℕ) (fits : x.val / width < cap) :
    (∑ y : ZMod N, if salieSelected t y then
      ((Finset.range cap).filter (· < y.val / width)).card else 0) % cap = x.val / width := by
  rw [salieSelected_sum unique hx]
  have eq : (Finset.range cap).filter (· < x.val / width) = Finset.range (x.val / width) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [eq, Finset.card_range, Nat.mod_eq_of_lt fits]

/-- The prefix of an `n`-bit representative fits in the promised `d`-bit count. -/
theorem saliePrefix_fits {N n d : ℕ} [NeZero N] (x : ZMod N) (size : N ≤ 2^n) (hd : d ≤ n) :
    x.val / 2^(n-d) < 2^d := by
  apply Nat.div_lt_of_lt_mul
  rw [← pow_add, Nat.sub_add_cancel hd]
  exact (ZMod.val_lt x).trans_le size

/-- The exact modular-square predicate has a unique quotient of the same input width. -/
theorem salieSquare_quotient {N y c : ℕ} (hy : y < N) (hc : c < N) :
    y^2 % N = c ↔ ∃! k, k < N ∧ y^2 = k*N+c := by
  have pos : 0 < N := by omega
  constructor
  · intro h
    have lt : y^2/N < N := Nat.div_lt_of_lt_mul (by
      simpa only [← sq] using Nat.pow_lt_pow_left hy (by decide : 2 ≠ 0))
    have eq : y^2 = y^2/N*N+c := by
      rw [← h, Nat.mul_comm (y^2/N) N, Nat.add_comm (N * (y^2 / N)) _, Nat.mod_add_div]
    refine ⟨y^2/N, ⟨lt, eq⟩, ?_⟩
    intro k hk
    exact Nat.eq_of_mul_eq_mul_right pos (by omega)
  · rintro ⟨k, ⟨_, eq⟩, _⟩
    rw [eq, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hc]

private theorem salieCosine_lipschitz (a b : ℝ) : |Real.cos a - Real.cos b| ≤ |a-b| := by
  rw [Real.cos_sub_cos, abs_mul, abs_mul]
  calc
    _ ≤ (2 * 1) * |(a-b)/2| := mul_le_mul
      (by simpa using Real.abs_sin_le_one ((a+b)/2)) Real.abs_sin_le_abs (abs_nonneg _) (by norm_num)
    _ = _ := by rw [abs_div]; norm_num; ring

/-- Replacing the hidden root by an interval midpoint costs at most `2π*width/N`
in the normalized sample, which contains twice its cosine. -/
theorem saliePrefix_cosine_error {y lo width N : ℝ} (hN : 0 < N)
    (lower : lo ≤ y) (upper : y ≤ lo + width) :
    |2 * Real.cos (2 * Real.pi * y / N) -
      2 * Real.cos (2 * Real.pi * (lo + width/2) / N)| ≤ 2 * Real.pi * width / N := by
  let a := 2 * Real.pi / N
  have apos : 0 ≤ a := by dsimp [a]; positivity
  have distance : |y - (lo + width/2)| ≤ width/2 := abs_le.mpr (by constructor <;> linarith)
  have lip := salieCosine_lipschitz (a*y) (a*(lo+width/2))
  rw [← mul_sub, abs_mul, abs_of_nonneg apos] at lip
  have bound := lip.trans (mul_le_mul_of_nonneg_left distance apos)
  have h (b : ℝ) : 2 * Real.pi * b / N = a * b := by dsimp [a]; ring
  rw [h, h, ← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), h]
  linarith

/-- A single exact comparison decides the sign of the hidden cosine on the lower half. -/
theorem salieHalf_negative {u : ℝ} (lo : 0 ≤ u) (hi : u ≤ 1/2) :
    Real.cos (2 * Real.pi * u) < 0 ↔ 1/4 < u := by
  have pp := Real.pi_pos
  constructor
  · intro h
    by_contra! hu
    have a := mul_le_mul_of_nonneg_left hu pp.le
    exact (not_lt_of_ge (Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [mul_nonneg pp.le lo],
      by linarith⟩)) h
  · intro hu
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    · nlinarith [mul_lt_mul_of_pos_left hu pp]
    · nlinarith [mul_le_mul_of_nonneg_left hi pp.le]

/-- Unhinted enumeration of the public predicate on a bounded example. -/
example : ((List.range 334).filter (fun y => y^2 % 667 = 64 ∧ y ≠ 8)).map (· / 32) = [4] := by
  decide +kernel

end PrimeFactors
