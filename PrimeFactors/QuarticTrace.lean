import PrimeFactors.PhaseCharacters
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

namespace PrimeFactors.QuarticTrace

section Field

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Up to the local Frobenius sign, this is the trace of y² = x³ − dx. -/
noncomputable def trace (d : F) : ℤ :=
  ∑ x : F, quadraticChar F x * quadraticChar F (x ^ 2 - d)

private theorem character_square (x : F) :
    quadraticChar F x ^ 2 = if x = 0 then 0 else 1 := by
  split_ifs with h
  · simp [h]
  · exact quadraticChar_sq_one h

/-- A square change in the parameter preserves the squared trace. -/
theorem trace_scale {u : F} (hu : u ≠ 0) (d : F) :
    trace (u ^ 2 * d) = quadraticChar F u * trace d := by
  unfold trace
  rw [← Equiv.sum_comp (Equiv.mulLeft₀ u hu) (fun x : F =>
    quadraticChar F x * quadraticChar F (x ^ 2 - u ^ 2 * d))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  change quadraticChar F (u * x) * quadraticChar F ((u * x) ^ 2 - u ^ 2 * d) = _
  rw [show (u * x) ^ 2 - u ^ 2 * d = u ^ 2 * (x ^ 2 - d) by ring,
    map_mul, map_mul, map_pow, quadraticChar_sq_one hu]
  ring

omit [Field F] in
private theorem omit_one (a : F) (w : ℤ) :
    (∑ x : F, if x = a then 0 else w) = (Fintype.card F - 1 : ℤ) * w := by
  have term (x : F) : (if x = a then 0 else w) = w - (if x = a then w else 0) := by
    split_ifs <;> simp
  simp_rw [term, Finset.sum_sub_distrib]
  simp
  ring

private theorem shifted_correlation (odd : ringChar F ≠ 2) (a b : F) :
    ∑ d : F, quadraticChar F (a - d) * quadraticChar F (b - d) =
      (if a = b then (Fintype.card F : ℤ) else 0) - 1 := by
  by_cases h : a = b
  · subst b
    simp only [if_pos rfl, ← sq, character_square, sub_eq_zero, eq_comm (a := a)]
    simpa using omit_one a 1
  · rw [if_neg h, zero_sub]
    convert phaseCharacters_shift_sum odd (a := -a) (b := -b) (fun he => h (neg_inj.mp he)) using 1
    apply Finset.sum_congr rfl
    intro x _
    rw [← map_mul]
    congr 1
    ring

/-- The complete second moment of the cubic character sums for split −1. -/
theorem second_moment (odd : ringChar F ≠ 2) (split : quadraticChar F (-1) = 1) :
    ∑ d : F, trace d ^ 2 = 2 * Fintype.card F * (Fintype.card F - 1 : ℤ) := by
  classical
  let χ := quadraticChar F
  have neg (x : F) : χ (-x) = χ x := by
    change quadraticChar F (-x) = _
    rw [show -x = -1 * x by ring, map_mul, split, one_mul]
  have diag (x : F) :
      ∑ y : F, (if x ^ 2 = y ^ 2 then χ x * χ y else 0) =
        if x = 0 then 0 else 2 := by
    by_cases hx : x = 0
    · subst x
      simp [χ]
    have distinct : x ≠ -x := by
      intro same
      exact hx ((Ring.eq_self_iff_eq_zero_of_char_ne_two odd).mp same.symm)
    have terms (y : F) :
        (if x ^ 2 = y ^ 2 then χ x * χ y else 0) =
          (if y = x then χ x ^ 2 else 0) + (if y = -x then χ x ^ 2 else 0) := by
      by_cases pos : y = x
      · subst y
        simp [distinct, sq]
      by_cases negated : y = -x
      · subst y
        simp [Ne.symm distinct, neg, sq]
      have neq : x ^ 2 ≠ y ^ 2 := by
        rw [ne_eq, sq_eq_sq_iff_eq_or_eq_neg]
        exact fun h => h.elim (fun e => pos e.symm) (fun e => negated (neg_eq_iff_eq_neg.mp e.symm))
      simp [pos, negated, neq]
    simp_rw [terms]
    have sqone : χ x ^ 2 = 1 := quadraticChar_sq_one hx
    simp [Finset.sum_add_distrib, hx, sqone]
  let B (d x : F) := χ x * χ (x ^ 2 - d)
  have expand (d : F) : trace d ^ 2 = ∑ x : F, ∑ y : F, B d x * B d y := by
    change (∑ x : F, B d x) ^ 2 = _
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  have corr (x y : F) : ∑ d : F, B d x * B d y =
      (Fintype.card F : ℤ) * (if x ^ 2 = y ^ 2 then χ x * χ y else 0) - χ x * χ y := by
    calc
      _ = χ x * χ y * ∑ d : F, χ (x ^ 2 - d) * χ (y ^ 2 - d) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        dsimp [B]
        ring
      _ = _ := by
        rw [show (∑ d : F, χ (x ^ 2 - d) * χ (y ^ 2 - d)) = _ from
          shifted_correlation odd (x ^ 2) (y ^ 2)]
        split_ifs <;> ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  have commute (x : F) : (∑ d : F, ∑ y : F, B d x * B d y) = ∑ y : F, ∑ d : F, B d x * B d y := Finset.sum_comm
  simp_rw [commute, corr, Finset.sum_sub_distrib, ← Finset.mul_sum, diag]
  have total : ∑ t : F, χ t = 0 := quadraticChar_sum_zero odd
  simp only [total, mul_zero, Finset.sum_const_zero, sub_zero, ← Finset.mul_sum, omit_one]
  ring

private theorem trace_zero (odd : ringChar F ≠ 2) : trace (0 : F) = 0 := by
  unfold trace
  convert quadraticChar_sum_zero (F := F) odd using 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x = 0
  · simp [hx]
  · rw [sub_zero, map_pow, quadraticChar_sq_one hx, mul_one]

/-- A nonsquare parameter supplies the missing square in a representation of 4|F|. -/
theorem complementary_squares (odd : ringChar F ≠ 2) (split : quadraticChar F (-1) = 1)
    {d : F} (nonsquare : quadraticChar F d = -1) :
    trace (1 : F) ^ 2 + trace d ^ 2 = 4 * Fintype.card F := by
  classical
  have hd : d ≠ 0 := fun h => by simp [h] at nonsquare
  have scale (u c : F) (hu : u ≠ 0) : trace (u ^ 2 * c) ^ 2 = trace c ^ 2 := by
    rw [trace_scale hu, mul_pow, quadraticChar_sq_one hu, one_mul]
  have pair (c : F) : trace c ^ 2 + trace (d * c) ^ 2 =
      if c = 0 then 0 else trace (1 : F) ^ 2 + trace d ^ 2 := by
    by_cases hc : c = 0
    · simp [hc, trace_zero odd]
    rw [if_neg hc]
    by_cases square : IsSquare c
    · obtain ⟨u, hu⟩ := square
      have un : u ≠ 0 := fun h => hc (by simp [hu, h])
      rw [show c = u ^ 2 * 1 by simpa [sq] using hu, scale u 1 un,
        show d * (u ^ 2 * 1) = u ^ 2 * d by ring, scale u d un]
    · have dn : c / d ≠ 0 := div_ne_zero hc hd
      have comp : IsSquare (c / d) := (quadraticChar_one_iff_isSquare dn).mp (by
        have h := congrArg (quadraticChar F) (div_mul_cancel₀ c hd)
        rw [map_mul, nonsquare, quadraticChar_neg_one_iff_not_isSquare.mpr square] at h
        linarith)
      obtain ⟨u, hu⟩ := comp
      have un : u ≠ 0 := fun h => dn (by simp [hu, h])
      have rep : c = u ^ 2 * d := (div_eq_iff hd).mp (by simpa [sq] using hu)
      rw [rep, scale u d un, show d * (u ^ 2 * d) = (u * d) ^ 2 * 1 by ring,
        scale (u*d) 1 (mul_ne_zero un hd), add_comm]
  have shift : (∑ c : F, trace (d * c) ^ 2) = ∑ c : F, trace c ^ 2 :=
    Equiv.sum_comp (Equiv.mulLeft₀ d hd) (fun c => trace c ^ 2)
  have h := congrArg (fun f : F → ℤ => ∑ c : F, f c) (funext pair)
  simp only [Finset.sum_add_distrib, shift, second_moment odd split, omit_one] at h
  have size : (1 : ℤ) < Fintype.card F := by exact_mod_cast (Fintype.one_lt_card (α := F))
  apply mul_left_cancel₀ (sub_ne_zero.mpr (ne_of_gt size))
  linear_combination -h

/-- With nonsquare −1 the terms at x and −x cancel for every parameter. -/
theorem inert_trace (d : F) (inert : quadraticChar F (-1) = -1) : trace d = 0 := by
  let w (x : F) := quadraticChar F x * quadraticChar F (x ^ 2 - d)
  have neg (x : F) : w (-x) = -w x := by
    change quadraticChar F (-x) * quadraticChar F ((-x) ^ 2 - d) = -(_ * _)
    rw [neg_sq, show -x = -1 * x by ring, map_mul, inert]
    ring
  have flip := Equiv.sum_comp (Equiv.neg F) w
  change (∑ x : F, w (-x)) = ∑ x : F, w x at flip
  simp_rw [neg, Finset.sum_neg_distrib] at flip
  change ∑ x : F, w x = 0
  omega

end Field

/-- A complete Jacobi sum indexed by the composite modulus itself. -/
noncomputable def complete (n : ℕ) [NeZero n] (d : ℤ) : ℤ :=
  ∑ x : ZMod n, jacobiSym ((x.val : ℤ) * ((x.val : ℤ) ^ 2 - d)) n

/-- CRT separates the product-only sum into the two local cubic traces. -/
theorem complete_eq (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    [NeZero (p*q)] (cop : p.Coprime q) (d : ℤ) :
    complete (p*q) d = trace (d : ZMod p) * trace (d : ZMod q) := by
  let e := ZMod.chineseRemainder cop
  let f (x : ZMod p) := quadraticChar (ZMod p) x * quadraticChar (ZMod p) (x ^ 2 - d)
  let g (x : ZMod q) := quadraticChar (ZMod q) x * quadraticChar (ZMod q) (x ^ 2 - d)
  have term (x : ZMod (p * q)) :
      jacobiSym ((x.val : ℤ) * ((x.val : ℤ) ^ 2 - d)) (p * q) = f (e x).1 * g (e x).2 := by
    rw [jacobiSym.mul_right' _ hp.out.ne_zero hq.out.ne_zero,
      ← jacobiSym.legendreSym.to_jacobiSym p, ← jacobiSym.legendreSym.to_jacobiSym q]
    have hx : e x = (x.val : ℕ) := by rw [← map_natCast e, ZMod.natCast_zmod_val]
    simp only [legendreSym, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
      map_mul, hx, f, g, Prod.fst_natCast, Prod.snd_natCast]
  unfold complete
  rw [Fintype.sum_equiv e.toEquiv _ (fun z => f z.1 * g z.2) term, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rfl

private theorem coordinate_unit {q : ℕ} (hq : q.Prime) (large : 4 < q) {a b : ℤ}
    (norm : a ^ 2 + b ^ 2 = 4 * q) : ¬ q ∣ a.natAbs := by
  intro ha
  have ai : (q : ℤ) ∣ a := (Int.natCast_dvd).mpr ha
  have bi : (q : ℤ) ∣ b ^ 2 := by
    rw [show b ^ 2 = 4 * q - a ^ 2 by linarith]
    exact dvd_sub (dvd_mul_left _ _) (dvd_pow ai (by decide : 2 ≠ 0))
  obtain ⟨i, hi⟩ := ai
  obtain ⟨j, hj⟩ := (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow bi
  have zero : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have cancel : (q : ℤ) * (q * (i ^ 2 + j ^ 2)) = q * 4 := by
    rw [hi, hj] at norm
    linear_combination norm
  have small : q ∣ 4 := Int.natCast_dvd_natCast.mp ⟨_, (mul_left_cancel₀ zero cancel).symm⟩
  exact (not_le_of_gt large) (Nat.le_of_dvd (by decide) small)

private theorem minus_split {p : ℕ} [Fact p.Prime] (four : p % 4 = 1) :
    quadraticChar (ZMod p) (-1) = 1 := by
  apply (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
  apply FiniteField.isSquare_neg_one_iff.mpr
  simp [ZMod.card, four]

/-- For the base parameter the half-trace is odd, fixing the parity of the two norm coordinates. -/
theorem base_parity (p : ℕ) [hp : Fact p.Prime] (pc : p % 4 = 1) :
    trace (1 : ZMod p) ≡ 2 [ZMOD 4] := by
  classical
  let w (x : (ZMod p)) := quadraticChar (ZMod p) (x * (x ^ 2 - 1))
  let rep (x : (ZMod p)) : ℤ := if w x = -1 ∧ x.val < (-x).val then 1 else 0
  have odd : ringChar (ZMod p) ≠ 2 := by change ringChar (ZMod p) ≠ 2; rw [ZMod.ringChar_zmod_n]; omega
  have distinct : (1 : (ZMod p)) ≠ -1 := (Ring.neg_one_ne_one_of_char_ne_two odd).symm
  have evenf (x : (ZMod p)) : w (-x) = w x := by
    change quadraticChar (ZMod p) _ = quadraticChar (ZMod p) _
    rw [show -x * ((-x) ^ 2 - 1) = -1 * (x * (x ^ 2 - 1)) by ring,
      map_mul, minus_split pc, one_mul]
  have term (x : (ZMod p)) : w x = 1 - (if x = 0 then 1 else 0) - (if x = 1 then 1 else 0) -
      (if x = -1 then 1 else 0) - 2 * (rep x + rep (-x)) := by
    by_cases hx : x = 0
    · simp [hx, w, rep]
    by_cases h1 : x = 1
    · simp [h1, w, rep, distinct]
    by_cases hneg : x = -1
    · simp [hneg, w, rep, Ne.symm distinct]
    have nz : x * (x ^ 2 - 1) ≠ 0 := mul_ne_zero hx (sub_ne_zero.mpr (by
      exact fun h => (sq_eq_one_iff.mp h).elim h1 hneg))
    have unequal : x.val ≠ (-x).val := by
      intro he
      exact hx ((Ring.eq_self_iff_eq_zero_of_char_ne_two odd).mp ((ZMod.val_injective p he).symm))
    rcases quadraticChar_dichotomy nz with positive | negative
    · change w x = 1 at positive
      simp [hx, h1, hneg, rep, evenf, positive]
    · change w x = -1 at negative
      rcases lt_or_gt_of_ne unequal with lt | gt
      · simp [hx, h1, hneg, rep, evenf, negative, lt, not_lt.mpr lt.le]
      · simp [hx, h1, hneg, rep, evenf, negative, gt, not_lt.mpr gt.le]
  have flip := Equiv.sum_comp (Equiv.neg (ZMod p)) rep
  change (∑ x : (ZMod p), rep (-x)) = ∑ x : (ZMod p), rep x at flip
  have total : trace (1 : (ZMod p)) = (p : ℤ) - 3 - 4 * ∑ x : (ZMod p), rep x := by
    unfold trace
    simp_rw [← map_mul]
    change (∑ x : (ZMod p), w x) = _
    calc
      _ = _ := Finset.sum_congr rfl (fun x _ => term x)
      _ = _ := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, flip]
        simp
        ring
  change trace (1 : (ZMod p)) % 4 = 2 % 4
  rw [total]
  omega

/-- Three coefficient bits distinguish the two prime classes even if N itself is 1 modulo 4. -/
theorem base_bit (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    [NeZero (p*q)] (cop : p.Coprime q) (pOdd : Odd p) (qOdd : Odd q) :
    complete (p*q) 1 ≡ 4 [ZMOD 8] ↔ p % 4 = 1 ∧ q % 4 = 1 := by
  rw [complete_eq p q cop]
  simp only [Int.cast_one]
  have vanishes (r : ℕ) [Fact r.Prime] (odd : Odd r) (h : r % 4 ≠ 1) :
      trace (1 : ZMod r) = 0 := by
    apply inert_trace _ (quadraticChar_neg_one_iff_not_isSquare.mpr _)
    rw [FiniteField.isSquare_neg_one_iff, ZMod.card]
    obtain ⟨k, hk⟩ := odd
    omega
  by_cases pc : p % 4 = 1
  · by_cases qc : q % 4 = 1
    · simp only [pc, qc, and_self, iff_true]
      have pbase := Int.modEq_iff_dvd.mp (base_parity p pc)
      have qbase := Int.modEq_iff_dvd.mp (base_parity q qc)
      obtain ⟨a, ha⟩ := pbase
      obtain ⟨b, hb⟩ := qbase
      apply Int.modEq_iff_dvd.mpr
      refine ⟨a+b-2*a*b, ?_⟩
      have hpval : trace (1 : ZMod p) = 2-4*a := by omega
      have hqval : trace (1 : ZMod q) = 2-4*b := by omega
      rw [hpval, hqval]
      ring
    · rw [vanishes q qOdd qc, mul_zero]
      simp [qc, Int.ModEq]
  · rw [vanishes p pOdd pc, zero_mul]
    simp [pc, Int.ModEq]

/-- Two public sums recover the prime at which d is a nonsquare. -/
theorem recover_nonsquare (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    [NeZero (p*q)] (cop : p.Coprime q) (pc : p % 4 = 1) (qc : q % 4 = 1) (d : ℤ)
    (left : quadraticChar (ZMod p) (d : ZMod p) = -1)
    (right : quadraticChar (ZMod q) (d : ZMod q) = 1) :
    (complete (p*q) 1 ^ 2 + complete (p*q) d ^ 2).natAbs.gcd (p*q) = p := by
  have pchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have qchar : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have normp := complementary_squares pchar (minus_split pc) left
  obtain ⟨w, hw⟩ := quadraticChar_exists_neg_one (F := ZMod q) qchar
  have normq := complementary_squares qchar (minus_split qc) hw
  rw [ZMod.card] at normp normq
  have qmin := hq.out.two_le
  have large : 4 < q := by omega
  have unit := coordinate_unit hq.out large normq
  have dn : (d : ZMod q) ≠ 0 := fun he => by simp [he] at right
  obtain ⟨u, hu⟩ := (quadraticChar_one_iff_isSquare dn).mp right
  have un : u ≠ 0 := fun he => dn (by simp [hu, he])
  have same : trace (d : ZMod q) ^ 2 = trace (1 : ZMod q) ^ 2 := by
    rw [show (d : ZMod q) = u ^ 2 * 1 by simpa [sq] using hu, trace_scale un,
      mul_pow, quadraticChar_sq_one un, one_mul]
  have identity : complete (p*q) 1 ^ 2 + complete (p*q) d ^ 2 =
      (p : ℤ) * (4 * trace (1 : ZMod q) ^ 2) := by
    rw [complete_eq p q cop, complete_eq p q cop]
    simp only [Int.cast_one, mul_pow, same]
    linear_combination trace (1 : ZMod q) ^ 2 * normp
  have cfour : q.Coprime 4 := hq.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) large)
  have c := (cfour.mul_right ((hq.out.coprime_iff_not_dvd.mpr unit).pow_right 2)).symm
  rw [identity, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast,
    show (4 : ℤ).natAbs = 4 by decide, Nat.gcd_mul_left, c.gcd_eq_one, mul_one]

/-- A negative public Jacobi symbol selects opposite local signs, without needing to know which. -/
theorem split_of_jacobi (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    [NeZero (p*q)] (cop : p.Coprime q) (pc : p % 4 = 1) (qc : q % 4 = 1)
    (d : ℤ) (separator : jacobiSym d (p*q) = -1) :
    let g := (complete (p*q) 1 ^ 2 + complete (p*q) d ^ 2).natAbs.gcd (p*q)
    g = p ∨ g = q := by
  rw [jacobiSym.mul_right' _ hp.out.ne_zero hq.out.ne_zero,
    ← jacobiSym.legendreSym.to_jacobiSym p, ← jacobiSym.legendreSym.to_jacobiSym q] at separator
  change quadraticChar (ZMod p) (d : ZMod p) * quadraticChar (ZMod q) (d : ZMod q) = -1 at separator
  have pd : (d : ZMod p) ≠ 0 := fun h => by simp [h] at separator
  have qd : (d : ZMod q) ≠ 0 := fun h => by simp [h] at separator
  rcases quadraticChar_dichotomy pd with pos | neg
  · right
    have qneg : quadraticChar (ZMod q) (d : ZMod q) = -1 := by simpa only [pos, one_mul] using separator
    letI : NeZero (q*p) := ⟨Nat.mul_ne_zero hq.out.ne_zero hp.out.ne_zero⟩
    simpa only [Nat.mul_comm q p] using recover_nonsquare q p cop.symm qc pc d qneg pos
  · left
    have qpos : quadraticChar (ZMod q) (d : ZMod q) = 1 := by rw [neg, neg_one_mul] at separator; omega
    exact recover_nonsquare p q cop pc qc d neg qpos

/-- At a good prime with zero trace, the weight-two Hecke recurrence fixes every coefficient. -/
theorem zero_trace_prime_powers {r : ℤ} (a : ℕ → ℤ) (first : a 0 = 1) (zero : a 1 = 0)
    (step : ∀ j, a (j+2) = -r * a j) (k : ℕ) :
    a (2*k) = (-r)^k ∧ a (2*k+1) = 0 := by
  induction k with
  | zero => simpa using And.intro first zero
  | succ k ih =>
    rw [show 2*(k+1) = 2*k+2 by omega, step, ih.1, pow_succ,
      show 2*k+2+1 = (2*k+1)+2 by omega, step, ih.2, mul_zero]
    exact ⟨mul_comm .., rfl⟩

/-- If both local traces vanish, coefficients at all powers of pq depend only on pq. -/
theorem zero_trace_product_powers (p q : ℤ) (a b : ℕ → ℤ)
    (a0 : a 0 = 1) (a1 : a 1 = 0) (as_ : ∀ j, a (j+2) = -p * a j)
    (b0 : b 0 = 1) (b1 : b 1 = 0) (bs : ∀ j, b (j+2) = -q * b j) (k : ℕ) :
    a (2*k) * b (2*k) = (p*q)^k ∧ a (2*k+1) * b (2*k+1) = 0 := by
  obtain ⟨ae, ao⟩ := zero_trace_prime_powers a a0 a1 as_ k
  obtain ⟨be, bo⟩ := zero_trace_prime_powers b b0 b1 bs k
  simp [ae, ao, be, bo, ← mul_pow]

/-- Two Fourier coefficients at N and N² determine the scaled squares of the prime traces. -/
theorem hecke_discriminant (p q u v : ℤ) :
    let A := u*v
    let B := (u^2-p)*(v^2-q)
    let S := A^2+p*q-B
    S = q*u^2+p*v^2 ∧ S^2-4*p*q*A^2 = (q*u^2-p*v^2)^2 := by
  dsimp
  constructor <;> ring

end PrimeFactors.QuarticTrace
