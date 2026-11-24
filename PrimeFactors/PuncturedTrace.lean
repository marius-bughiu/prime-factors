import PrimeFactors.ExtensionTrace
import PrimeFactors.QuarticTrace

namespace PrimeFactors.PuncturedTrace

open ExtensionTrace

/-- The marked cubic has a double zero at 2. -/
def marked {R : Type*} [CommRing R] (x : R) : R := (x-2)^2 * cubic 0 (-1) 0 x

/-- Norm of the marked cubic evaluated at x+y√d. -/
def markedNorm {R : Type*} [CommRing R] (d x y : R) : R :=
  ((x-2)^2-d*y^2)^2 * normCubic 0 (-1) 0 d x y

section Field
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def markedBase : ℤ := ∑ x : F, quadraticChar F (marked x)

noncomputable def markedExtension (d : F) : ℤ :=
  ∑ z : F × F, quadraticChar F (markedNorm d z.1 z.2)

/-- The marked rational point contributes its own quadratic character to the base sum. -/
theorem drop_base :
    markedBase (F := F) = trace (0 : F) (-1) 0 - quadraticChar F 6 := by
  classical
  have term (x : F) : quadraticChar F (marked x) = quadraticChar F (cubic 0 (-1) 0 x) -
      (if x = 2 then quadraticChar F 6 else 0) := by
    by_cases h : x = 2
    · subst x
      rw [show cubic (0 : F) (-1) 0 2 = 6 by unfold cubic; ring]
      simp [marked]
    · rw [marked, map_mul, quadraticChar_sq_one' (sub_ne_zero.mpr h)]
      simp [h]
  simp only [markedBase, trace, term, Finset.sum_sub_distrib]
  simp

/-- The split quadratic algebra has two independent marked coordinates. -/
theorem marked_split (odd : ringChar F ≠ 2) {s : F} (nz : s ≠ 0) :
    markedExtension (s^2) = markedBase (F := F) ^ 2 := by
  let e : F × F ≃ F × F := {
    toFun := fun ⟨x,y⟩ => (x+s*y,x-s*y)
    invFun := fun ⟨u,v⟩ => ((u+v)/2,(u-v)/(2*s))
    left_inv := by
      have two := Ring.two_ne_zero odd
      rintro ⟨x,y⟩; ext <;> dsimp <;> field_simp <;> ring
    right_inv := by
      have two := Ring.two_ne_zero odd
      rintro ⟨u,v⟩; ext <;> dsimp <;> field_simp <;> ring }
  let h (z : F × F) := quadraticChar F (marked z.1) * quadraticChar F (marked z.2)
  have term (z : F × F) : quadraticChar F (markedNorm (s^2) z.1 z.2) = h (e z) := by
    change _ = quadraticChar F (marked (z.1+s*z.2)) * quadraticChar F (marked (z.1-s*z.2))
    rw [← map_mul]
    congr 1
    unfold markedNorm marked normCubic cubic
    ring
  unfold markedExtension markedBase
  rw [Fintype.sum_equiv e _ h term, Fintype.sum_prod_type]
  simp only [h, ← Finset.mul_sum, ← Finset.sum_mul, sq]

/-- In the inert quadratic algebra the sole removed term occurs at (2,0), with value one. -/
theorem marked_inert (odd : ringChar F ≠ 2) {d : F} (neg : quadraticChar F d = -1)
    (six : (6 : F) ≠ 0) :
    markedExtension d = 2 * Fintype.card F - trace (0 : F) (-1) 0 ^ 2 - 1 := by
  classical
  have ns := quadraticChar_neg_one_iff_not_isSquare.mp neg
  have norm_zero (x y : F) (hz : (x-2)^2-d*y^2 = 0) : (x,y) = (2,0) := by
    by_cases hy : y = 0
    · subst y
      have hx : (x-2)^2 = 0 := by simpa using hz
      simp [(sub_eq_zero.mp (sq_eq_zero_iff.mp hx))]
    · exfalso
      apply ns
      refine ⟨(x-2)/y, ?_⟩
      field_simp
      linear_combination -hz
  have term (z : F × F) : quadraticChar F (markedNorm d z.1 z.2) =
      quadraticChar F (normCubic 0 (-1) 0 d z.1 z.2) - (if z = (2,0) then 1 else 0) := by
    by_cases hz : z = (2,0)
    · subst z
      rw [show normCubic (0 : F) (-1) 0 d 2 0 = (6 : F)^2 by unfold normCubic; ring,
        quadraticChar_sq_one' six]
      simp [markedNorm]
    · have unit : (z.1-2)^2-d*z.2^2 ≠ 0 := fun h => hz (norm_zero z.1 z.2 h)
      rw [markedNorm, map_mul, quadraticChar_sq_one' unit]
      simp [hz]
  have smooth := legendre_inert odd (l := (-1 : F)) (neg_ne_zero.mpr one_ne_zero)
    (Ring.neg_one_ne_one_of_char_ne_two odd) neg
  simp only [add_neg_cancel, neg_zero] at smooth
  unfold markedExtension
  simp only [term, Finset.sum_sub_distrib]
  change extension (0 : F) (-1) 0 d - _ = _
  rw [smooth]
  simp

end Field

/-- Both sums are defined over the composite modulus itself. -/
noncomputable def base (n : ℕ) [NeZero n] : ℤ :=
  ∑ x : ZMod n, jacobiSym (marked (x.val : ℤ)) n

noncomputable def grid (n : ℕ) [NeZero n] (d : ℤ) : ℤ :=
  ∑ z : ZMod n × ZMod n, jacobiSym (markedNorm d (z.1.val : ℤ) z.2.val) n

theorem base_crt (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)] (cop : p.Coprime q) :
    base (p*q) = markedBase (F := ZMod p) * markedBase (F := ZMod q) := by
  let e := ZMod.chineseRemainder cop
  apply separated e.toEquiv
  intro x
  have hx : e x = (x.val : ℕ) := by rw [← map_natCast e, ZMod.natCast_zmod_val]
  change jacobiSym _ _ = quadraticChar (ZMod p) (marked (e x).1) *
    quadraticChar (ZMod q) (marked (e x).2)
  rw [jacobi_crt, hx]
  simp [marked, cubic]

theorem grid_crt (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)] (cop : p.Coprime q) (d : ℤ) :
    grid (p*q) d = markedExtension (d : ZMod p) * markedExtension (d : ZMod q) := by
  let e := ZMod.chineseRemainder cop
  let E := (e.toEquiv.prodCongr e.toEquiv).trans (Equiv.prodProdProdComm _ _ _ _)
  apply separated E
  rintro ⟨x,y⟩
  have hx : e x = (x.val : ℕ) := by rw [← map_natCast e, ZMod.natCast_zmod_val]
  have hy : e y = (y.val : ℕ) := by rw [← map_natCast e, ZMod.natCast_zmod_val]
  change jacobiSym _ _ = quadraticChar (ZMod p) (markedNorm _ (e x).1 (e y).1) *
    quadraticChar (ZMod q) (markedNorm _ (e x).2 (e y).2)
  rw [jacobi_crt, hx, hy]
  simp [markedNorm, normCubic]

/-- Multiplying by the public Jacobi symbol at 6 removes the two unknown local signs. -/
theorem normalized_sums (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (po : p ≠ 2) (qo : q ≠ 2)
    (sixP : (6 : ZMod p) ≠ 0) (sixQ : (6 : ZMod q) ≠ 0) (d : ℤ)
    (split : ∃ w : ZMod p, w ≠ 0 ∧ (d : ZMod p) = w ^ 2)
    (inert : quadraticChar (ZMod q) (d : ZMod q) = -1) :
    let U := quadraticChar (ZMod p) 6 * trace (0 : ZMod p) (-1) 0
    let V := quadraticChar (ZMod q) 6 * trace (0 : ZMod q) (-1) 0
    let e := jacobiSym 6 (p*q)
    e * baseSum (p*q) 0 (-1) 0 = U*V ∧
    e * base (p*q) = (U-1)*(V-1) ∧ grid (p*q) d = (U-1)^2*(2*q-V^2-1) := by
  obtain ⟨w, wn, hw⟩ := split
  dsimp only
  rw [baseSum_crt p q cop, base_crt p q cop, jacobi_crt, grid_crt p q cop, hw,
    marked_split (by simpa only [ZMod.ringChar_zmod_n] using po) wn,
    marked_inert (by simpa only [ZMod.ringChar_zmod_n] using qo) inert sixQ, ZMod.card]
  simp only [drop_base, Int.cast_zero, Int.cast_neg, Int.cast_one, Int.cast_ofNat]
  have hs := quadraticChar_sq_one sixP
  have ht := quadraticChar_sq_one sixQ
  refine ⟨by ring, ?_, ?_⟩
  · linear_combination
      (quadraticChar (ZMod q) 6 * trace (0 : ZMod q) (-1) 0 - quadraticChar (ZMod q) 6 ^ 2) * -hs +
      (quadraticChar (ZMod p) 6 * trace (0 : ZMod p) (-1) 0 - 1) * -ht
  · have first : (trace (0 : ZMod p) (-1) 0 - quadraticChar (ZMod p) 6)^2 =
        (quadraticChar (ZMod p) 6 * trace (0 : ZMod p) (-1) 0 - 1)^2 := by
      linear_combination (1 - trace (0 : ZMod p) (-1) 0 ^ 2) * hs
    rw [first, mul_pow (quadraticChar (ZMod q) 6), ht, one_mul]

/-- When r is 3 modulo 4, the unmarked local cubic trace vanishes identically. -/
theorem trace_zero {r : ℕ} [Fact r.Prime] (rc : r % 4 = 3) :
    trace (0 : ZMod r) (-1) 0 = 0 := by
  have neg : quadraticChar (ZMod r) (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr (by simp [FiniteField.isSquare_neg_one_iff, rc])
  convert QuarticTrace.inert_trace (1 : ZMod r) neg using 1
  unfold trace QuarticTrace.trace
  apply Finset.sum_congr rfl
  intro x _
  rw [← map_mul]
  congr 1
  unfold cubic
  ring

/-- The one marked sum measures twice the inert prime minus one without a Frobenius oracle. -/
theorem both_three (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (pc : p % 4 = 3) (qc : q % 4 = 3)
    (sixP : (6 : ZMod p) ≠ 0) (sixQ : (6 : ZMod q) ≠ 0) (d : ℤ)
    (split : ∃ w : ZMod p, w ≠ 0 ∧ (d : ZMod p) = w ^ 2)
    (inert : quadraticChar (ZMod q) (d : ZMod q) = -1) :
    grid (p*q) d = 2*q - 1 ∧ (grid (p*q) d + 1) / 2 = q := by
  have h := (normalized_sums p q cop (by omega) (by omega) sixP sixQ d split inert).2.2
  simp only [trace_zero pc, trace_zero qc, mul_zero, zero_sub, neg_sq, one_pow, zero_pow
    (by decide : 2 ≠ 0), sub_zero, one_mul] at h
  exact ⟨h, by omega⟩

/-- For an odd prime the unmarked trace is even, so either local sign normalization avoids 1. -/
theorem trace_even {p : ℕ} [Fact p.Prime] (odd : Odd p) :
    Even (trace (0 : ZMod p) (-1) 0) := by
  obtain ⟨k, hk⟩ := odd
  by_cases pc : p % 4 = 3
  · simp [trace_zero pc]
  have one : p % 4 = 1 := by omega
  have eq : trace (0 : ZMod p) (-1) 0 = QuarticTrace.trace (1 : ZMod p) := by
    unfold trace QuarticTrace.trace
    apply Finset.sum_congr rfl
    intro x _
    rw [← map_mul]
    congr 1
    unfold cubic
    ring
  rw [eq]
  have h := QuarticTrace.base_parity p one
  change QuarticTrace.trace (1 : ZMod p) % 4 = 2 % 4 at h
  exact ⟨QuarticTrace.trace (1 : ZMod p) / 2, by omega⟩

/-- In the correct ordering, integer division recovers q exactly for any even signed trace. -/
theorem decode (q U V B : ℤ) (even : Even U) (measured : B = (U-1)^2*(2*q-V^2-1)) :
    (B/(U-1)^2+V^2+1)/2 = q := by
  obtain ⟨k, hk⟩ := even
  have nonzero : (U-1)^2 ≠ 0 := pow_ne_zero _ (by omega)
  rw [measured, Int.mul_ediv_cancel_left _ nonzero]
  omega

/-- An integer pair with the same sum and product agrees in one of the two orders. -/
private theorem root_pair (x y U V : ℤ) (prod : x*y = U*V) (sum : x+y = U+V) :
    (x = U ∧ y = V) ∨ (x = V ∧ y = U) := by
  have zero : (x-U)*(x-V) = 0 := by linear_combination x*sum-prod
  rcases mul_eq_zero.mp zero with h | h
  · exact Or.inl ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

/-- Public sum and product admit integer roots. In either ordering, trying both
candidate divisions recovers the inert prime, including when the roots coincide. -/
theorem recover_from_measurements (p q : ℕ) [hp : Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (po : p ≠ 2) (qo : q ≠ 2)
    (sixP : (6 : ZMod p) ≠ 0) (sixQ : (6 : ZMod q) ≠ 0) (d : ℤ)
    (split : ∃ w : ZMod p, w ≠ 0 ∧ (d : ZMod p) = w ^ 2)
    (inert : quadraticChar (ZMod q) (d : ZMod q) = -1) :
    let T := jacobiSym 6 (p*q) * baseSum (p*q) 0 (-1) 0
    let S := T + 1 - jacobiSym 6 (p*q) * base (p*q)
    let candidate := fun x y : ℤ => (grid (p*q) d / (x-1)^2+y^2+1)/2
    (∃ x y : ℤ, x*y = T ∧ x+y = S) ∧
      ∀ x y : ℤ, x*y = T → x+y = S → candidate x y = (q : ℤ) ∨ candidate y x = (q : ℤ) := by
  let U := quadraticChar (ZMod p) 6 * trace (0 : ZMod p) (-1) 0
  let V := quadraticChar (ZMod q) 6 * trace (0 : ZMod q) (-1) 0
  obtain ⟨prod, adjusted, grid_eq⟩ := normalized_sums p q cop po qo sixP sixQ d split inert
  change _ = U*V at prod
  change _ = (U-1)*(V-1) at adjusted
  have even : Even U := (trace_even (hp.out.odd_of_ne_two po)).mul_left _
  have answer := decode q U V (grid (p*q) d) even grid_eq
  dsimp only
  rw [prod, adjusted]
  have sum : U*V+1-(U-1)*(V-1) = U+V := by ring
  rw [sum]
  refine ⟨⟨U, V, rfl, rfl⟩, ?_⟩
  intro x y hp' hs'
  rcases root_pair x y U V hp' hs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl answer
  · exact Or.inr answer

/-- Taking a gcd of the marked sum plus one also returns the inert prime. -/
theorem both_three_gcd (p q : ℕ) [hp : Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (pc : p % 4 = 3) (qc : q % 4 = 3)
    (sixP : (6 : ZMod p) ≠ 0) (sixQ : (6 : ZMod q) ≠ 0) (d : ℤ)
    (split : ∃ w : ZMod p, w ≠ 0 ∧ (d : ZMod p) = w ^ 2)
    (inert : quadraticChar (ZMod q) (d : ZMod q) = -1) :
    (grid (p*q) d + 1).natAbs.gcd (p*q) = q := by
  rw [(both_three p q cop pc qc sixP sixQ d split inert).1, sub_add_cancel, Int.natAbs_mul,
    Int.natAbs_natCast, show (2:ℤ).natAbs = 2 by decide, Nat.gcd_mul_right]
  have c : p.Coprime 2 := hp.out.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  rw [c.symm.gcd_eq_one]
  simp

/-- The two selectors on 77 recover opposite factors. -/
theorem example_77 : grid 77 2 = 21 ∧ grid 77 3 = 13 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have two : quadraticChar (ZMod 11) (2 : ℤ) = -1 := by
    apply quadraticChar_neg_one_iff_not_isSquare.mpr
    obtain nonres : ∀ x : ZMod 11, (2:ZMod 11) ≠ x*x := by decide
    exact fun ⟨x, h⟩ => nonres x h
  have three : quadraticChar (ZMod 7) (3 : ℤ) = -1 := by
    apply quadraticChar_neg_one_iff_not_isSquare.mpr
    obtain nonres : ∀ x : ZMod 7, (3:ZMod 7) ≠ x*x := by decide
    exact fun ⟨x, h⟩ => nonres x h
  exact ⟨(both_three 7 11 (by decide) (by decide) (by decide) (by decide) (by decide) 2
    ⟨3, by decide, by decide⟩ two).1, (both_three 11 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) 3 ⟨5, by decide, by decide⟩ three).1⟩

end PrimeFactors.PuncturedTrace
