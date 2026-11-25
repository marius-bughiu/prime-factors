import PrimeFactors.PuncturedTrace

namespace PrimeFactors.MarkedTraceBit

open ExtensionTrace

def f {R : Type*} [CommRing R] (x : R) := x * (x^2-1)

def mark {R : Type*} [CommRing R] (a b x : R) := (x-a)^2 * (x-b)^2 * f x

def norm {R : Type*} [CommRing R] (a b d x y : R) :=
  ((x-a)^2-d*y^2)^2 * ((x-b)^2-d*y^2)^2 * normCubic 0 (-1) 0 d x y

section Field
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def base (a b : F) : ℤ := ∑ x : F, quadraticChar F (mark a b x)

noncomputable def ext (a b d : F) : ℤ :=
  ∑ z : F × F, quadraticChar F (norm a b d z.1 z.2)

private theorem remove_one {I : Type*} [DecidableEq I] [Fintype I]
    (a : I) (h : I → ℤ) :
    (∑ i : I, if i=a then 0 else h i) = (∑ i : I, h i) - h a := by
  have term (i : I) : (if i=a then 0 else h i) = h i - (if i=a then h a else 0) := by
    split_ifs with hi <;> simp_all
  simp_rw [term, Finset.sum_sub_distrib]
  simp

private theorem base_eval (a b : F) (different : a ≠ b) :
    base a b = trace (0 : F) (-1) 0 - quadraticChar F (f a) - quadraticChar F (f b) := by
  let t (x : F) := quadraticChar F (f x)
  have term (x : F) : quadraticChar F (mark a b x) =
      if x=b then 0 else if x=a then 0 else t x := by
    by_cases ha : x=a
    · simp [ha, mark]
    by_cases hb : x=b
    · simp [hb, mark]
    simp only [mark, map_mul, quadraticChar_sq_one' (sub_ne_zero.mpr ha),
      quadraticChar_sq_one' (sub_ne_zero.mpr hb), one_mul, if_neg ha, if_neg hb, t]
  unfold base
  simp_rw [term]
  rw [remove_one, remove_one, if_neg different.symm]
  have h : (∑ x : F, t x) = trace (0 : F) (-1) 0 := by
    apply Finset.sum_congr rfl
    intro x _
    apply congrArg (quadraticChar F)
    unfold f cubic
    ring
  rw [h]

private theorem split_sum (odd : ringChar F ≠ 2) (a b s : F) (sn : s ≠ 0) :
    ext a b (s^2) = base a b ^ 2 := by
  have two := Ring.two_ne_zero odd
  let e : F × F ≃ F × F := {
    toFun := fun ⟨x,y⟩ => (x+s*y,x-s*y)
    invFun := fun ⟨u,v⟩ => ((u+v)/2,(u-v)/(2*s))
    left_inv := by rintro ⟨x,y⟩; ext <;> dsimp <;> field_simp <;> ring
    right_inv := by rintro ⟨u,v⟩; ext <;> dsimp <;> field_simp <;> ring }
  let h := fun (x : F) => quadraticChar F (mark a b x)
  have term (z : F × F) : quadraticChar F (norm a b (s^2) z.1 z.2) = h (e z).1 * h (e z).2 := by
    change _ = quadraticChar F (mark a b (z.1+s*z.2)) * quadraticChar F (mark a b (z.1-s*z.2))
    rw [← map_mul]
    congr 1
    have mask (c : F) : (z.1-c)^2-s^2*z.2^2 = (z.1+s*z.2-c)*(z.1-s*z.2-c) := by ring
    have cubic_identity : normCubic 0 (-1) 0 (s^2) z.1 z.2 = f (z.1+s*z.2) * f (z.1-s*z.2) := by
      unfold f normCubic
      ring
    simp only [norm, mark, mask, cubic_identity]
    ring
  rw [ext, separated e _ h h term, base, sq]

private theorem inert_sum (odd : ringChar F ≠ 2) (a b d : F) (neg : quadraticChar F d = -1)
    (different : a ≠ b) (ha : f a ≠ 0) (hb : f b ≠ 0) :
    ext a b d = 2*Fintype.card F - trace (0 : F) (-1) 0 ^ 2 - 2 := by
  let t (z : F × F) := quadraticChar F (normCubic 0 (-1) 0 d z.1 z.2)
  have zero (c x y : F) (hz : (x-c)^2-d*y^2 = 0) : (x,y) = (c,0) := by
    by_cases hy : y = 0
    · subst y
      have hx : (x-c)^2 = 0 := by simpa using hz
      simp [sub_eq_zero.mp (sq_eq_zero_iff.mp hx)]
    · exfalso
      apply quadraticChar_neg_one_iff_not_isSquare.mp neg
      refine ⟨(x-c)/y, ?_⟩
      field_simp
      linear_combination -hz
  have term (z : F × F) : quadraticChar F (norm a b d z.1 z.2) =
      if z=(b,0) then 0 else if z=(a,0) then 0 else t z := by
    by_cases za : z=(a,0)
    · simp [za, norm]
    by_cases zb : z=(b,0)
    · simp [zb, norm]
    have ua : (z.1-a)^2-d*z.2^2 ≠ 0 := fun hz => za (zero a z.1 z.2 hz)
    have ub : (z.1-b)^2-d*z.2^2 ≠ 0 := fun hz => zb (zero b z.1 z.2 hz)
    simp only [norm, map_mul, quadraticChar_sq_one' ua, quadraticChar_sq_one' ub,
      one_mul, if_neg za, if_neg zb, t]
  have axis (c : F) (good : f c ≠ 0) : t (c,0) = 1 := by
    change quadraticChar F (normCubic 0 (-1) 0 d c 0) = 1
    rw [show normCubic 0 (-1) 0 d c 0 = (f c)^2 by unfold normCubic f; ring]
    exact quadraticChar_sq_one' good
  have smooth := legendre_inert odd (l := (-1 : F)) (neg_ne_zero.mpr one_ne_zero)
    (Ring.neg_one_ne_one_of_char_ne_two odd) neg
  simp only [add_neg_cancel, neg_zero] at smooth
  unfold ext
  simp_rw [term]
  rw [remove_one, remove_one, if_neg (fun he => different (congrArg Prod.fst he).symm),
    axis a ha, axis b hb]
  change extension (0 : F) (-1) 0 d -1-1 = _
  rw [smooth]
  ring

end Field

/-- The actual two-dimensional sum is evaluated using only residues modulo N. -/
noncomputable def grid (n : ℕ) [NeZero n] (a b d : ℤ) : ℤ :=
  ∑ z : ZMod n × ZMod n, jacobiSym (norm a b d (z.1.val : ℤ) z.2.val) n

theorem grid_crt (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (a b d : ℤ) :
    grid (p*q) a b d = ext (a : ZMod p) b d * ext (a : ZMod q) b d := by
  let e := ZMod.chineseRemainder cop
  let E := (e.toEquiv.prodCongr e.toEquiv).trans (Equiv.prodProdProdComm _ _ _ _)
  apply separated E
  rintro ⟨x,y⟩
  have hx : e x = (x.val : ℕ) := by rw [← map_natCast e, ZMod.natCast_zmod_val]
  have hy : e y = (y.val : ℕ) := by rw [← map_natCast e, ZMod.natCast_zmod_val]
  change jacobiSym _ _ = quadraticChar (ZMod p) (norm _ _ _ (e x).1 (e y).1) *
    quadraticChar (ZMod q) (norm _ _ _ (e x).2 (e y).2)
  rw [jacobi_crt, hx, hy]
  simp [norm, normCubic]

private theorem residue_class {r : ℕ} [h : Fact r.Prime] (odd : r ≠ 2) :
    (r % 4 = 3 ∧ trace (0 : ZMod r) (-1) 0 = 0 ∧ quadraticChar (ZMod r) (-1) = -1) ∨
    (r % 4 = 1 ∧ trace (0 : ZMod r) (-1) 0 % 4 = 2 ∧ quadraticChar (ZMod r) (-1) = 1) := by
  have parity := h.out.odd_of_ne_two odd
  obtain ⟨k, hk⟩ := parity
  by_cases hc : r % 4 = 3
  · exact Or.inl ⟨hc, PuncturedTrace.trace_zero hc,
      quadraticChar_neg_one_iff_not_isSquare.mpr (by simp [FiniteField.isSquare_neg_one_iff, hc])⟩
  · have ho : r % 4 = 1 := by omega
    have eq : trace (0 : ZMod r) (-1) 0 = QuarticTrace.trace (1 : ZMod r) := by
      unfold trace QuarticTrace.trace
      apply Finset.sum_congr rfl
      intro x _
      rw [← map_mul]
      congr 1
      unfold cubic
      ring
    exact Or.inr ⟨ho, eq ▸ QuarticTrace.base_parity r ho,
      (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr (by
        simp [FiniteField.isSquare_neg_one_iff, ho])⟩

private theorem last_factor {q : ℕ} [Fact q.Prime] (odd : q ≠ 2) :
    (2*(q:ℤ) - trace (0 : ZMod q) (-1) 0 ^ 2 - 2) % 8 = 4 := by
  rcases residue_class odd with ⟨qc, v, _⟩ | ⟨qc, v, _⟩
  · rw [v]; omega
  · let z := trace (0 : ZMod q) (-1) 0
    have form : z = 4 * (z/4) + 2 := by change z%4 = 2 at v; omega
    change (2*↑q-z^2-2)%8 = 4
    rw [form]
    ring_nf
    omega

/-- Four low bits are always zero, and bit 4 records one hidden character value. -/
theorem grid_bit (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)] (cop : p.Coprime q)
    (po : p ≠ 2) (qo : q ≠ 2) (a b d : ℤ)
    (differentP : (a : ZMod p) ≠ b) (differentQ : (a : ZMod q) ≠ b)
    (ap : f (a : ZMod p) ≠ 0) (bp : f (b : ZMod p) ≠ 0)
    (aq : f (a : ZMod q) ≠ 0) (bq : f (b : ZMod q) ≠ 0)
    (split : ∃ w : ZMod p, w ≠ 0 ∧ (d : ZMod p) = w ^ 2)
    (inert : quadraticChar (ZMod q) (d : ZMod q) = -1) :
    grid (p*q) a b d % 32 =
      if quadraticChar (ZMod p) (-(f (a : ZMod p) * f (b : ZMod p))) = -1 then 16 else 0 := by
  obtain ⟨w, wn, hw⟩ := split
  rw [grid_crt p q cop, hw, split_sum (by simpa only [ZMod.ringChar_zmod_n] using po) _ _ _ wn,
    inert_sum (by simpa only [ZMod.ringChar_zmod_n] using qo) _ _ _ inert differentQ aq bq, base_eval _ _ differentP, ZMod.card]
  let u := trace (0 : ZMod p) (-1) 0
  let k := 2*(q:ℤ) - trace (0 : ZMod q) (-1) 0 ^ 2 - 2
  have v : k%8 = 4 := last_factor qo
  have kform : k = 8*(k/8)+4 := by omega
  change ((u-_-_)^2*k)%32 = _
  rw [show -(f (a : ZMod p) * f (b : ZMod p)) = -1 * (f (a : ZMod p) * f (b : ZMod p)) by ring, map_mul, map_mul, kform]
  rcases residue_class po with ⟨_, uz, neg⟩ | ⟨_, bits, neg⟩
  · change u = 0 at uz
    rw [uz, neg]
    rcases quadraticChar_dichotomy ap with s | s <;> rcases quadraticChar_dichotomy bp with t | t <;>
      rw [s,t] <;> norm_num <;> omega
  · change u%4 = 2 at bits
    have uform : u = 4*(u/4)+2 := by omega
    rw [uform, neg]
    rcases quadraticChar_dichotomy ap with s | s <;> rcases quadraticChar_dichotomy bp with t | t <;>
      rw [s,t] <;> norm_num <;> ring_nf <;> omega

/-- Adjacent marks realize any unit square class via a linear fractional map. -/
theorem adjacent_identity {F : Type*} [Field F] (a : F) (different : 1-a ≠ 0) :
    let x := (1+2*a)/(1-a)
    f x*f (x+1) = a*(x*(x+1)*(x+2))^2 := by
  dsimp only
  unfold f
  field_simp
  ring

/-- The three lowest bits of the original singly marked grid are fixed for every eligible prime pair. -/
theorem single_mark_mod_eight (p q : ℕ) [hp : Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (po : p ≠ 2) (qo : q ≠ 2) (sp : (6 : ZMod p) ≠ 0) (sq : (6 : ZMod q) ≠ 0)
    (d : ℤ) (split : ∃ w : ZMod p, w ≠ 0 ∧ (d : ZMod p) = w ^ 2)
    (inert : quadraticChar (ZMod q) (d : ZMod q) = -1) :
    PuncturedTrace.grid (p*q) d % 8 = 5 := by
  rw [(PuncturedTrace.normalized_sums p q cop po qo sp sq d split inert).2.2,
    mul_pow (quadraticChar (ZMod q) 6), quadraticChar_sq_one sq, one_mul]
  let u := quadraticChar (ZMod p) 6 * trace (0 : ZMod p) (-1) 0
  obtain ⟨k, hk⟩ : Even u := (PuncturedTrace.trace_even (hp.out.odd_of_ne_two po)).mul_left _
  let v := trace (0 : ZMod q) (-1) 0
  have last : (2*(q:ℤ)-v^2-2)%8 = 4 := last_factor qo
  have next : (2*(q:ℤ)-v^2-1)%8 = 5 := by omega
  change ((u-1)^2 * (2*↑q-v^2-1))%8 = 5
  rw [Int.mul_emod, next]
  rcases (show k = 2*(k/2) ∨ k = 2*(k/2)+1 by omega) with h | h <;>
    rw [hk, h] <;> ring_nf <;> omega

/-- Substituting the rational parameter transfers the single local sign from the prescribed input. -/
theorem adjacent_character {F : Type*} [Field F] [Fintype F] [DecidableEq F] (a x : F)
    (different : 1-a ≠ 0) (parameter : x = (1+2*a)/(1-a)) (unit : x*(x+1)*(x+2) ≠ 0) :
    quadraticChar F (-(f x * f (x+1))) = quadraticChar F (-a) := by
  have h : f x * f (x+1) = a*(x*(x+1)*(x+2))^2 := by
    rw [parameter]
    exact adjacent_identity a different
  rw [h, ← neg_mul, map_mul, quadraticChar_sq_one' unit, mul_one]

/-- Worked examples of both possible fifth bits, with the selector and primes fixed. -/
theorem example_143 : grid 143 46 47 5 % 32 = 16 ∧ grid 143 106 107 5 % 32 = 0 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have sel : quadraticChar (ZMod 13) (5 : ℤ) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr (fun ⟨t, ht⟩ =>
      (by decide : ∀ t : ZMod 13, 5 ≠ t*t) t ht)
  have first := grid_bit 11 13 (by decide) (by decide) (by decide) 46 47 5 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ⟨4, by decide, by decide⟩ sel
  have second := grid_bit 11 13 (by decide) (by decide) (by decide) 106 107 5 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ⟨4, by decide, by decide⟩ sel
  have first_value : quadraticChar (ZMod 11) (-(f (46 : ZMod 11) * f (47 : ZMod 11))) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr (fun ⟨t, ht⟩ =>
      (by decide : ∀ t : ZMod 11, -(f 46*f 47) ≠ t*t) t ht)
  have second_value : -(f (106 : ZMod 11) * f (107 : ZMod 11)) = 1 := by decide
  simpa only [first_value, second_value, map_one, if_pos rfl, show (1:ℤ) ≠ -1 by decide,
    if_false] using And.intro first second

end PrimeFactors.MarkedTraceBit
