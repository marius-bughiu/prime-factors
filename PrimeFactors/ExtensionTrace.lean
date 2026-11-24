import PrimeFactors.PhaseCharacters
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

namespace PrimeFactors.ExtensionTrace

/-- The monic cubic with coefficients in descending order. -/
def cubic {R : Type*} [CommRing R] (a b c x : R) : R := x^3+a*x^2+b*x+c

/-- The norm of the cubic evaluated at x+y√d in R[T]/(T²−d). -/
def normCubic {R : Type*} [CommRing R] (a b c d x y : R) : R :=
  (x^3+3*x*d*y^2+a*(x^2+d*y^2)+b*x+c)^2 - d*(y*(3*x^2+d*y^2+2*a*x+b))^2

section Field
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def trace (a b c : F) : ℤ := ∑ x : F, quadraticChar F (cubic a b c x)

noncomputable def extension (a b c d : F) : ℤ :=
  ∑ z : F × F, quadraticChar F (normCubic a b c d z.1 z.2)

/-- Split fibers separate as two independent evaluations of the cubic. -/
theorem split_extension (odd : ringChar F ≠ 2) (a b c s : F) (nz : s ≠ 0) :
    extension a b c (s^2) = trace a b c ^ 2 := by
  classical
  have two : (2:F) ≠ 0 := Ring.two_ne_zero odd
  let e : F × F ≃ F × F := {
    toFun := fun ⟨x,y⟩ => (x+s*y,x-s*y)
    invFun := fun ⟨u,v⟩ => ((u+v)/2,(u-v)/(2*s))
    left_inv := by rintro ⟨x,y⟩; ext <;> dsimp <;> field_simp <;> ring
    right_inv := by rintro ⟨u,v⟩; ext <;> dsimp <;> field_simp <;> ring }
  let h (z : F × F) := quadraticChar F (cubic a b c z.1) * quadraticChar F (cubic a b c z.2)
  have point (z : F × F) : quadraticChar F (normCubic a b c (s^2) z.1 z.2) = h (e z) := by
    change _ = quadraticChar F (cubic a b c (z.1+s*z.2)) * quadraticChar F (cubic a b c (z.1-s*z.2))
    rw [← map_mul]
    congr 1
    unfold normCubic cubic
    ring
  unfold extension trace
  rw [Fintype.sum_equiv e _ h point, Fintype.sum_prod_type]
  simp only [h, ← Finset.mul_sum, ← Finset.sum_mul, sq]

/-- Weighting by the number of square roots changes a sum over y² into a sum over its values. -/
private theorem sum_squares (odd : ringChar F ≠ 2) (f : F → ℤ) :
    ∑ y : F, f (y^2) = ∑ t : F, (quadraticChar F t + 1) * f t := by
  rw [← Finset.sum_fiberwise Finset.univ (fun y : F => y^2) (fun y => f (y^2))]
  apply Finset.sum_congr rfl
  intro t _
  have fibers : ∀ y ∈ Finset.univ.filter (fun y : F => y^2=t), f (y^2) = f t :=
    fun y hy => congrArg f (Finset.mem_filter.mp hy).2
  rw [Finset.sum_congr rfl fibers, Finset.sum_const, nsmul_eq_mul]
  have h := quadraticChar_card_sqrts odd t
  simpa only [Set.toFinset_setOf] using congrArg (fun c : ℤ => c * f t) h

private theorem opposite_squares (odd : ringChar F ≠ 2) {d : F} (neg : quadraticChar F d = -1)
    (f : F → ℤ) : (∑ y : F, f (y^2)) + (∑ y : F, f (d*y^2)) = 2*∑ t : F, f t := by
  have nz : d ≠ 0 := fun h => by simp [h] at neg
  rw [sum_squares odd f, sum_squares odd (fun t => f (d*t))]
  have scaled : (∑ t : F, (quadraticChar F t+1)*f (d*t)) =
      ∑ t : F, (1-quadraticChar F t)*f t := by
    rw [← Equiv.sum_comp (Equiv.mulLeft₀ d nz) (fun t => (1-quadraticChar F t)*f t)]
    apply Finset.sum_congr rfl
    intro t _
    change _ = (1-quadraticChar F (d*t))*f (d*t)
    rw [map_mul,neg]
    ring
  rw [scaled, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- The quadratic-character sum of t²−k distinguishes exactly k=0. -/
private theorem shifted_square (odd : ringChar F ≠ 2) (k : F) :
    ∑ t : F, quadraticChar F (t^2-k) = (if k=0 then (Fintype.card F : ℤ) else 0)-1 := by
  by_cases z : k=0
  · subst k
    have term (t : F) : quadraticChar F (t^2-0) = 1-(if t=0 then 1 else 0) := by
      by_cases h : t=0
      · simp [h]
      · simp [h,quadraticChar_sq_one' h]
    simp_rw [term]
    simp [Finset.sum_sub_distrib]
  · rw [sum_squares odd (fun t => quadraticChar F (t-k))]
    simp_rw [add_mul, one_mul, ← map_mul, Finset.sum_add_distrib]
    have correlation := phaseCharacters_shift_sum (F := F) odd (a := 0) (b := -k)
      (by simpa using z)
    have shift := Equiv.sum_comp (Equiv.subRight k) (quadraticChar F)
    change (∑ t : F, quadraticChar F (t-k)) = ∑ t : F, quadraticChar F t at shift
    rw [shift, quadraticChar_sum_zero odd, add_zero]
    simpa [z,sub_eq_add_neg] using correlation

/-- After fixing norm u, the remaining quadratic has discriminant (a²−4b)(u−b)². -/
private def normQuadratic {R : Type*} [CommRing R] (a b u t : R) : R :=
  b*t^2+a*(u+b)*t+(u-b)^2+a^2*u

private theorem normQuadratic_sum (odd : ringChar F ≠ 2) (a b : F) (bn : b ≠ 0)
    (disc : a^2-4*b ≠ 0) (u : F) :
    ∑ t : F, quadraticChar F (normQuadratic a b u t) =
    quadraticChar F b * ((if u=b then (Fintype.card F : ℤ) else 0)-1) := by
  have two : (2:F) ≠ 0 := Ring.two_ne_zero odd
  let h := a*(u+b)/(2*b)
  let k := (a^2-4*b)*(u-b)^2/(2*b)^2
  have point (t : F) : normQuadratic a b u t = b*((t+h)^2-k) := by
    unfold normQuadratic h k
    field_simp
    ring
  simp_rw [point,map_mul (quadraticChar F) b,← Finset.mul_sum]
  have shift := Equiv.sum_comp (Equiv.addRight h) (fun t : F => quadraticChar F (t^2-k))
  change (∑ t : F, quadraticChar F ((t+h)^2-k)) = _ at shift
  rw [shift, shifted_square odd k]
  have key : k=0 ↔ u=b := by
    simp [k,disc,bn,two,sub_eq_zero]
  rw [if_congr key rfl rfl]

private theorem normQuadratic_total (odd : ringChar F ≠ 2) (a b : F) (bn : b ≠ 0)
    (disc : a^2-4*b ≠ 0) :
    ∑ u : F, ∑ t : F, quadraticChar F (u * normQuadratic a b u t) = Fintype.card F := by
  simp_rw [map_mul (quadraticChar F) _ (normQuadratic ..), ← Finset.mul_sum,
    normQuadratic_sum odd a b bn disc]
  have term (u : F) :
      quadraticChar F u * (quadraticChar F b * ((if u=b then (Fintype.card F : ℤ) else 0)-1)) =
      (if u=b then (Fintype.card F : ℤ) else 0)-quadraticChar F u * quadraticChar F b := by
    by_cases h : u=b
    · subst u
      rw [if_pos rfl]
      nlinarith [quadraticChar_sq_one bn]
    · simp [h]
  simp_rw [term, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [quadraticChar_sum_zero odd]
  simp

/-- For every smooth cubic X(X²+aX+b), including irreducible quadratic factors, the
degree-two extension character sum is 2|F| minus the square of the base sum. -/
theorem root_inert (odd : ringChar F ≠ 2) (a b : F) {d : F} (bn : b ≠ 0)
    (disc : a^2-4*b ≠ 0) (neg : quadraticChar F d = -1) :
    extension a b 0 d = 2*(Fintype.card F : ℤ)-trace a b 0 ^ 2 := by
  classical
  have two : (2:F) ≠ 0 := Ring.two_ne_zero odd
  let e : F × F ≃ F × F := {
    toFun := fun ⟨x,s⟩ => (x^2-s,2*x)
    invFun := fun ⟨u,t⟩ => (t/2,(t/2)^2-u)
    left_inv := by rintro ⟨x,s⟩; ext <;> dsimp <;> field_simp
    right_inv := by rintro ⟨u,t⟩; ext <;> dsimp <;> field_simp }
  let w (x s : F) := quadraticChar F ((x^2-s)*normQuadratic a b (x^2-s) (2*x))
  have point (z : F × F) : ∀ d' : F, quadraticChar F (normCubic a b 0 d' z.1 z.2) = w z.1 (d'*z.2^2) := by
    intro d'
    dsimp [w]
    congr 1
    unfold normCubic normQuadratic
    ring
  have all : (∑ x : F, ∑ s : F, w x s) = Fintype.card F := by
    rw [← Fintype.sum_prod_type (fun z : F × F => w z.1 z.2),
      Fintype.sum_equiv e (fun z : F × F => w z.1 z.2)
        (fun z => quadraticChar F (z.1*normQuadratic a b z.1 z.2)) (fun z => by cases z; rfl),
      Fintype.sum_prod_type]
    exact normQuadratic_total odd a b bn disc
  have pair : extension a b 0 1 + extension a b 0 d = 2*(Fintype.card F : ℤ) := by
    unfold extension
    simp_rw [point, Fintype.sum_prod_type, one_mul]
    rw [← Finset.sum_add_distrib, ← all, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact opposite_squares odd neg (w x)
  rw [show extension a b 0 1 = trace a b 0 ^ 2 by
    simpa using split_extension odd a b 0 1 one_ne_zero] at pair
  linarith

/-- The visible roots of the Legendre family yield good reduction whenever l differs from 0,1. -/
theorem legendre_inert (odd : ringChar F ≠ 2) {l d : F} (lz : l ≠ 0) (lo : l ≠ 1)
    (neg : quadraticChar F d = -1) :
    extension (-(1+l)) l 0 d = 2*(Fintype.card F : ℤ)-trace (-(1+l)) l 0 ^ 2 := by
  apply root_inert odd _ _ lz _ neg
  rw [show (-(1+l))^2-4*l = (l-1)^2 by ring]
  exact pow_ne_zero 2 (sub_ne_zero.mpr lo)

/-- The known root x=0 removes one summand, so every trace is strictly smaller than |F|. -/
theorem trace_root_bound (a b : F) : |trace a b 0| < Fintype.card F := by
  classical
  have term (x : F) : |quadraticChar F (cubic a b 0 x)| ≤ 1-(if x=0 then 1 else 0) := by
    by_cases zero : x=0
    · simp [zero,cubic]
    rw [if_neg zero, sub_zero]
    by_cases root : cubic a b 0 x = 0
    · simp [root]
    rcases quadraticChar_dichotomy root with h | h <;> simp [h]
  calc
    _ ≤ ∑ x : F, |quadraticChar F (cubic a b 0 x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : F, (1-(if x=0 then 1 else 0)) := Finset.sum_le_sum (fun x _ => term x)
    _ < _ := by simp [Finset.sum_sub_distrib]

end Field

noncomputable def baseSum (n : ℕ) [NeZero n] (a b c : ℤ) : ℤ :=
  ∑ x : ZMod n, jacobiSym (cubic a b c (x.val : ℤ)) n

noncomputable def normSum (n : ℕ) [NeZero n] (a b c d : ℤ) : ℤ :=
  ∑ z : ZMod n × ZMod n, jacobiSym (normCubic a b c d (z.1.val : ℤ) z.2.val) n

/-- Decomposition of a public Jacobi symbol across the two prime residue fields. -/
theorem jacobi_crt (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (z : ℤ) :
    jacobiSym z (p*q) = quadraticChar (ZMod p) z * quadraticChar (ZMod q) z := by
  rw [jacobiSym.mul_right' _ hp.out.ne_zero hq.out.ne_zero,
    ← jacobiSym.legendreSym.to_jacobiSym p, ← jacobiSym.legendreSym.to_jacobiSym q]
  rfl

/-- A product weight over a finite CRT bijection separates multiplicatively. -/
theorem separated {X L R : Type*} [Fintype X] [Fintype L] [Fintype R]
    (e : X ≃ L × R) (f : X → ℤ) (g : L → ℤ) (h : R → ℤ)
    (term : ∀ x, f x = g (e x).1 * h (e x).2) :
    ∑ x, f x = (∑ u, g u) * ∑ v, h v := by
  rw [Fintype.sum_equiv e _ (fun z => g z.1 * h z.2) term, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

theorem baseSum_crt (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (a b c : ℤ) :
    baseSum (p*q) a b c = trace (a : ZMod p) b c * trace (a : ZMod q) b c := by
  let e := ZMod.chineseRemainder cop
  apply separated e.toEquiv
  intro x
  have hx : e x = (x.val : ℕ) := by rw [← map_natCast e, ZMod.natCast_zmod_val]
  change jacobiSym _ _ = quadraticChar (ZMod p) (cubic _ _ _ (e x).1) *
    quadraticChar (ZMod q) (cubic _ _ _ (e x).2)
  rw [jacobi_crt, hx]
  simp [cubic]

theorem normSum_crt (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (a b c d : ℤ) :
    normSum (p*q) a b c d =
      extension (a : ZMod p) b c d * extension (a : ZMod q) b c d := by
  let e := ZMod.chineseRemainder cop
  let E := (e.toEquiv.prodCongr e.toEquiv).trans (Equiv.prodProdProdComm _ _ _ _)
  apply separated E
  rintro ⟨x,y⟩
  have hx : e x = (x.val : ℕ) := by rw [← map_natCast e, ZMod.natCast_zmod_val]
  have hy : e y = (y.val : ℕ) := by rw [← map_natCast e, ZMod.natCast_zmod_val]
  change jacobiSym _ _ = quadraticChar (ZMod p) (normCubic _ _ _ _ (e x).1 (e y).1) *
    quadraticChar (ZMod q) (normCubic _ _ _ _ (e x).2 (e y).2)
  rw [jacobi_crt, hx, hy]
  simp [normCubic]

/-- In this sign convention the inert degree-two term is 2q−v². -/
theorem extract_identity (q : ℕ) (u v A B : ℤ) (base : A = u*v)
    (ext : B = u^2 * (2*q-v^2)) : B+A^2 = q*(2*u^2) := by
  rw [base,ext]
  ring

theorem extract_gcd {p q : ℕ} (hp : p.Prime) (large : 2 < p) {u v A B : ℤ}
    (base : A = u*v) (ext : B = u^2 * (2*q-v^2)) (nonzero : u ≠ 0)
    (small : u.natAbs < p) : (B+A^2).natAbs.gcd (p*q) = q := by
  have ct : p.Coprime u.natAbs := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr nonzero) small)
  have c2 : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) large)
  rw [extract_identity q u v A B base ext, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow,
    Int.natAbs_natCast, show (2:ℤ).natAbs = 2 by decide, Nat.mul_comm p q, Nat.gcd_mul_left,
    (c2.mul_right (ct.pow_right 2)).symm.gcd_eq_one, mul_one]

/-- For a nonsingular elliptic curve the conventional Hasse inequality supplies this premise.
The inequality suffices when the split-prime trace is nonzero and p>4. -/
theorem small_of_hasse {p : ℕ} {u : ℤ} (large : 4 < p) (hasse : u^2 ≤ 4*p) :
    u.natAbs < p := by
  by_contra! h
  have hc : (p : ℤ) ≤ (u.natAbs : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at hc
  have pge : (5:ℤ) ≤ p := by exact_mod_cast large
  have sqh := pow_le_pow_left₀ (Int.natCast_nonneg p) hc 2
  rw [sq_abs] at sqh
  nlinarith [mul_nonneg (by linarith : 0≤(p:ℤ)-5) (Int.natCast_nonneg p)]

/-- A product-only signal. Both complete sums are integers computable from n,l,d. -/
noncomputable def legendreSignal (n : ℕ) [NeZero n] (l d : ℤ) : ℤ :=
  normSum n (-(1+l)) l 0 d + baseSum n (-(1+l)) l 0 ^ 2

/-- Public complete sums for any cubic X(X²+aX+b) that is smooth at the inert prime.
No elliptic-curve point-count theorem is an input to this identity. -/
theorem rootSignal_eq (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (po : p ≠ 2) (qo : q ≠ 2) (a b d : ℤ)
    (bn : (b : ZMod q) ≠ 0) (disc : (a : ZMod q)^2 - 4*(b : ZMod q) ≠ 0)
    (split : quadraticChar (ZMod p) (d : ZMod p) = 1)
    (inert : quadraticChar (ZMod q) (d : ZMod q) = -1) :
    normSum (p*q) a b 0 d + baseSum (p*q) a b 0 ^ 2 =
      (q : ℤ) * (2 * trace (a : ZMod p) b 0 ^ 2) := by
  have pchar : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have qchar : ringChar (ZMod q) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have dn : (d : ZMod p) ≠ 0 := fun h => by simp [h] at split
  obtain ⟨s,hs⟩ := (quadraticChar_one_iff_isSquare dn).mp split
  have sn : s ≠ 0 := fun h => dn (by simp [hs,h])
  have de : (d : ZMod p) = s^2 := by simpa [sq] using hs
  rw [normSum_crt p q cop, baseSum_crt p q cop]
  simp only [Int.cast_zero]
  rw [de,split_extension pchar _ _ _ s sn,root_inert qchar _ _ bn disc inert,ZMod.card]
  ring

/-- The complete signal equals twice the inert prime times the squared split-prime trace.
Only the inert prime needs the three branch points to be distinct for this identity. -/
theorem legendreSignal_eq (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (po : p ≠ 2) (qo : q ≠ 2) (l d : ℤ)
    (lz : (l : ZMod q) ≠ 0) (lo : (l : ZMod q) ≠ 1)
    (split : quadraticChar (ZMod p) (d : ZMod p) = 1)
    (inert : quadraticChar (ZMod q) (d : ZMod q) = -1) :
    legendreSignal (p*q) l d = (q : ℤ) * (2 * trace (-(1+(l : ZMod p))) l 0 ^ 2) := by
  have ds : ((-(1+l) : ℤ) : ZMod q)^2-4*l ≠ 0 := by
    push_cast
    rw [show (-(1+(l : ZMod q)))^2-4*l = (l-1)^2 by ring]
    exact pow_ne_zero 2 (sub_ne_zero.mpr lo)
  simpa only [legendreSignal,Int.cast_neg,Int.cast_add,Int.cast_one] using
    rootSignal_eq p q cop po qo (-(1+l)) l d lz ds split inert

/-- Under the local signs the gcd is exactly the inert prime whenever the signal is nonzero.
If zero, gcd(0,N)=N. This detects unsuccessful parameters from the public data. -/
theorem legendreSignal_gcd (p q : ℕ) [hp : Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (po : p ≠ 2) (qo : q ≠ 2) (l d : ℤ)
    (lz : (l : ZMod q) ≠ 0) (lo : (l : ZMod q) ≠ 1)
    (split : quadraticChar (ZMod p) (d : ZMod p) = 1)
    (inert : quadraticChar (ZMod q) (d : ZMod q) = -1)
    (nonzero : legendreSignal (p*q) l d ≠ 0) :
    (legendreSignal (p*q) l d).natAbs.gcd (p*q) = q := by
  let u := trace (-(1+(l : ZMod p))) l 0
  have formula := legendreSignal_eq p q cop po qo l d lz lo split inert
  change legendreSignal (p*q) l d = q*(2*u^2) at formula
  have un : u ≠ 0 := fun h => nonzero (by simp [formula,h])
  have small := trace_root_bound (-(1+(l : ZMod p))) l
  change |u| < _ at small
  rw [ZMod.card, ← Int.natCast_natAbs] at small
  have nsmall : u.natAbs < p := by exact_mod_cast small
  rw [formula]
  simpa using extract_gcd (q := q) hp.out (by have := hp.out.two_le; omega)
    (u := u) (v := 0) (A := 0) (B := q*(2*u^2)) (by ring) (by ring) un nsmall

/-- Public good-reduction check at either factor of the product. -/
private theorem good_parameter {n p : ℕ} [Fact p.Prime] (factor : p ∣ n) (l : ℤ)
    (good : (l*(l-1)).natAbs.Coprime n) : (l : ZMod p) ≠ 0 ∧ (l : ZMod p) ≠ 1 := by
  have cp := good.coprime_dvd_right factor
  have unit : ¬p ∣ (l*(l-1)).natAbs := (Nat.Prime.coprime_iff_not_dvd Fact.out).mp cp.symm
  have nz : ((l*(l-1) : ℤ) : ZMod p) ≠ 0 := by
    intro h
    exact unit (Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h))
  push_cast at nz
  exact ⟨(mul_ne_zero_iff.mp nz).1, sub_ne_zero.mp (mul_ne_zero_iff.mp nz).2⟩

/-- A usable public statement without knowing which factor splits. If the selected parameter
gives nonzero signal, the gcd returns one of the two factors. All selection tests use n alone. -/
theorem split_of_jacobi (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (po : p ≠ 2) (qo : q ≠ 2) (l d : ℤ)
    (good : (l*(l-1)).natAbs.Coprime (p*q)) (separator : jacobiSym d (p*q) = -1)
    (nonzero : legendreSignal (p*q) l d ≠ 0) :
    let g := (legendreSignal (p*q) l d).natAbs.gcd (p*q)
    g = p ∨ g = q := by
  rw [jacobi_crt] at separator
  have pd : (d : ZMod p) ≠ 0 := fun h => by simp [h] at separator
  rcases quadraticChar_dichotomy pd with pos | neg
  · right
    have qneg : quadraticChar (ZMod q) (d : ZMod q) = -1 := by simpa only [pos,one_mul] using separator
    obtain ⟨lz,lo⟩ := good_parameter (dvd_mul_left q p) l good
    exact legendreSignal_gcd p q cop po qo l d lz lo pos qneg nonzero
  · left
    have qpos : quadraticChar (ZMod q) (d : ZMod q) = 1 := by rw [neg,neg_one_mul] at separator; omega
    obtain ⟨lz,lo⟩ := good_parameter (dvd_mul_right p q) l good
    letI : NeZero (q*p) := ⟨Nat.mul_ne_zero hq.out.ne_zero hp.out.ne_zero⟩
    have swap : legendreSignal (q*p) l d ≠ 0 := by simpa only [Nat.mul_comm q p] using nonzero
    simpa only [Nat.mul_comm q p] using legendreSignal_gcd q p cop.symm qo po l d lz lo qpos neg swap

end PrimeFactors.ExtensionTrace
