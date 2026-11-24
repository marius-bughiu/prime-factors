import PrimeFactors.MaskedRelations
import PrimeFactors.RootIntervalSlope
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PrimeFactors.NormOrbit

/-- Reducing wrt X² = −d produces one affine expression valid at every root,
in arbitrary characteristic and over rings with zero divisors. -/
theorem polynomial_affine {R : Type*} [CommRing R] (d : R) (P : Polynomial R) :
    ∃ c b : R, ∀ z : R, z^2 = -d → P.eval z = c+b*z := by
  induction P using Polynomial.induction_on with
  | C a => exact ⟨a, 0, fun z _ => by simp⟩
  | add P Q ih jh =>
    obtain ⟨c,b,h⟩ := ih
    obtain ⟨e,f,g⟩ := jh
    exact ⟨c+e,b+f,fun z hz => by rw [Polynomial.eval_add,h z hz,g z hz]; ring⟩
  | monomial n a ih =>
    obtain ⟨c,b,h⟩ := ih
    refine ⟨-d*b,c,fun z hz => ?_⟩
    rw [pow_succ, ← mul_assoc, Polynomial.eval_mul, h z hz, Polynomial.eval_X]
    linear_combination b*hz

/-- Conjugating a denominator reduces a rational map to the same affine
form divided by a scalar. That scalar is tested for invertibility by gcd. -/
theorem conjugate_denominator {R : Type*} [CommRing R] (r s c b z d : R) (root : z^2 = -d) :
    (c+b*z)*(c-b*z) = c^2+d*b^2 ∧
    (r+s*z)*(c-b*z) = (r*c+d*s*b)+(s*c-r*b)*z := by
  constructor
  · linear_combination -b^2*root
  · linear_combination -s*b*root

/-- Uniform validity on the two global signs already forces both coefficient
equations. The known root supplies no hidden prime labels. -/
theorem coefficient_equations {R : Type*} [CommRing R] (c b z d : R)
    (two : IsUnit (2 : R)) (unit : IsUnit z)
    (root : z^2 = -d) (pos : (c+b*z)^2 = -d) (neg : (c-b*z)^2 = -d) :
    c*b=0 ∧ c^2-d*b^2 = -d := by
  have zero : (2*2*z)*(c*b)=0 := by linear_combination pos - neg
  have cb := ((two.mul two).mul unit).mul_right_inj.mp (zero.trans (mul_zero _).symm)
  refine ⟨cb, ?_⟩
  linear_combination pos - b^2*root - 2*z*cb

/-- The only uniform characteristic-zero field identities that square to
a strictly negative rational are sign changes of the generator. -/
theorem rational_identity (c b d : ℚ) (dp : 0<d)
    (cross : c*b=0) (constant : c^2-d*b^2 = -d) : c=0 ∧ (b=1 ∨ b= -1) := by
  have cz : c=0 := (mul_eq_zero.mp cross).resolve_right (by
    intro bz
    rw [bz] at constant
    nlinarith [sq_nonneg c])
  refine ⟨cz, ?_⟩
  rw [cz] at constant
  have h : d*(b^2-1)=0 := by linear_combination -constant
  have sq := (mul_eq_zero.mp h).resolve_left dp.ne'
  exact sq_eq_one_iff.mp (sub_eq_zero.mp sq)

private theorem nonunit_gcd {N : ℕ} [NeZero N] {x : ZMod N} (h : x≠0) (nu : ¬ IsUnit x) :
    1 < x.val.gcd N ∧ x.val.gcd N < N := by
  have gpos := Nat.gcd_pos_of_pos_right x.val (NeZero.pos N)
  have n1 : x.val.gcd N≠1 := by
    intro hc
    apply nu
    simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime _ _).mpr hc
  have xpos := Nat.pos_of_ne_zero (fun eq => h ((ZMod.val_eq_zero x).mp eq))
  exact ⟨by omega, (Nat.le_of_dvd xpos (Nat.gcd_dvd_left ..)).trans_lt (ZMod.val_lt x)⟩

/-- A modular root transformation reduced to c+bX is a constant root or a
global sign, or one of two specified coefficient gcds already splits N.
All four branches can be checked before evaluating the map at a root. -/
theorem classify {N : ℕ} [NeZero N] (c b d : ZMod N) (unit : IsUnit d)
    (cross : c*b=0) (constant : c^2-d*b^2 = -d) :
    (b=0 ∧ c^2 = -d) ∨ (c=0 ∧ (b=1 ∨ b= -1)) ∨
    (1<c.val.gcd N ∧ c.val.gcd N<N) ∨
    (1<(b-1).val.gcd N ∧ (b-1).val.gcd N<N) := by
  by_cases cz : c=0
  · have same : d*b^2 = d*1 := by rw [cz] at constant; linear_combination -constant
    have sq := unit.mul_right_inj.mp same
    by_cases plus : b=1
    · exact Or.inr (Or.inl ⟨cz,Or.inl plus⟩)
    by_cases minus : b= -1
    · exact Or.inr (Or.inl ⟨cz,Or.inr minus⟩)
    exact Or.inr (Or.inr (Or.inr (maskedRelations_split (y:=1) (by simpa using sq) plus minus)))
  by_cases cu : IsUnit c
  · have bz := cu.mul_right_inj.mp (cross.trans (mul_zero _).symm)
    exact Or.inl ⟨bz,by simpa [bz] using constant⟩
  exact Or.inr (Or.inr (Or.inl (nonunit_gcd cz cu)))

/-- Multiplying a point by c+e√(−d) preserves its modular direction up to
any common conjugation. If the new denominator fails to be a unit, the
scalar norm was already a nonunit. -/
theorem norm_product {R : Type*} [CommRing R] (x a c e d : R) (onCone : x^2+d*a^2=0) :
    (x*c-d*a*e)*a = x*(a*c+x*e) ∧
    (a*c+x*e)*(a*c-x*e) = a^2*(c^2+d*e^2) := by
  constructor
  · linear_combination -e*onCone
  · linear_combination -e^2*onCone

/-- For a linear norm similitude the determinant already supplies the
orientation. Its square is the square of the multiplier. -/
theorem similitude {R : Type*} [CommRing R] (A B C E d k z : R) (du : IsUnit d)
    (left : A^2+d*C^2=k) (middle : A*B+d*C*E=0) (right : B^2+d*E^2=d*k)
    (root : z^2 = -d) :
    (A*E-B*C)^2=k^2 ∧ (A*E-B*C)*(A*z+B)=k*z*(C*z+E) := by
  constructor
  · apply du.mul_right_inj.mp
    linear_combination (B^2+d*E^2)*left + k*right - (A*B+d*C*E)*middle
  · linear_combination (E*z)*left - (C*z-E)*middle - C*right - k*C*root

/-- A denominator whose symbolic norm vanishes, but whose linear coefficient
is a unit, is proportional to X+w for an explicitly available root w.
If numerator and denominator satisfy the root identity, the quotient on
its domain is a publicly known constant. A squarefree modulus has the
required property that an element with square zero vanishes. -/
theorem singular_denominator {R : Type*} [CommRing R] (w r s d : R) (root : w^2= -d)
    (nonzero : IsUnit (w+w)) (reduced : ∀ x : R, x^2=0 → x=0)
    (valid : ∀ z : R, z^2= -d → (r+s*z)^2= -d*(z+w)^2) :
    s^2= -d ∧ ∀ z : R, r+s*z=s*(z+w) := by
  have vanishes : (r-s*w)^2=0 := by
    simpa [sub_eq_add_neg] using valid (-w) (by simpa using root)
  have h := sub_eq_zero.mp (reduced _ vanishes)
  have prop (z : R) : r+s*z=s*(z+w) := by rw [h]; ring
  refine ⟨?_,prop⟩
  have eqn := valid w root
  rw [prop w, mul_pow, mul_comm (s^2), mul_comm (-d)] at eqn
  exact (nonzero.pow 2).mul_right_inj.mp eqn

/-- A root at just one hidden divisor forces a small positive norm in a
public box. The signed coordinate can be replaced by its absolute value
when the norm is tested. -/
theorem local_box {p L : ℕ} [NeZero p] (d z : ℤ) (lp : 0<L) (ltp : L<p)
    (size : p<(L+1)^2) (zu : IsUnit (z : ZMod p)) (root : (z : ZMod p)^2= -d) :
    ∃ (a : ℕ) (t : ℤ), 1≤a ∧ a≤L ∧ t≠0 ∧ |t|≤L ∧
      (t : ZMod p)^2+d*(a : ZMod p)^2=0 := by
  obtain ⟨a,ap,al,j,close⟩ := boundedSlope_exists p L z (NeZero.pos p) lp
  let t : ℤ := a*z-p*j
  have close' : |t| *((L : ℤ)+1)≤p := close
  have large : (p : ℤ)<((L : ℤ)+1)*((L : ℤ)+1) := by
    exact_mod_cast (show p < (L+1)*(L+1) by simpa [pow_two] using size)
  have bound : |t|<(L : ℤ)+1 := lt_of_mul_lt_mul_right
    (close'.trans_lt large) (by positivity)
  have tz : (t : ZMod p)=(a : ZMod p)*(z : ZMod p) := by dsimp [t]; push_cast; simp
  have nz : t≠0 := by
    intro bad
    rw [bad, Int.cast_zero, mul_comm] at tz
    have az : (a : ZMod p)=0 := zu.mul_right_inj.mp (tz.symm.trans (mul_zero _).symm)
    have small := lt_of_le_of_lt al ltp
    have dv := (ZMod.natCast_zmod_eq_zero_iff_dvd a p).mp az
    exact (Nat.not_dvd_of_pos_of_lt (by omega) small) dv
  refine ⟨a,t,ap,al,nz,by omega,?_⟩
  rw [tz,mul_pow,root]
  ring

/-- Every odd collection of local nonsquares has a nonsquare product.
An odd square-product relation among signed discriminants therefore gives
a local cover, independently of the modulus size. -/
theorem odd_square_cover {F : Type*} [Field F] [Fintype F] (ds : List F)
    (odd : Odd ds.length) (square : IsSquare ds.prod) : ∃ x ∈ ds, IsSquare x := by
  classical
  by_contra! allbad
  have eval (xs : List F) (bad : ∀ x ∈ xs, ¬ IsSquare x) :
      quadraticChar F xs.prod=(-1 : ℤ)^xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.prod_cons, List.length_cons, map_mul, pow_succ]
      rw [quadraticChar_neg_one_iff_not_isSquare.mpr (bad x (by simp)),
        ih (fun y h => bad y (by simp [h]))]
      ring
  have char := eval ds allbad
  rw [odd.neg_one_pow] at char
  exact (quadraticChar_neg_one_iff_not_isSquare.mp char) square

/-- Among −1, 2, and −2 at least one is a square at every odd prime. -/
theorem three_discriminants {p : ℕ} [Fact p.Prime] (odd : (2 : ZMod p)≠0) :
    IsSquare (-1 : ZMod p) ∨ IsSquare (2 : ZMod p) ∨ IsSquare (-2 : ZMod p) := by
  by_cases h : IsSquare (-1 : ZMod p)
  · exact Or.inl h
  by_cases j : IsSquare (2 : ZMod p)
  · exact Or.inr (Or.inl j)
  apply Or.inr <| Or.inr <| (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr odd)).mp ?_
  rw [show (-2 : ZMod p)=(-1)*2 by ring, map_mul,
    quadraticChar_neg_one_iff_not_isSquare.mpr h,
    quadraticChar_neg_one_iff_not_isSquare.mpr j]
  decide

/-- The indefinite member u²−2v² does not vanish on a positive grid.
The exponent of 2 on its two sides would have opposite parities. -/
theorem unequal_squares {u v : ℕ} (vp : 0<v) : u^2 ≠ 2*v^2 := by
  intro eqn
  have fac := congrArg (fun k : ℕ => k.factorization 2) eqn
  simp only [Nat.factorization_mul (by decide : 2≠0) (pow_ne_zero _ vp.ne'),
    Nat.factorization_pow, Nat.Prime.factorization_self Nat.prime_two,
    Finsupp.add_apply,Finsupp.smul_apply,nsmul_eq_mul] at fac
  omega

/-- Any nonzero signed leaf smaller than N and divisible by a hidden
nontrivial divisor immediately splits N. -/
theorem leaf_gcd {N p : ℕ} {V : ℤ} (pd : p∣N) (large : 1<p) (pv : (p : ℤ)∣V)
    (vn : V≠0) (size : V.natAbs<N) :
    1<V.natAbs.gcd N ∧ V.natAbs.gcd N<N := by
  have vpos : 0<V.natAbs := Nat.pos_of_ne_zero (by simpa using vn)
  have ng := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left N vpos)
    (Nat.dvd_gcd (Int.natCast_dvd.mp pv) pd)
  exact ⟨large.trans_le ng, (Nat.le_of_dvd vpos (Nat.gcd_dvd_left ..)).trans_lt size⟩

/-- For any odd hidden prime p in the covered width, one of the three
public forms and one point of the public grid give a proper gcd. Both
coordinates are positive and neither the input nor the search needs a
square root at p. -/
theorem guaranteed_box {N p R : ℕ} [Fact p.Prime] (odd : (2 : ZMod p)≠0)
    (pd : p∣N) (rp : 0<R) (short : R<p) (wide : p<(R+1)^2) (safe : 3*R^2<N) :
    ∃ (d : ℤ) (u v : ℕ), (d=1 ∨ d=2 ∨ d= -2) ∧
      1≤u ∧ u≤R ∧ 1≤v ∧ v≤R ∧
      1<((u : ℤ)^2+d*v^2).natAbs.gcd N ∧ ((u : ℤ)^2+d*v^2).natAbs.gcd N<N := by
  have choice : ∃ d : ℤ, (d=1 ∨ d=2 ∨ d= -2) ∧ IsSquare (-(d : ZMod p)) := by
    rcases three_discriminants odd with h|h|h
    · exact ⟨1,Or.inl rfl,by simpa using h⟩
    · exact ⟨-2,Or.inr (Or.inr rfl),by simpa using h⟩
    · exact ⟨2,Or.inr (Or.inl rfl),by simpa using h⟩
  obtain ⟨d,choice,w,hw⟩ := choice
  let z : ℤ := w.val
  have wz : (z : ZMod p)=w := by dsimp [z]; simp
  have wzsq : (z : ZMod p)^2= -d := by rw [wz,pow_two]; exact hw.symm
  have wu : IsUnit (z : ZMod p) := by
    apply isUnit_iff_ne_zero.mpr
    intro zero
    rw [zero,zero_pow (by decide),zero_eq_neg] at wzsq
    have dn : (d : ZMod p)≠0 := by
      rcases choice with rfl|rfl|rfl
      · exact_mod_cast (one_ne_zero : (1 : ZMod p)≠0)
      · exact_mod_cast odd
      · simpa using neg_ne_zero.mpr odd
    exact dn wzsq
  obtain ⟨v,t,vp,vr,tn,tr,eqn⟩ := local_box d z rp short wide wu wzsq
  let u := t.natAbs
  have us : (u : ℤ)^2=t^2 := by dsimp [u]; rw [Int.natCast_natAbs,sq_abs]
  have ur : u≤R := by exact_mod_cast (show (u : ℤ)≤R by simpa [u] using tr)
  have up : 0<u := Nat.pos_of_ne_zero (by simpa [u] using tn)
  let V : ℤ := (u : ℤ)^2+d*v^2
  have hpV : (p : ℤ)∣V := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd V p).mp
    dsimp [V]
    rw [us]
    push_cast
    exact eqn
  have vZ : 0<(v : ℤ) := by exact_mod_cast (show 0<v by omega)
  have nz : V≠0 := by
    dsimp [V]
    rcases choice with rfl|rfl|rfl
    · positivity
    · positivity
    · intro bad
      apply unequal_squares vp
      exact_mod_cast (show (u : ℤ)^2=2*(v : ℤ)^2 by linarith)
  have uu : (u : ℤ)^2≤(R : ℤ)^2 := by exact_mod_cast Nat.pow_le_pow_left ur 2
  have vv : (v : ℤ)^2≤(R : ℤ)^2 := by exact_mod_cast Nat.pow_le_pow_left vr 2
  have absV : |V|≤3*(R : ℤ)^2 := by
    dsimp [V]
    rcases choice with rfl|rfl|rfl <;> apply abs_le.mpr <;>
      constructor <;> nlinarith [sq_nonneg (u : ℤ),sq_nonneg (v : ℤ)]
  have size : V.natAbs<N := by
    have small : |V|<(N : ℤ) := absV.trans_lt (by exact_mod_cast safe)
    exact_mod_cast (show (V.natAbs : ℤ)<N by simpa using small)
  exact ⟨d,u,v,choice,up,ur,vp,vr,leaf_gcd pd (Fact.out : p.Prime).one_lt hpV nz size⟩

/-- Positive norm grid on 77. The coefficient 2 finds the prime 11 even
though −2 is a nonresidue at 7, so the full modulus has no such root. -/
theorem box_example :
    Nat.gcd ((1^2+2)*(2^2+2)*(3^2+2)*(4^2+2)) 77=11 ∧
    (∀ x : ZMod 7, x^2 ≠ -2) ∧ (3 : ZMod 11)^2= -2 := by decide

/-- On an inert side every grid value stays nonzero, even if the public
coefficient is large. Thus only the split prime can divide a row product
when the Jacobi symbol is negative. -/
theorem inert_leaf {F : Type*} [Field F] (u v D : F) (vp : v≠0) (inert : ¬ IsSquare D) :
    u^2-D*v^2≠0 := by
  intro hit
  apply inert
  refine ⟨u/v,?_⟩
  rw [← pow_two,div_pow,eq_div_iff (pow_ne_zero _ vp)]
  exact (sub_eq_zero.mp hit).symm

/-- Positive short ratios coinciding up to sign modulo p already give
the same ordinary rational number. This proves the no-collision step in
the exact random-coefficient probability. -/
theorem short_ratio {p A B C E : ℕ} [Fact p.Prime]
    (sp : 0<A*E+B*C) (small : A*E+B*C<p)
    (modular : ((A : ZMod p)*E)^2=((B : ZMod p)*C)^2) : A*E=B*C := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp modular with h|h
  · have a : A*E<p := by omega
    have b : B*C<p := by omega
    exact ((ZMod.natCast_eq_natCast_iff ..).mp (by simpa only [Nat.cast_mul] using h)).eq_of_lt_of_lt a b
  · have zero : ((A*E+B*C : ℕ) : ZMod p)=0 := by push_cast; rw [h,neg_add_cancel]
    exact ((Nat.not_dvd_of_pos_of_lt sp small) ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp zero)).elim

/-- No small integer norm can have two distinct prime divisors at least X.
This bounds coverage among the hidden primes even when their root choices
are adapted to the input. -/
theorem one_large_prime {X m p q : ℕ} (pos : 0<m) (size : m<X^2)
    (hp : p.Prime) (hq : q.Prime) (lp : X≤p) (lq : X≤q)
    (divp : p∣m) (divq : q∣m) : p=q := by
  by_contra ne
  have div := (hp.coprime_iff_not_dvd.mpr (fun h => ne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))).mul_dvd_of_dvd_of_dvd divp divq
  have low : X*X ≤ p*q := Nat.mul_le_mul lp lq
  have high := Nat.le_of_dvd pos div
  rw [pow_two] at size
  omega

/-- With small bounded coefficients every nonzero value under the
smaller prime is coprime to the product, even when chosen adaptively. -/
theorem box_coprime {p q H C u v : ℕ} {d : ℤ} (hp : p.Prime) (hq : q.Prime)
    (uH : u≤H) (vH : v≤H) (dC : d.natAbs≤C)
    (smallP : (1+C)*H^2<p) (smallQ : (1+C)*H^2<q)
    (nz : (u : ℤ)^2+d*v^2≠0) :
    ((u : ℤ)^2+d*v^2).natAbs.gcd (p*q)=1 := by
  have bound : ((u : ℤ)^2+d*v^2).natAbs≤(1+C)*H^2 := calc
    _ ≤ ((u : ℤ)^2).natAbs+(d*v^2).natAbs := Int.natAbs_add_le ..
    _ = u^2+d.natAbs*v^2 := by simp [Int.natAbs_mul, Int.natAbs_pow]
    _ ≤ H^2+C*H^2 := Nat.add_le_add (Nat.pow_le_pow_left uH 2)
      (Nat.mul_le_mul dC (Nat.pow_le_pow_left vH 2))
    _ = _ := by ring
  have pos : 0<((u : ℤ)^2+d*v^2).natAbs := Nat.pos_of_ne_zero (by simpa using nz)
  exact (Nat.coprime_of_lt_prime pos (bound.trans_lt smallP) hp).symm.mul_right
    (Nat.coprime_of_lt_prime pos (bound.trans_lt smallQ) hq).symm

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 10000 in
/-- Both box cutoffs below the smallest 1024-bit prime. -/
theorem fixed_coefficient_cutoffs :
    (1+733*739)*(2^501)^2 < (2^1023 : ℕ) ∧
    (1+2)*(2^510)^2 < (2^1023 : ℕ) := by decide +kernel

/-- All 8,647 positive catalog coefficients are at most 733·739. At
side 2^501 all their leaves are coprime to every target product. -/
theorem positive_catalog_exclusion {p q u v d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (pwidth : 2^1023≤p) (qwidth : 2^1023≤q) (pos : 0<u)
    (uH : u≤2^501) (vH : v≤2^501) (dC : d≤733*739) :
    ((u : ℤ)^2+(d : ℤ)*v^2).natAbs.gcd (p*q)=1 := by
  apply box_coprime hp hq uH vH (C:=733*739) (by simpa using dC)
    (fixed_coefficient_cutoffs.1.trans_le pwidth) (fixed_coefficient_cutoffs.1.trans_le qwidth)
  positivity

/-- For the three unconditional forms, side 2^510 excludes every target
factor. The irrationality of √2 handles the indefinite form. -/
theorem three_form_exclusion {p q u v : ℕ} {d : ℤ} (hp : p.Prime) (hq : q.Prime)
    (pwidth : 2^1023≤p) (qwidth : 2^1023≤q) (vp : 0<v)
    (uH : u≤2^510) (vH : v≤2^510) (choice : d=1 ∨ d=2 ∨ d= -2) :
    ((u : ℤ)^2+d*v^2).natAbs.gcd (p*q)=1 := by
  apply box_coprime hp hq uH vH (C:=2)
    (by rcases choice with rfl|rfl|rfl <;> decide)
    (fixed_coefficient_cutoffs.2.trans_le pwidth) (fixed_coefficient_cutoffs.2.trans_le qwidth)
  have vz : (0 : ℤ)<v := by exact_mod_cast vp
  rcases choice with rfl|rfl|rfl
  · exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (by decide) (sq_pos_of_pos vz))).ne'
  · exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (by decide) (sq_pos_of_pos vz))).ne'
  · intro bad
    apply unequal_squares vp
    exact_mod_cast (show (u : ℤ)^2=2*(v : ℤ)^2 by linarith)

/-- A Pell representation gives the same discriminant to the prospective
four-torsion form and its composition square. The final identity is the
unimodular substitution reducing the square to its public class. -/
theorem pell_lift (x y N h u v : ℤ) (norm : x^2+N=2*y^2) (odd : x=2*h-1) :
    (2*x)^2-4*y*(2*y)= -4*N ∧
    (2*x)^2-4*y^2*2= -4*N ∧
    2*(2*(u+h*v)^2-2*x*(u+h*v)*v+y^2*v^2)=
      4*u^2+4*u*v+(N+1)*v^2 := by
  refine ⟨by linear_combination 4*norm, by linear_combination 4*norm, ?_⟩
  rw [odd] at norm ⊢
  linear_combination -v^2*norm

/-- Two square roots of the same nonidentity involution differ by an
involution. This involution is new exactly when the two supplied roots
are distinct even up to inversion. -/
theorem fourth_roots {G : Type*} [CommGroup G] (A B T : G)
    (a : A^2=T) (b : B^2=T) :
    (A/B)^2=1 ∧ (A/B=1 ↔ A=B) ∧ (A/B=T ↔ B=A⁻¹) := by
  refine ⟨by simp [div_pow,a,b],div_eq_one, ?_⟩
  rw [← a]
  constructor
  · intro h
    have e : A*B⁻¹=A*A := by simpa only [div_eq_mul_inv,pow_two] using h
    exact inv_injective (by simpa only [inv_inv] using (mul_left_cancel e))
  · intro h
    simp [h,pow_two]

theorem pell_example :
    (5:ℤ)^2+697=2*19^2 ∧ (19:ℤ)^2+697=2*23^2 ∧
    Nat.gcd (19*19-5*23) 697=41 ∧ Nat.gcd (19*19+5*23) 697=17 ∧
    29-12=17 ∧ 29+12=41 := by decide

/-- A modular transform with coefficients (5, 26) already reveals 5.
A nonconstant invertible one with coefficients (0,14) reveals 13. -/
theorem examples :
    ((5 : ZMod 65)*26=0 ∧ (5 : ZMod 65)^2-26^2= -1 ∧ Nat.gcd 5 65=5) ∧
    ((14 : ZMod 65)^2=1 ∧ Nat.gcd (14-1) 65=13) := by decide

end PrimeFactors.NormOrbit
