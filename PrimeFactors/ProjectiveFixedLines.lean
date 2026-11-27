import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Fixed lines of a two-dimensional linear map

The projective line over a field has one affine chart and one point at infinity.
Over a product of two fields we use the product of the two projective lines,
including points finite at exactly one component. For the finite-field
classification see Meagher and Spiga, arXiv:0910.3193v2, p. 4.
-/

namespace PrimeFactors.ProjectiveFixedLines

/-- Entries of the matrix acting on column vectors. -/
structure Coeff (F : Type*) where
  a : F
  b : F
  c : F
  d : F
deriving DecidableEq

variable {F : Type*}
def det [CommRing F] (M : Coeff F) := M.a*M.d-M.b*M.c
def delta [CommRing F] (M : Coeff F) := (M.a-M.d)^2+4*M.b*M.c
def scalar [Zero F] (M : Coeff F) := M.b=0 ∧ M.c=0 ∧ M.a=M.d

theorem trace_formula [CommRing F] (M : Coeff F) : delta M = (M.a+M.d)^2 - 4*det M := by
  unfold delta det; ring

variable [Field F] [DecidableEq F]

/-- Homogeneous coordinates [z:1] and [1:0]. -/
def act (M : Coeff F) : Option F → Option F
  | none => if M.c=0 then none else some (M.a/M.c)
  | some z => if M.c*z+M.d=0 then none else some ((M.a*z+M.b)/(M.c*z+M.d))

theorem finite_fixed_iff (M : Coeff F) (unit : det M ≠ 0) (z : F) :
    act M (some z)=some z ↔ M.c*(z*z)+(M.d-M.a)*z+(-M.b)=0 := by
  by_cases pole : M.c*z+M.d=0
  · simp [act,pole]
    intro zero
    apply unit
    unfold det
    linear_combination (M.a-M.c*z)*pole+M.c*zero
  · simp only [act,if_neg pole, Option.some.injEq, div_eq_iff pole]
    constructor <;> intro h <;> linear_combination -h

variable [Fintype F]

noncomputable def fixed (M : Coeff F) : Finset (Option F) :=
  Finset.univ.filter fun x => act M x=x

theorem finite_mem (M : Coeff F) (unit : det M≠0) (z : F) :
    some z∈fixed M ↔ M.c*(z*z)+(M.d-M.a)*z+(-M.b)=0 := by
  simp [fixed,finite_fixed_iff M unit z]

theorem infinity_mem (M : Coeff F) : none∈fixed M ↔ M.c=0 := by
  by_cases eq : M.c=0 <;> simp [fixed,act,eq]

noncomputable def squareCount (D : F) : ℕ := by
  classical exact if D=0 then 1 else if IsSquare D then 2 else 0

theorem scalar_count (M : Coeff F) (unit : det M≠0) (s : scalar M) :
    (fixed M).card=Fintype.card F + 1 := by
  obtain ⟨hb,hc,ha⟩ := s
  have equal : fixed M=Finset.univ := by
    ext t
    cases t with
    | none => simp [infinity_mem,hc]
    | some z => simp [finite_mem M unit,hb,hc,ha]
  simp [equal]

variable [NeZero (2:F)]

omit [NeZero (2:F)] in
private theorem nonscalar_triangular (M : Coeff F) (unit : det M≠0) (no : ¬scalar M)
    (hc : M.c=0) : (fixed M).card=squareCount (delta M) := by
  classical
  by_cases ad : M.a=M.d
  · have hb : M.b≠0 := fun hb => no ⟨hb,hc,ad⟩
    have ff : fixed M={none} := by
      ext t
      cases t with
      | none => simp [infinity_mem,hc]
      | some z => simp [finite_mem M unit,hc,ad,hb]
    simp [ff, squareCount,delta,hc,ad]
  · have nz : M.d-M.a≠0 := sub_ne_zero.mpr (Ne.symm ad)
    have df : delta M=(M.a-M.d)^2 := by simp [delta,hc]
    have root : IsSquare (delta M) := ⟨M.a-M.d,by rw [df,pow_two]⟩
    have dn : delta M≠0 := by rw [df]; exact pow_ne_zero _ (sub_ne_zero.mpr ad)
    have ff : fixed M={none,some (M.b/(M.d-M.a))} := by
      ext t
      cases t with
      | none => simp [infinity_mem,hc]
      | some z =>
        simp [finite_mem M unit,hc]
        rw [eq_div_iff nz]; constructor <;> intro h <;> linear_combination h
    simp [ff,squareCount,dn,root]

private theorem nonscalar_other (M : Coeff F) (unit : det M≠0) (hc : M.c≠0) :
    (fixed M).card=squareCount (delta M) := by
  classical
  have disc : discrim M.c (M.d-M.a) (-M.b)=delta M := by unfold discrim delta; ring
  by_cases dz : delta M=0
  · have ff : fixed M={some (-(M.d-M.a)/(2*M.c))} := by
      ext t
      cases t with
      | none => simp [infinity_mem,hc]
      | some z =>
        simp only [finite_mem M unit,Finset.mem_singleton,Option.some.injEq]
        exact quadratic_eq_zero_iff_of_discrim_eq_zero hc (disc.trans dz) _
    simp [ff,squareCount,dz]
  · by_cases ds : IsSquare (delta M)
    · obtain ⟨s,hs⟩ := ds
      have sn : s≠0 := by intro eq; simp [eq] at hs; contradiction
      let L := (-(M.d-M.a)+s)/(2*M.c)
      let R := (-(M.d-M.a)-s)/(2*M.c)
      have lr : L≠R := by
        intro same
        have eq := (div_left_inj' (mul_ne_zero (NeZero.ne (2:F)) hc)).mp same
        have prod : (2:F)*s=0 := by linear_combination eq
        exact (mul_ne_zero (NeZero.ne _) sn) prod
      have ff : fixed M={some L,some R} := by
        ext t
        cases t with
        | none => simp [infinity_mem,hc]
        | some z =>
          simp only [finite_mem M unit,Finset.mem_insert,Finset.mem_singleton,Option.some.injEq]
          exact quadratic_eq_zero_iff hc (disc.trans hs) _
      have ds' : IsSquare (delta M) := ⟨s,hs⟩
      simp [ff,squareCount,dz,ds',lr]
    · have ff : fixed M=∅ := by
        apply Finset.eq_empty_of_forall_not_mem
        intro t mem
        cases t with
        | none => exact hc ((infinity_mem M).mp mem)
        | some z =>
          have q := discrim_eq_sq_of_quadratic_eq_zero ((finite_mem M unit z).mp mem)
          exact ds ⟨_,by rw [←disc,q,pow_two]⟩
      simp [ff,squareCount,dz,ds]

/-- Exact field count for each invertible nonscalar matrix, in both affine charts. -/
theorem nonscalar_count (M : Coeff F) (unit : det M≠0) (no : ¬scalar M) :
    (fixed M).card=squareCount (delta M) := by
  by_cases h : M.c=0
  · exact nonscalar_triangular M unit no h
  · exact nonscalar_other M unit h

/-- Scalar matrices contribute the entire line. Other matrices contribute
one, two or zero according to the vanishing and square class of the discriminant. -/
noncomputable def localCount (M : Coeff F) : ℕ := by
  classical exact if scalar M then Fintype.card F + 1 else squareCount (delta M)

theorem field_count (M : Coeff F) (unit : det M ≠ 0) : (fixed M).card = localCount M := by
  classical
  by_cases s : scalar M
  · simpa [localCount, s] using scalar_count M unit s
  · simpa [localCount, s] using nonscalar_count M unit s

/-- The two CRT charts are independent, including mixed affine/infinite points. -/
noncomputable def both {E : Type*} [Field E] [Fintype E] [DecidableEq E]
    (M : Coeff F) (L : Coeff E) : Finset (Option F × Option E) :=
  Finset.univ.filter fun z => (act M z.1,act L z.2)=z

omit [NeZero (2:F)] in
theorem both_count {E : Type*} [Field E] [Fintype E] [DecidableEq E]
    (M : Coeff F) (L : Coeff E) : (both M L).card=(fixed M).card*(fixed L).card := by
  have h : both M L=(fixed M) ×ˢ (fixed L) := by
    ext ⟨t,s⟩
    simp [both,fixed]
  rw [h,Finset.card_product]

/-- Complete classification for independent local components of any invertible
matrix, including repeated discriminants and mixed scalar cases. -/
theorem crt_count {E : Type*} [Field E] [Fintype E] [DecidableEq E] [NeZero (2:E)]
    (M : Coeff F) (L : Coeff E) (um : det M ≠ 0) (ul : det L ≠ 0) :
    (both M L).card = localCount M * localCount L := by
  rw [both_count, field_count M um, field_count L ul]

/-- A matrix scalar at both primes fixes every projective point. -/
theorem scalar_total {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (M : Coeff (ZMod p)) (L : Coeff (ZMod q)) (um : det M≠0) (ul : det L≠0)
    (sm : scalar M) (sl : scalar L) :
    (both M L).card=p*q+p+q+1 := by
  rw [both_count,scalar_count M um sm,scalar_count L ul sl,ZMod.card,ZMod.card]
  ring

theorem square_crt {p q : ℕ} (cop : p.Coprime q) (x : ZMod (p*q)) :
    IsSquare x ↔ IsSquare ((ZMod.chineseRemainder cop x).1) ∧
      IsSquare ((ZMod.chineseRemainder cop x).2) := by
  let e := ZMod.chineseRemainder cop
  change IsSquare x ↔ IsSquare (e x).1 ∧ IsSquare (e x).2
  constructor
  · rintro ⟨s,rfl⟩
    rw [map_mul]
    exact ⟨⟨(e s).1,rfl⟩,⟨(e s).2,rfl⟩⟩
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    refine ⟨e.symm (a,b),e.injective ?_⟩
    rw [map_mul,e.apply_symm_apply]
    exact Prod.ext ha hb

/-- Generic trace given the unit discriminant and no local scalar. -/
theorem generic_trace {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [NeZero (2:ZMod p)] [NeZero (2:ZMod q)] (cop : p.Coprime q)
    (M : Coeff (ZMod p)) (L : Coeff (ZMod q)) (unitM : det M≠0) (unitL : det L≠0)
    (ordinaryM : ¬scalar M) (ordinaryL : ¬scalar L) (D : ZMod (p*q))
    (matchM : (ZMod.chineseRemainder cop D).1=delta M)
    (matchL : (ZMod.chineseRemainder cop D).2=delta L)
    (nzM : delta M≠0) (nzL : delta L≠0) :
    (both M L).card=(if IsSquare D then 4 else 0) := by
  classical
  have qr := square_crt cop D
  rw [matchM,matchL] at qr
  rw [both_count,nonscalar_count M unitM ordinaryM,nonscalar_count L unitL ordinaryL]
  by_cases s : IsSquare (delta M) <;> by_cases t : IsSquare (delta L) <;>
    simp [squareCount,qr,nzM,nzL,s,t]

def cayley (x : F) : Coeff F :=
  ⟨(1+x)/(1-x),2*x/(1-x),2/(1-x),(1+x)/(1-x)⟩

omit [DecidableEq F] [Fintype F] [NeZero (2:F)] in
theorem cayley_det {x : F} (away : x≠1) : det (cayley x)=1 := by
  unfold det cayley
  field_simp [sub_ne_zero.mpr away.symm]
  ring

theorem cayley_finite {x : F} (away : x≠1) (z : F) :
    some z∈fixed (cayley x) ↔ z^2=x := by
  rw [finite_mem _ (by rw [cayley_det away]; exact one_ne_zero)]
  change 2/(1-x)*(z*z)+((1+x)/(1-x)-(1+x)/(1-x))*z+ -(2*x/(1-x))=0 ↔ z^2=x
  simp only [sub_self,zero_mul,add_zero]
  have nz : 1-x≠0 := sub_ne_zero.mpr away.symm
  field_simp [nz]
  constructor <;> intro h
  · apply mul_left_cancel₀ (NeZero.ne (2:F))
    linear_combination h
  · linear_combination 2*h

theorem cayley_infinity {x : F} (away : x≠1) :
    none ∉fixed (cayley x) := by
  rw [infinity_mem]
  exact div_ne_zero (NeZero.ne _) (sub_ne_zero.mpr away.symm)

/-- When one of the two primes divides a public value z, but the other
does not, a gcd recovers a proper divisor without counting any lines. -/
theorem split_by_gcd {p q z : ℕ} (op : 1<p) (oq : 0<q)
    (yes : p∣z) (no : ¬q∣z) :
    1<(p*q).gcd z ∧ (p*q).gcd z<p*q := by
  let g := (p*q).gcd z
  have np : 0<p*q := Nat.mul_pos (by omega) oq
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ np
  have pg : p∣g := Nat.dvd_gcd (dvd_mul_right ..) yes
  have upper : g≤p*q := Nat.le_of_dvd np (Nat.gcd_dvd_left ..)
  have different : g≠p*q := by
    intro eq
    have dz : g∣z := Nat.gcd_dvd_right ..
    exact no ((dvd_mul_left q p).trans (eq ▸ dz))
  exact ⟨op.trans_le (Nat.le_of_dvd gp pg),lt_of_le_of_ne upper different⟩



/-- Reduce a single integer matrix at a positive characteristic. -/
noncomputable def reduce (n : ℕ) (M : Coeff ℤ) : Coeff (ZMod n) :=
  ⟨M.a, M.b, M.c, M.d⟩

theorem reduce_det (n : ℕ) (M : Coeff ℤ) : det (reduce n M) = ((det M : ℤ) : ZMod n) := by
  simp [det, reduce]

theorem reduce_delta (n : ℕ) (M : Coeff ℤ) :
    delta (reduce n M) = ((delta M : ℤ) : ZMod n) := by
  simp [delta, reduce]

/-- The common divisor of the three scalar conditions on integer entries. -/
def scalarDivisor (M : Coeff ℤ) : ℕ := M.b.natAbs.gcd (M.c.natAbs.gcd (M.a - M.d).natAbs)

private theorem abs_dvd_iff_zero (k : ℕ) (z : ℤ) :
    k ∣ z.natAbs ↔ (z : ZMod k) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← Int.natCast_dvd_natCast, Int.dvd_natAbs]

theorem scalar_iff_dvd (n : ℕ) (M : Coeff ℤ) :
    scalar (reduce n M) ↔ n ∣ scalarDivisor M := by
  rw [scalarDivisor, Nat.dvd_gcd_iff, Nat.dvd_gcd_iff]
  simp only [abs_dvd_iff_zero, Int.cast_sub, sub_eq_zero, scalar, reduce]

/-- A locally scalar matrix with nonscalar second component has a nontrivial
common divisor of its three public scalar conditions and the modulus. -/
theorem mixed_scalar_gcd {p q : ℕ} (hp : 1 < p) (hq : 0 < q) (M : Coeff ℤ)
    (sp : scalar (reduce p M)) (sq : ¬scalar (reduce q M)) :
    1 < (p*q).gcd (scalarDivisor M) ∧ (p*q).gcd (scalarDivisor M) < p*q :=
  split_by_gcd hp hq ((scalar_iff_dvd _ _).mp sp) (fun h => sq ((scalar_iff_dvd _ _).mpr h))

private theorem nonzero_reduction {p N : ℕ} [Fact p.Prime] {z : ℤ} (part : p ∣ N)
    (unit : N.Coprime z.natAbs) : (z : ZMod p) ≠ 0 :=
  fun zero => (Nat.Prime.not_dvd_one (Fact.out : p.Prime))
    (unit ▸ Nat.dvd_gcd part ((abs_dvd_iff_zero _ _).mpr zero))

omit [DecidableEq F] [Fintype F] [NeZero (2:F)] in
private theorem nonscalar_of_discriminant (M : Coeff F) (nz : delta M ≠ 0) : ¬scalar M := by
  rintro ⟨hb, hc, ad⟩
  simp [delta, hb, hc, ad] at nz

/-- With unit determinant and unit discriminant, the fixed count for a single
integer matrix equals four exactly when its discriminant is a square modulo
the product. The hypotheses also exclude both local scalar cases. -/
theorem integer_generic {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [NeZero (2 : ZMod p)] [NeZero (2 : ZMod q)] (cop : p.Coprime q) (M : Coeff ℤ)
    (unit : (p*q).Coprime (det M).natAbs) (regular : (p*q).Coprime (delta M).natAbs) :
    (both (reduce p M) (reduce q M)).card =
      if IsSquare ((delta M : ℤ) : ZMod (p*q)) then 4 else 0 := by
  have dp : delta (reduce p M) ≠ 0 := by
    rw [reduce_delta]
    exact nonzero_reduction (dvd_mul_right ..) regular
  have dq : delta (reduce q M) ≠ 0 := by
    rw [reduce_delta]
    exact nonzero_reduction (dvd_mul_left ..) regular
  apply generic_trace cop _ _ _ _ (nonscalar_of_discriminant _ dp) (nonscalar_of_discriminant _ dq)
     _ _ _ dp dq
  · rw [reduce_det]
    exact nonzero_reduction (dvd_mul_right ..) unit
  · rw [reduce_det]
    exact nonzero_reduction (dvd_mul_left ..) unit
  · rw [map_intCast, reduce_delta]
    rfl
  · rw [map_intCast, reduce_delta]
    rfl

/-- The invertible companion matrix of the equation z²=x when x is nonzero. -/
def companion (x : F) : Coeff F := ⟨0, x, 1, 0⟩

omit [DecidableEq F] [Fintype F] [NeZero (2:F)] in
theorem companion_det (x : F) : det (companion x) = -x := by simp [companion, det]

omit [NeZero (2:F)] in
theorem companion_finite {x : F} (unit : x ≠ 0) (z : F) :
    some z ∈ fixed (companion x) ↔ z^2 = x := by
  rw [finite_mem _ (by simpa [companion_det] using unit)]
  simp [companion, pow_two, ← sub_eq_add_neg, sub_eq_zero]

omit [NeZero (2:F)] in
theorem companion_infinity (x : F) : none ∉ fixed (companion x) := by
  simp [infinity_mem, companion]

omit [NeZero (2:F)] in
private theorem card_roots_of_chart (M : Coeff F) (x : F)
    (infinity : none ∉ fixed M) (finite : ∀ z : F, some z ∈ fixed M ↔ z^2 = x) :
    (fixed M).card = (Finset.univ.filter fun z : F => z^2 = x).card := by
  classical
  have same : fixed M = (Finset.univ.filter fun z : F => z^2 = x).image some := by
    ext y
    cases y with
    | none => simp [infinity]
    | some z => simp [finite]
  rw [same, Finset.card_image_of_injective _ (Option.some_injective F)]

/-- The determinant-one normalization counts square roots, including the
repeated-root case x=0. In odd characteristic division by 1−x requires x≠1. -/
theorem cayley_count {x : F} (away : x ≠ 1) :
    (fixed (cayley x)).card = (Finset.univ.filter fun z : F => z^2 = x).card :=
  card_roots_of_chart _ x (cayley_infinity away) (cayley_finite away)

omit [NeZero (2:F)] in
/-- The companion matrix requires only x≠0 and also handles x=1. -/
theorem companion_count {x : F} (unit : x ≠ 0) :
    (fixed (companion x)).card = (Finset.univ.filter fun z : F => z^2 = x).card :=
  card_roots_of_chart _ x (companion_infinity x) (companion_finite unit)

/-- The scalar case is characterized by the full cardinality of the fixed set. -/
theorem scalar_iff_full (M : Coeff F) (unit : det M ≠ 0) :
    scalar M ↔ (fixed M).card = Fintype.card F + 1 := by
  classical
  refine ⟨scalar_count M unit, ?_⟩
  intro allLines
  by_contra small
  rw [nonscalar_count M unit small] at allLines
  have lower := Fintype.one_lt_card (α := F)
  unfold squareCount at allLines
  split at allLines <;> first | omega | (split at allLines <;> omega)

/-- Every composite square root corresponds to one ordered pair of local roots. -/
theorem root_count_crt {p q : ℕ} [NeZero p] [NeZero q] (cop : p.Coprime q)
    (x : ZMod (p*q)) :
    (Finset.univ.filter fun z : ZMod (p*q) => z^2 = x).card =
      (Finset.univ.filter fun a : ZMod p => a^2 = (ZMod.chineseRemainder cop x).1).card *
      (Finset.univ.filter fun b : ZMod q => b^2 = (ZMod.chineseRemainder cop x).2).card := by
  let e := ZMod.chineseRemainder cop
  rw [← Finset.card_product]
  apply Finset.card_equiv e.toEquiv
  intro t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  calc
    (t^2 = x) ↔ e (t^2) = e x := e.injective.eq_iff.symm
    _ ↔ _ := by rw [map_pow, Prod.ext_iff]; rfl

/-- Counting the fixed projective lines of the determinant-one pair counts
exactly the square roots of the supplied residue at the composite modulus. -/
theorem cayley_count_crt {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [NeZero (2 : ZMod p)] [NeZero (2 : ZMod q)] (cop : p.Coprime q) (x : ZMod (p*q))
    (hp : (ZMod.chineseRemainder cop x).1 ≠ 1)
    (hq : (ZMod.chineseRemainder cop x).2 ≠ 1) :
    (both (cayley (ZMod.chineseRemainder cop x).1) (cayley (ZMod.chineseRemainder cop x).2)).card =
      (Finset.univ.filter fun z : ZMod (p*q) => z^2 = x).card := by
  rw [both_count, cayley_count hp, cayley_count hq, root_count_crt cop]

/-- The companion pair provides the same equality under the unit condition on x. -/
theorem companion_count_crt {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (x : ZMod (p*q)) (hp : (ZMod.chineseRemainder cop x).1 ≠ 0)
    (hq : (ZMod.chineseRemainder cop x).2 ≠ 0) :
    (both (companion (ZMod.chineseRemainder cop x).1)
      (companion (ZMod.chineseRemainder cop x).2)).card =
      (Finset.univ.filter fun z : ZMod (p*q) => z^2 = x).card := by
  rw [both_count, companion_count hp, companion_count hq, root_count_crt cop]

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : NeZero (2 : ZMod 7) := ⟨by decide⟩
local instance : NeZero (2 : ZMod 11) := ⟨by decide⟩

/-- Two determinant-one matrices at level 77 have unit discriminants of the
same positive Jacobi symbol but different numbers of fixed projective lines. -/
theorem jacobi_counterexample :
    let M : Coeff ℤ := ⟨24, 23, 25, 24⟩
    let L : Coeff ℤ := ⟨14, 13, 15, 14⟩
    det M = 1 ∧ det L = 1 ∧ jacobiSym (delta M) 77 = 1 ∧ jacobiSym (delta L) 77 = 1 ∧
      (both (reduce 7 M) (reduce 11 M)).card = 4 ∧
      (both (reduce 7 L) (reduce 11 L)).card = 0 := by
  dsimp only
  refine ⟨by decide, by decide, by norm_num [delta], by norm_num [delta], ?_, ?_⟩
  · rw [integer_generic (by decide : Nat.Coprime 7 11) (⟨24, 23, 25, 24⟩ : Coeff ℤ) (by decide) (by decide)]
    decide +kernel
  · rw [integer_generic (by decide : Nat.Coprime 7 11) (⟨14, 13, 15, 14⟩ : Coeff ℤ) (by decide) (by decide)]
    decide +kernel

end PrimeFactors.ProjectiveFixedLines
