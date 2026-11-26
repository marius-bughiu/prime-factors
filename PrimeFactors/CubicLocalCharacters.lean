import PrimeFactors.CubicTraceSquare
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Fintype.Units
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-! Quadratic characters on the reductions of cubic number-field-sieve
relations. At a good odd prime the separable residual algebra is a product
of finite fields. Degree-one characters and the obstruction between local
and global squares are classical; see Buhler, Lenstra and Pomerance,
*Factoring integers with the number field sieve*, §§6,8. -/
namespace PrimeFactors.CubicLocalCharacters

section FieldNorm
variable {F E : Type*} [Field F] [Field E] [Finite F] [Finite E] [Algebra F E]

private theorem nonsquare_mul {K : Type*} [Field K] [Finite K]
    {x y : K} (hx : ¬IsSquare x) (hy : ¬IsSquare y) : IsSquare (x*y) := by
  classical
  letI := Fintype.ofFinite K
  have nx : x≠0 := fun h => hx (h ▸ IsSquare.zero)
  have ny : y≠0 := fun h => hy (h ▸ IsSquare.zero)
  apply (quadraticChar_one_iff_isSquare (mul_ne_zero nx ny)).mp
  rw [map_mul, quadraticChar_neg_one_iff_not_isSquare.mpr hx,
    quadraticChar_neg_one_iff_not_isSquare.mpr hy]
  norm_num

/-- A norm from an odd finite field extension detects squares exactly, including zero.
Surjectivity supplies a lift of a nonsquare. The product of two nonsquares is square. -/
theorem norm_square_iff (hF : ringChar F≠2) (x : E) :
    IsSquare (Algebra.norm F x) ↔ IsSquare x := by
  classical
  constructor
  · intro h
    by_contra bad
    have nx : x≠0 := fun e => bad (e ▸ IsSquare.zero)
    obtain ⟨a,ha⟩ := FiniteField.exists_nonsquare hF
    obtain ⟨z,hz⟩ := FiniteField.norm_surjective F E a
    have nz : ¬IsSquare z := fun s => ha (hz ▸ (s.map (Algebra.norm F)))
    have s := (nonsquare_mul nz bad).map (Algebra.norm F)
    rw [map_mul,hz] at s
    have nN : Algebra.norm F x≠0 := Algebra.norm_ne_zero_iff.mpr nx
    exact ha (by simpa only [mul_div_cancel_right₀ _ nN] using s.div h)
  · exact IsSquare.map (Algebra.norm F)

end FieldNorm

section NormProducts
variable (F : Type*) [Field F]

/-- The actual algebra norm of a product is the product of the algebra norms.
Multiplication is block diagonal on the underlying vector space. -/
theorem norm_pair {A B : Type*} [Ring A] [Ring B] [Algebra F A] [Algebra F B]
    [FiniteDimensional F A] [FiniteDimensional F B] (a : A) (b : B) :
    Algebra.norm F (a,b)=Algebra.norm F a * Algebra.norm F b := by
  simp only [Algebra.norm_apply]
  convert LinearMap.det_prodMap (Algebra.lmul F A a) (Algebra.lmul F B b) using 2

private theorem self_norm (a : F) : Algebra.norm F a = a := by
  simp [Algebra.norm_apply,Algebra.smul_def]

end NormProducts

private theorem pair_isSquare {A B : Type*} [Mul A] [Mul B] (a : A) (b : B) :
    IsSquare (a,b) ↔ IsSquare a ∧ IsSquare b := by
  constructor
  · rintro ⟨⟨c,d⟩,eq⟩
    exact ⟨⟨c,congrArg Prod.fst eq⟩,⟨d,congrArg Prod.snd eq⟩⟩
  · rintro ⟨⟨c,rfl⟩,⟨d,rfl⟩⟩
    exact ⟨(c,d),rfl⟩

private theorem cancel_square {F : Type*} [Field F] {u v : F}
    (hn : u*v≠0) (whole : IsSquare (u*v)) (first : IsSquare u) : IsSquare v := by
  simpa only [mul_div_cancel_left₀ _ (left_ne_zero_of_mul hn)] using whole.div first

section Cubic
variable {F E : Type*} [Field F] [Finite F] [Field E] [Finite E] [Algebra F E]

/-- The one linear component of a 1+2 splitting is the only required
character after imposing nonzero square norm. -/
theorem linear_quadratic (hF : ringChar F≠2) (a : F) (b : E)
    (hn : Algebra.norm F (a,b)≠0) (whole : IsSquare (Algebra.norm F (a,b))) :
    IsSquare (a,b) ↔ IsSquare a := by
  rw [norm_pair,self_norm] at hn whole
  rw [pair_isSquare]
  exact ⟨And.left, fun ha => ⟨ha,(norm_square_iff hF b).mp (cancel_square hn whole ha)⟩⟩

omit [Finite F] in
/-- For three linear factors any selected pair suffices, by ordering the
tested coordinates first in the product decomposition. -/
theorem three_linear (a b c : F) (hn : Algebra.norm F ((a,b),c)≠0)
    (whole : IsSquare (Algebra.norm F ((a,b),c))) :
    IsSquare ((a,b),c) ↔ IsSquare a ∧ IsSquare b := by
  rw [norm_pair,norm_pair,self_norm,self_norm,self_norm] at hn whole
  rw [pair_isSquare,pair_isSquare]
  exact ⟨And.left, fun h => ⟨h,cancel_square hn whole (h.1.mul h.2)⟩⟩

omit [Finite F] in
/-- Statements in product coordinates apply to the given residual algebra
through its CRT algebra isomorphism; in particular they retain its actual norm. -/
theorem transport {A B : Type*} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) (x : A) :
    Algebra.norm F (e x)=Algebra.norm F x ∧ (IsSquare (e x) ↔ IsSquare x) := by
  refine ⟨Algebra.norm_eq_of_algEquiv e x,?_,IsSquare.map e⟩
  intro h
  simpa using h.map e.symm

end Cubic

section Signs
variable {F E : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

/-- Character compatibility at all elements, with zero mapped to zero. -/
theorem norm_character (hF : ringChar F≠2) (x : E) :
    quadraticChar F (Algebra.norm F x)=quadraticChar E x := by
  by_cases h : x=0
  · subst x
    simp only [Algebra.norm_zero,quadraticChar_zero]
  · have nx : Algebra.norm F x≠0 := Algebra.norm_ne_zero_iff.mpr h
    simp only [quadraticChar_apply,quadraticCharFun,if_neg h,if_neg nx,norm_square_iff hF]

/-- Both unit signs occur at every odd finite field. -/
theorem sign_surjective (hF : ringChar F≠2) :
    Function.Surjective (quadraticChar F).toUnitHom := by
  intro s
  rcases Int.units_eq_one_or s with rfl|rfl
  · exact ⟨1,map_one _⟩
  · obtain ⟨u,h⟩ := quadraticChar_exists_neg_one' hF
    exact ⟨u,Units.ext h⟩

end Signs

/-- Choose any signs on the last r coordinates, then fill the unique first
sign that leaves their product one. -/
noncomputable def patternEquiv (r : ℕ) :
    (Fin r → ℤˣ) ≃ {s : Fin (r+1) → ℤˣ // ∏ i, s i = 1} where
  toFun s := ⟨Fin.cons (∏ i,s i)⁻¹ s, by simp [Fin.prod_univ_succ]⟩
  invFun s i := s.1 i.succ
  left_inv s := by funext i; simp
  right_inv s := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (∏ j : Fin r, s.val j.succ)⁻¹ = s.val 0
      exact (eq_inv_of_mul_eq_one_left ((Fin.prod_univ_succ s.val).symm.trans s.property)).symm
    · simp

/-- A nonempty product of r+1 fields has exactly 2^r admissible patterns. -/
theorem sign_patterns_card (r : ℕ) :
    Fintype.card {s : Fin (r+1) → ℤˣ // ∏ i, s i = 1}=2^r := by
  rw [←Fintype.card_congr (patternEquiv r),Fintype.card_fun,Fintype.card_units_int,Fintype.card_fin]

/-- All admissible patterns are actually attained on units with square norm.
The product of component norms is the norm in CRT coordinates. -/
theorem realize_pattern {ι : Type*} [Fintype ι] (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (E : ι → Type*) [∀ i, Field (E i)] [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    [∀ i, Algebra F (E i)] (hF : ringChar F≠2) (s : ι → ℤˣ) :
    (∏ i,s i)=1 ↔ ∃ x : (i : ι) → (E i)ˣ,
      (∀ i, (quadraticChar (E i)).toUnitHom (x i)=s i) ∧
      IsSquare (∏ i,Algebra.norm F (x i : E i)) := by
  classical
  have tie (x : (i : ι) → (E i)ˣ) (eq : ∀ i, (quadraticChar (E i)).toUnitHom (x i)=s i) :
      IsSquare (∏ i,Algebra.norm F (x i : E i)) ↔ (∏ i,s i)=1 := by
    have nz : (∏ i,Algebra.norm F (x i : E i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => Algebra.norm_ne_zero_iff.mpr (x i).ne_zero
    rw [←quadraticChar_one_iff_isSquare nz,map_prod]
    have each (i) : quadraticChar F (Algebra.norm F (x i : E i))=(s i : ℤ) := by
      rw [norm_character hF]
      exact congrArg Units.val (eq i)
    simp_rw [each]
    change (∏ i, (Units.coeHom ℤ) (s i))=1 ↔ _
    rw [←map_prod]
    exact ⟨fun h => Units.ext h, fun h => congrArg Units.val h⟩
  constructor
  · intro good
    choose x hx using fun i => sign_surjective
      (F:=E i) (by rwa [←Algebra.ringChar_eq F (E i)]) (s i)
    exact ⟨x,hx,(tie x hx).mpr good⟩
  · rintro ⟨x,hx,hs⟩
    exact (tie x hx).mp hs

section MissedPrime
open CubicTraceSquare Polynomial

/-- For any coefficient ring, beta(t) has coordinates (H,Ht,0) in the
cubic power basis, where H is the norm of 1+tα and α³=11. -/
def value {R : Type*} [CommRing R] (t a : R) : R := (1+11*t^3)*(1+t*a)

theorem value_zero_parameter {R : Type*} [CommRing R] (a : R) : value 0 a=1 := by
  simp [value]

theorem missed_five (t : ZMod 5) (ht : t=2) :
    value t 1=2 ∧ ¬IsSquare (value t 1) := by
  subst t
  constructor
  · decide
  · rintro ⟨r,hr⟩
    exact (by decide : ∀ y : ZMod 5, value 2 1≠y*y) r hr

private theorem integral_trace (H : ℤ) (u : ℚ)
    (root : quartic (3*(H:ℚ)) (3*(H:ℚ)^2) ((H:ℚ)^2) u = 0) :
    ∃ m : ℤ, (m^2-3*H)^2-8*H^2*m-4*(3*H^2)=0 := by
  let P : ℤ[X] := (X^2-C (3*H))^2 - C (8*H^2)*X - C (12*H^2)
  have monic : P.Monic := by dsimp [P]; monicity!
  have ann : aeval u P=0 := by
    simp only [P,map_sub,map_pow,map_mul,aeval_X,aeval_C]
    simp only [eq_intCast,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
    unfold quartic at root
    linear_combination root
  obtain ⟨m,hm,_⟩ := exists_integer_of_is_root_of_monic monic ann
  change u=(m:ℚ) at hm
  subst u
  refine ⟨m,?_⟩
  unfold quartic at root
  exact_mod_cast root

private theorem masked_from_trace (t : ℕ) (t0 : t≠0)
    (reject : let H : ℤ := 1+11*t^3
              ∀ m : ℤ, (m^2-3*H)^2-8*H^2*m-4*(3*H^2)≠0) :
    let H : ℚ := 1+11*t^3
    Algebra.norm ℚ (elem H (H*t) 0)=H^4 ∧ ¬IsSquare (elem H (H*t) 0) := by
  let H : ℚ := 1+11*t^3
  have norm : pureNorm 11 H (H*t) 0=H^2^2 := by
    dsimp [pureNorm,H]
    ring
  change Algebra.norm ℚ (elem H (H*t) 0)=H^4 ∧ _
  constructor
  · rw [norm_elem,norm]
    ring
  · have nt : H*(t:ℚ)≠0 := mul_ne_zero (by dsimp [H]; positivity) (by exact_mod_cast t0)
    rw [square_iff_trace (w:=H^2) (Or.inl nt) (by simpa only [←pow_mul] using norm)]
    rintro ⟨u,hu⟩
    simp only [mul_zero,sub_zero] at hu
    obtain ⟨m,hm⟩ := integral_trace (1+11*(t:ℤ)^3) u (by simpa [H] using hu)
    exact reject m hm

/-- In the actual irreducible cubic field Q(∛11), t=2 mod 5 gives
square norm and excludes rational-coefficient square roots. -/
theorem masked_nonsquare (t : ℕ) (ht : (t:ZMod 5)=2) :
    let H : ℚ := 1+11*t^3
    Algebra.norm ℚ (elem H (H*t) 0)=H^4 ∧ ¬IsSquare (elem H (H*t) 0) := by
  apply masked_from_trace t (by rintro rfl; exact (by decide : (0:ZMod 5)≠2) ht)
  dsimp only
  intro m hm
  have eq5 := congrArg (fun z : ℤ => (z:ZMod 5)) hm
  push_cast at eq5
  rw [ht] at eq5
  exact (by decide : ∀ y : ZMod 5, (y^2-3*(1+11*2^3))^2-
    8*(1+11*2^3)^2*y-4*(3*(1+11*2^3)^2)≠0) m eq5

/-- If the given finite menu omits 5, choose t=2 M⁴, where M is the product
of its primes. Every tested evaluation is 1, including extension-field
coordinates. The omitted prime still witnesses a genuine global nonsquare. -/
theorem finite_menu_miss (M : ℕ) (omit5 : (M : ZMod 5)≠0) :
    ∃ t : ℕ, M∣t ∧ (t:ZMod 5)=2 ∧
      (∀ ℓ : ℕ, ℓ∣M → ∀ a : ZMod ℓ, value (t:ZMod ℓ) a=1) ∧
      (let H : ℚ := 1+11*t^3
       Algebra.norm ℚ (elem H (H*t) 0)=H^4 ∧ ¬IsSquare (elem H (H*t) 0)) := by
  let t := 2*M^4
  have dvd : M∣t := ⟨2*M^3,by dsimp [t]; ring⟩
  have ht : (t:ZMod 5)=2 := by
    have four := (by decide : ∀ m : ZMod 5, m≠0 → m^4=1) M omit5
    dsimp [t]
    push_cast
    rw [four,mul_one]
  refine ⟨t,dvd,ht,?_,masked_nonsquare t ht⟩
  intro ℓ hℓ a
  obtain ⟨c,hc⟩ := hℓ.trans dvd
  simp [hc,value]

/-- A parameter divisible by ℓ gives the unit 1 throughout the full residual
algebra, including components that have no root in the prime field. -/
theorem passes_full_reduction {t ℓ : ℕ} (h : ℓ∣t) {R : Type*} [CommRing R] [CharP R ℓ]
    (a : R) : value (t:R) a=1 := by
  rw [(CharP.cast_eq_zero_iff R ℓ t).mpr h,value_zero_parameter]

private theorem no_auxiliary_trace {R : Type*} [Field R] (six : (6:R)≠0)
    (ns : ¬IsSquare (3:R)) (u : R) : (u^2-3*9)^2-8*9^2*u-4*(3*9^2)≠0 := by
  intro root
  have eq : (u^2+27)^2=3*(6*(u+3))^2 := by linear_combination root
  by_cases h : u+3=0
  · have e : u= -3 := by linear_combination h
    have z : (u^2+27)^2=0 := by simpa only [h,mul_zero,zero_pow (by decide : 2≠0)] using eq
    have z' := sq_eq_zero_iff.mp z
    rw [e] at z'
    have sixSq : (6:R)^2=0 := by linear_combination z'
    exact six (sq_eq_zero_iff.mp sixSq)
  · apply ns
    refine (isSquare_iff_exists_sq _).mpr ⟨(u^2+27)/(6*(u+3)),?_⟩
    rw [div_pow]
    exact (eq_div_iff (pow_ne_zero _ (mul_ne_zero six h))).mpr eq.symm

/-- Every finite menu misses a global nonsquare of square norm in Q(∛11).
Take M to be the product of its primes. The held-out ℓ has splitting type
1+2, and β at its linear root is the nonsquare 27. -/
theorem any_finite_menu_miss (M : ℕ) (mp : 0<M) :
    ∃ t : ℕ, M∣t ∧
      (let H : ℚ := 1+11*t^3
       Algebra.norm ℚ (elem H (H*t) 0)=H^4 ∧ ¬IsSquare (elem H (H*t) 0)) := by
  have five : IsUnit (5 : ZMod 12) := (ZMod.isUnit_iff_coprime 5 12).mpr (by decide)
  obtain ⟨ℓ,large,lp,h12⟩ := Nat.forall_exists_prime_gt_and_eq_mod five (M+36)
  letI : Fact ℓ.Prime := ⟨lp⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have residue := congrArg ZMod.val h12
  change (ℓ:ZMod 12).val=(5:ZMod 12).val at residue
  rw [ZMod.val_natCast] at residue
  change ℓ%12=5 at residue
  have small (n : ℕ) (pos : 0<n) (cap : n<ℓ) : (n:ZMod ℓ)≠0 :=
    fun e => Nat.not_dvd_of_pos_of_lt pos cap ((ZMod.natCast_zmod_eq_zero_iff_dvd n ℓ).mp e)
  have six : (6:ZMod ℓ)≠0 := small 6 (by decide) (by omega)
  have ns : ¬IsSquare (3:ZMod ℓ) := by
    have rr := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p:=ℓ) (q:=3) (by omega) (by decide)
    have h3 : (ℓ:ZMod 3)=2 := (ZMod.natCast_eq_natCast_iff ℓ 2 3).mpr (by change ℓ%3=2; omega)
    have reject : ¬IsSquare (2:ZMod 3) := by rintro ⟨z,h⟩; exact (by decide : ∀ a : ZMod 3, 2≠a*a) z h
    simpa only [h3] using fun h => reject (h3 ▸ rr.mp h)
  have cop : (Nat.card (ZMod ℓ)ˣ).Coprime 3 := by
    rw [Nat.card_units,Nat.card_eq_fintype_card,ZMod.card]
    exact (Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)).symm
  have h11 : (11:ZMod ℓ)≠0 := small 11 (by decide) (by omega)
  have h8 : (8:ZMod ℓ)≠0 := small 8 (by decide) (by omega)
  obtain ⟨v,cv⟩ := cop.pow_left_bijective.surjective
    (Units.mk0 (8/11 : ZMod ℓ) (div_ne_zero h8 h11))
  have cubic : (v:ZMod ℓ)^3=8/11 := congrArg Units.val cv
  have munit : M.Coprime ℓ := (lp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt mp (by omega))).symm
  obtain ⟨t,hm,hv⟩ := Nat.chineseRemainder munit 0 (v:ZMod ℓ).val
  have tv : (t:ZMod ℓ)=v := ((ZMod.natCast_eq_natCast_iff ..).mpr hv).trans (ZMod.natCast_zmod_val _)
  have t0 : t≠0 := by rintro rfl; exact v.ne_zero (by simpa using tv.symm)
  refine ⟨t,Nat.modEq_zero_iff_dvd.mp hm,masked_from_trace t t0 ?_⟩
  have nine : 1+11*(t:ZMod ℓ)^3=9 := by
    rw [tv,cubic]
    field_simp
    ring
  dsimp only
  intro z hz
  have reduced := congrArg (fun a : ℤ => (a:ZMod ℓ)) hz
  push_cast at reduced
  rw [nine] at reduced
  exact no_auxiliary_trace six ns z reduced

end MissedPrime

end PrimeFactors.CubicLocalCharacters
