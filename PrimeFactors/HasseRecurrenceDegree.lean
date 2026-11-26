import PrimeFactors.TranslatedHasse
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

/-! A degree bound for constant-coefficient recurrences of diagonal moments. -/
noncomputable section
namespace PrimeFactors.HasseRecurrenceDegree

open Polynomial
open scoped Polynomial

variable {K : Type*} [Field K]

/-- Clear the denominator of a polynomial in the substitution X/F(X). -/
def clearTerms {R : Type*} [CommRing R] (F : R[X]) (s : ℕ) (a : ℕ → R) : R[X] :=
  ∑ j ∈ Finset.range (s+1), C (a j)*X^j*F^(s-j)

/-- Jacobian denominator for the diagonal generating series. -/
def jac {R : Type*} [CommRing R] (F : R[X]) := F-X*F.derivative

private theorem term_degree (F : K[X]) (s j : ℕ) (a : ℕ → K) :
    (C (a j)*X^j*F^(s-j)).natDegree ≤ j+(s-j)*F.natDegree := by
  compute_degree

private theorem index_drop {s j d : ℕ} (jd : j≤s) (jp : 0<j) (large : 2≤d) :
    j+(s-j)*d < s*d := by
  have eqn : (s-j)*d+j*d = s*d := by rw [← Nat.add_mul, Nat.sub_add_cancel jd]
  have bigger := Nat.mul_le_mul_left j large
  omega

private theorem clear_degree (F : K[X]) (s : ℕ) (a : ℕ → K) (large : 2≤F.natDegree) :
    (clearTerms F s a).natDegree ≤ s*F.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have jd := Finset.mem_range.mp hj
  by_cases z : j=0
  · subst j
    simpa using term_degree F s 0 a
  · exact (term_degree ..).trans (index_drop (by omega) (by omega) large).le

private theorem clear_top (F : K[X]) (s : ℕ) (a : ℕ → K) (large : 2≤F.natDegree) :
    (clearTerms F s a).coeff (s*F.natDegree) = a 0*F.leadingCoeff^s := by
  rw [clearTerms, finset_sum_coeff, Finset.sum_eq_single 0]
  · simp only [pow_zero, mul_one, Nat.sub_zero, coeff_C_mul]
    rw [← natDegree_pow, coeff_natDegree, leadingCoeff_pow]
  · intro j hj h0
    exact coeff_eq_zero_of_natDegree_lt ((term_degree ..).trans_lt
      (index_drop (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) (by omega) large))
  · simp

private theorem jac_degree (F : K[X]) (large : 2≤F.natDegree) :
    (jac F).natDegree ≤ F.natDegree := by
  refine (natDegree_sub_le ..).trans (max_le le_rfl ?_)
  have der := natDegree_derivative_le F
  have bound := natDegree_mul_le (p := (X : K[X])) (q := F.derivative)
  rw [natDegree_X] at bound
  omega

private theorem jac_top (F : K[X]) (large : 2≤F.natDegree) :
    (jac F).coeff F.natDegree = (1-(F.natDegree:K))*F.leadingCoeff := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (show F.natDegree≠0 by omega)
  rw [jac, coeff_sub, coeff_natDegree, hk, coeff_X_mul, coeff_derivative]
  rw [show k+1=F.natDegree by omega, coeff_natDegree, Nat.cast_succ]
  ring

/-- If P and Q both start with 1, the error from clearing QG−P has a
nonzero leading coefficient whenever the degree of F is a unit. -/
theorem obstruction_top (F : K[X]) (s : ℕ) (a b : ℕ → K)
    (large : 2≤F.natDegree) (a0 : a 0=1) (b0 : b 0=1) :
    (F*clearTerms F s b - jac F*clearTerms F s a).coeff ((s+1)*F.natDegree) =
      (F.natDegree:K)*F.leadingCoeff^(s+1) := by
  rw [coeff_sub, Nat.succ_mul, add_comm,
    coeff_mul_of_natDegree_le le_rfl (clear_degree F s b large),
    coeff_mul_of_natDegree_le (jac_degree F large) (clear_degree F s a large),
    coeff_natDegree, clear_top F s a large, clear_top F s b large, jac_top F large, a0, b0, pow_succ]
  ring

/-- A necessary order bound for a denominator-cleared Padé match. -/
theorem cleared_bound (F : K[X]) (s m : ℕ) (a b : ℕ → K)
    (large : 2≤F.natDegree) (char : (F.natDegree:K)≠0) (a0 : a 0=1) (b0 : b 0=1)
    (matchPrefix : X^(m+1) ∣ F*clearTerms F s b - jac F*clearTerms F s a) :
    m < (s+1)*F.natDegree := by
  by_contra! sm
  have vanish := X_pow_dvd_iff.mp matchPrefix _ (show (s+1)*F.natDegree<m+1 by omega)
  rw [obstruction_top F s a b large a0 b0] at vanish
  have nz : F ≠ 0 := by intro z; simp [z] at large
  exact (mul_ne_zero char (pow_ne_zero _ (leadingCoeff_ne_zero.mpr nz))) vanish


/-- Central diagonal moments of a polynomial with an arbitrary coefficient ring. -/
def moment {R : Type*} [CommRing R] (F : R[X]) (n : ℕ) := (F^n).coeff n

private theorem clear_succ {R : Type*} [CommRing R] (F : R[X]) (m : ℕ) (a : ℕ → R) :
    clearTerms F (m+1) a = F*clearTerms F m a + C (a (m+1))*X^(m+1) := by
  rw [clearTerms, Finset.sum_range_succ, clearTerms, Finset.mul_sum]
  simp only [Nat.sub_self, pow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have jle := Finset.mem_range.mp hj
  rw [show m+1-j=(m-j)+1 by omega, pow_succ]
  ring

private theorem jac_moment_cancel (F : ℤ[X]) (m : ℕ) :
    (jac F * F^m).coeff (m+1) = 0 := by
  have dh := congrArg (fun p : ℤ[X] => p.coeff m) (derivative_pow F (m+1))
  simp only [coeff_derivative, Nat.add_sub_cancel, coeff_C_mul, Nat.cast_succ] at dh
  have cast : (m:ℤ)+1≠0 := by positivity
  have eqn : (F^(m+1)).coeff (m+1) = (F.derivative*F^m).coeff m := by
    apply mul_right_cancel₀ cast
    convert dh using 1
    simp only [mul_assoc, coeff_C_mul, Nat.cast_succ]
    ring_nf
  rw [jac, sub_mul, ← pow_succ', mul_assoc, coeff_sub, coeff_X_mul, eqn, sub_self]

private theorem error_next_coeff (F : ℤ[X]) (m : ℕ) :
    (F^(m+1)-jac F*clearTerms F m (moment F)).coeff (m+1) = moment F (m+1) := by
  rw [coeff_sub, clearTerms, Finset.mul_sum, finset_sum_coeff, Finset.sum_eq_zero]
  · simp [moment]
  intro j hj
  have jle := Finset.mem_range.mp hj
  rw [show jac F*(C (moment F j)*X^j*F^(m-j)) =
    C (moment F j)*(jac F*F^(m-j))*X^j by ring,
    show m+1=(m-j+1)+j by omega, coeff_mul_X_pow, coeff_C_mul, jac_moment_cancel, mul_zero]

/-- Finite Jacobian form of Lagrange inversion with no division of coefficients. -/
theorem integral_lagrange (F : ℤ[X]) (m : ℕ) :
    X^(m+1) ∣ F^(m+1)-jac F*clearTerms F m (moment F) := by
  induction m with
  | zero =>
    simp [clearTerms, jac, moment]
  | succ m ih =>
    obtain ⟨H,hH⟩ := ih
    have hz := error_next_coeff F m
    rw [hH, coeff_X_pow_mul' H (m+1) (m+1)] at hz
    simp only [le_refl, if_true, Nat.sub_self] at hz
    have div : X ∣ F*H-jac F*C (moment F (m+1)) := by
      rw [X_dvd_iff, coeff_sub, mul_coeff_zero, mul_coeff_zero, jac, coeff_sub, mul_coeff_zero]
      simp [hz]
    obtain ⟨A,ha⟩ := div
    refine ⟨A,?_⟩
    calc
      _ = F*(F^(m+1)-jac F*clearTerms F m (moment F))-
          jac F*C (moment F (m+1))*X^(m+1) := by rw [clear_succ, pow_succ' F (m+1)]; ring
      _ = X^(m+1)*(F*H-jac F*C (moment F (m+1))) := by rw [hH]; ring
      _ = _ := by rw [ha, pow_succ X (m+1)]; ring


private theorem mapped_lagrange (G : ℤ[X]) (φ : ℤ →+* K) (m : ℕ) :
    let F := G.map φ
    X^(m+1) ∣ F^(m+1)-jac F*clearTerms F m (moment F) := by
  dsimp only
  have h := (Polynomial.mapRingHom φ).map_dvd (integral_lagrange G m)
  have mc : (clearTerms G m (moment G)).map φ = clearTerms (G.map φ) m (moment (G.map φ)) := by
    change (Polynomial.mapRingHom φ) _ = _
    rw [clearTerms, map_sum, clearTerms]
    apply Finset.sum_congr rfl
    intro i _
    have mom : φ (moment G i) = moment (G.map φ) i := by
      simp only [moment, ← Polynomial.map_pow, coeff_map]
    simp only [coe_mapRingHom, Polynomial.map_mul, Polynomial.map_pow,
      map_C, map_X, mom]
  simpa only [coe_mapRingHom, Polynomial.map_pow, map_X, Polynomial.map_sub,
    Polynomial.map_mul, jac, derivative_map, mc] using h

/-- Ordinary polynomials with the supplied coefficients through index s. -/
def plain {R : Type*} [CommRing R] (s : ℕ) (a : ℕ → R) : R[X] :=
  ∑ j ∈ Finset.range (s+1), C (a j)*X^j

private theorem map_clear {R A : Type*} [CommRing R] [CommRing A]
    (φ : R[X] →+* A) (F : R[X]) (w : A) (inv : φ F*w=1) (s : ℕ) (a : ℕ → R) :
    φ (clearTerms F s a) = φ F ^ s * (plain s a).eval₂ (φ.comp C) (φ X*w) := by
  rw [clearTerms, map_sum, plain, eval₂_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have le : j≤s := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  simp only [map_mul, map_pow, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, RingHom.comp_apply,
    mul_pow]
  have pw : φ F^s * w^j = φ F^(s-j) := by
    conv_lhs => rw [← Nat.sub_add_cancel le]
    rw [pow_add, mul_assoc, ← mul_pow, inv, one_pow, mul_one]
  calc
    _ = (φ F^s*w^j)*(φ (C (a j))*φ X^j) := by rw [pw]; ring
    _ = _ := by ring

/-- If a rational power series P/Q matches the diagonal moments up to and
including index m, its denominator/order budget must pass the stated bound.
The two coefficient lists can both depend on the input. -/
theorem finite_prefix (G : ℤ[X]) (ι : ℤ →+* K) (s m : ℕ) (a b : ℕ → K)
    (F0 : (G.map ι).coeff 0=1) (large : 2≤(G.map ι).natDegree)
    (char : ((G.map ι).natDegree:K)≠0) (a0 : a 0=1) (b0 : b 0=1)
    (fit : X^(m+1) ∣ plain s b * plain m (moment (G.map ι)) - plain s a) :
    m < (s+1)*(G.map ι).natDegree := by
  let F := G.map ι
  let cut : K[X] := X^(m+1)
  let π := AdjoinRoot.mk cut
  have xnil : π X^(m+1)=0 := by
    rw [← map_pow]
    exact AdjoinRoot.mk_self
  obtain ⟨U,hU⟩ := X_dvd_iff.mpr (show (F-1).coeff 0=0 by simp [F,F0])
  have cop : IsCoprime (X : K[X]) F := ⟨-U,1,by linear_combination hU⟩
  obtain ⟨V,W,hVW⟩ := (cop.pow_left : IsCoprime cut F)
  let w := π W
  have inv : π F*w=1 := by
    have key := congrArg π hVW
    simp only [map_add,map_mul,map_one,show π (X^(m+1))=0 from AdjoinRoot.mk_self, mul_zero,zero_add] at key
    exact (mul_comm _ _).trans key
  let ψ := eval₂RingHom (π.comp C) (π X*w)
  have cap : ψ cut=0 := by
    change eval₂ _ _ (X^(m+1) : K[X])=0
    rw [eval₂_pow,eval₂_X,mul_pow,xnil,zero_mul]
  obtain ⟨D,hD⟩ := fit
  have recurrence : ψ (plain s b) * ψ (plain m (moment F)) = ψ (plain s a) := by
    apply sub_eq_zero.mp
    have eqn := congrArg ψ hD
    simpa only [map_sub,map_mul,show ψ (X^(m+1))=0 from cap,zero_mul] using eqn
  have lag := (AdjoinRoot.mk_eq_zero.mpr (mapped_lagrange G ι m))
  change π (F^(m+1)-jac F*clearTerms F m (moment F))=0 at lag
  rw [map_sub,map_pow,map_mul,map_clear π F w inv] at lag
  have unit : IsUnit (π F) := isUnit_iff_exists_inv.mpr ⟨w,inv⟩
  have jj : π F = π (jac F)*ψ (plain m (moment F)) := by
    apply (unit.pow m).mul_left_cancel
    calc
      _ = π F^(m+1) := (pow_succ _ _).symm
      _ = _ := (sub_eq_zero.mp lag).trans (by change _ = π F^m*(π (jac F)* (plain m _).eval₂ _ _); ring)
  apply cleared_bound F s m a b large char a0 b0
  apply AdjoinRoot.mk_eq_zero.mp
  change π (F*clearTerms F s b-jac F*clearTerms F s a)=0
  rw [map_sub,map_mul,map_mul,map_clear π F w inv,map_clear π F w inv]
  change π F*(π F^s*ψ (plain s b))-π (jac F)*(π F^s*ψ (plain s a))=0
  linear_combination (π F^s*ψ (plain s b))*jj + (π F^s*π (jac F))*recurrence


private def cubic {R : Type*} [CommRing R] (c : R) : R[X] :=
  (X+C c)^3-(X+C c)

private theorem cubic_bound {R : Type*} [CommRing R] (c : R) : (cubic c).natDegree ≤ 3 := by
  unfold cubic
  compute_degree

private theorem moment_cubic {R : Type*} [CommRing R] (c : R) (j : ℕ) :
    moment (reflect 3 (cubic c)) j = TranslatedHasse.value j c := by
  have reflectP (i : ℕ) : (reflect 3 (cubic c))^i = reflect (i*3) ((cubic c)^i) := by
    induction i with
    | zero => simp
    | succ i ih =>
      have bound : ((cubic c)^i).natDegree ≤ i*3 :=
        natDegree_pow_le.trans (Nat.mul_le_mul_left i (cubic_bound c))
      rw [pow_succ, ih, Nat.succ_mul, pow_succ, reflect_mul _ _ bound (cubic_bound c)]
  rw [moment, reflectP, coeff_reflect, revAt_le (show j≤j*3 by omega),
    show j*3-j=2*j by omega]
  rfl

private theorem map_plain {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (m : ℕ) (a : ℕ → R) : (plain m a).map φ = plain m (fun i => φ (a i)) := by
  change (Polynomial.mapRingHom φ) _ = _
  rw [plain,map_sum,plain]
  simp only [coe_mapRingHom, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X]

private theorem cubic_size {p : ℕ} [Fact p.Prime] (five : 5≤p) (v : ZMod p) :
    let F := reflect 3 (cubic v)
    F.coeff 0=1 ∧ 2≤F.natDegree ∧ F.natDegree≤3 := by
  let F := reflect 3 (cubic v)
  have c2 : F.coeff 2 = 3*v^2-1 := by
    norm_num [F,cubic,coeff_sub,coeff_X_add_C_pow, coeff_add,coeff_X, coeff_C,revAt]
    ring
  have c3 : F.coeff 3 = v^3-v := by
    norm_num [F,cubic,coeff_sub,coeff_X_add_C_pow, coeff_add,coeff_X, coeff_C,revAt]
  refine ⟨?_,?_,?_⟩
  · norm_num [cubic,coeff_sub,coeff_X_add_C_pow, coeff_add,coeff_X, coeff_C,revAt]
  · change 2≤F.natDegree
    by_contra! low
    have h2 := coeff_eq_zero_of_natDegree_lt low
    have h3 := coeff_eq_zero_of_natDegree_lt (show F.natDegree<3 by omega)
    rw [c2] at h2
    rw [c3, show v^3-v=v*(v^2-1) by ring, mul_eq_zero] at h3
    rcases h3 with z | a
    · simp [z] at h2
    · have sq := sub_eq_zero.mp a
      have two : (2:ZMod p)≠0 := by
        exact fun z => (Nat.not_dvd_of_pos_of_lt (by decide : 0<2) (by omega : 2<p))
          ((ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).mp z)
      apply two
      linear_combination h2-3*sq
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [coeff_reflect,revAt_eq_self_of_lt hj]
    exact coeff_eq_zero_of_natDegree_lt ((cubic_bound v).trans_lt hj)

/-- For every integer translation of X³−X and any odd prime divisor at least
five, agreement through half-index m requires 3(s+1)>m. The normalized
polynomials P and Q may be chosen after seeing both modulus and translation. -/
theorem translated_prefix {n p : ℕ} [Fact p.Prime] (div : p∣n) (five : 5≤p)
    (c : ℤ) (s m : ℕ) (a b : ℕ → ZMod n) (a0 : a 0=1) (b0 : b 0=1)
    (fit : X^(m+1) ∣ plain s b * plain m (fun j => TranslatedHasse.value j (c:ZMod n))
      - plain s a) :
    m < 3*(s+1) := by
  let φ := ZMod.castHom div (ZMod p)
  let ι := Int.castRingHom (ZMod p)
  let G := reflect 3 (cubic c)
  have mapped : G.map ι = reflect 3 (cubic (c:ZMod p)) := by
    dsimp only [G]
    rw [← reflect_map]
    simp [cubic,ι]
  have h := (Polynomial.mapRingHom φ).map_dvd fit
  simp only [coe_mapRingHom,Polynomial.map_pow,map_X,Polynomial.map_sub,Polynomial.map_mul,
    map_plain] at h
  have vr (j : ℕ) : φ (TranslatedHasse.value j (c:ZMod n)) = moment (G.map ι) j := by
    rw [mapped,moment_cubic,← TranslatedHasse.cast_value,← TranslatedHasse.cast_value]
    exact map_intCast φ _
  simp only [vr] at h
  have size := cubic_size five (c:ZMod p)
  rw [← mapped] at size
  have ch : ((G.map ι).natDegree : ZMod p) ≠ 0 := by
    rw [ne_eq,ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have done := finite_prefix G ι s m (fun i => φ (a i)) (fun i => φ (b i)) size.1 size.2.1 ch
    (by simp [a0]) (by simp [b0]) h
  exact done.trans_le (by rw [Nat.mul_comm 3]; exact Nat.mul_le_mul_left _ size.2.2)

private theorem plain_coeff {R : Type*} [CommRing R] (a : ℕ → R) (s k : ℕ) :
    (plain s a).coeff k = if k≤s then a k else 0 := by
  simp [plain,finset_sum_coeff,coeff_C_mul, coeff_X_pow,Nat.lt_succ_iff]

/-- A homogeneous fixed-coefficient recurrence implies the usual rational
prefix fit. The first s+1 numerator coefficients absorb the initial terms. -/
private theorem fit_of_recurrence {R : Type*} [CommRing R] (a b : ℕ → R) (s m : ℕ)
    (a0 : a 0=1) (b0 : b 0=1)
    (rec : ∀ i, s < i → i ≤ m → (∑ j ∈ Finset.range (s+1), b j*a (i-j))=0) :
    ∃ u : ℕ → R, u 0=1 ∧ X^(m+1) ∣ plain s b*plain m a-plain s u := by
  let V := plain s b * plain m a
  refine ⟨V.coeff,?_,?_⟩
  · simp [V,mul_coeff_zero,plain_coeff,a0,b0]
  · apply X_pow_dvd_iff.mpr
    intro i hi
    rw [coeff_sub,plain_coeff]
    by_cases si : i≤s
    · simp [si,V]
    rw [if_neg si,sub_zero,plain,Finset.sum_mul,finset_sum_coeff]
    refine (Finset.sum_congr rfl fun j hj => ?_).trans (rec i (by omega) (by omega))
    have ij : j ≤ i := by have := Finset.mem_range.mp hj; omega
    rw [mul_assoc,coeff_C_mul,coeff_X_pow_mul',if_pos ij,plain_coeff,if_pos (by omega)]

/-- No homogeneous scalar recurrence of fixed order s can match the first
m+1 moments of any translated cubic modulo n unless m<3(s+1). This includes
matrix-power outputs by Cayley–Hamilton. The coefficients may depend on n,c. -/
theorem translated_recurrence {n p : ℕ} [Fact p.Prime] (div : p∣n) (five : 5≤p)
    (c : ℤ) (s m : ℕ) (b : ℕ → ZMod n) (b0 : b 0=1)
    (rec : ∀ i, s < i → i ≤ m → (∑ j ∈ Finset.range (s+1),
      b j * TranslatedHasse.value (i-j) (c:ZMod n))=0) :
    m < 3*(s+1) := by
  obtain ⟨a,a0,fit⟩ := fit_of_recurrence (fun j => TranslatedHasse.value j (c:ZMod n)) b s m
    (by simp [TranslatedHasse.value]) b0 rec
  exact translated_prefix div five c s m a b a0 b0 fit

/-- In particular, none of the full translated sequences admits a rational
generating function with a fixed denominator and numerator degree bound. -/
theorem no_fixed_rational {n p : ℕ} [Fact p.Prime] (div : p∣n) (five : 5≤p)
    (c : ℤ) (s : ℕ) (a b : ℕ → ZMod n) (a0 : a 0=1) (b0 : b 0=1) :
    ¬ ∀ m, X^(m+1) ∣ plain s b*plain m (fun j => TranslatedHasse.value j (c:ZMod n))-plain s a := by
  intro h
  exact (Nat.lt_irrefl _) (translated_prefix div five c s (3*(s+1)) a b a0 b0 (h _))

end PrimeFactors.HasseRecurrenceDegree
