import PrimeFactors.ProjectiveFixedLines
import PrimeFactors.Certificate
import PrimeFactors.PhaseCharacters
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Totient

/-!
# Complete moments of a determinant-one matrix family

The fixed-line total for the family (t,−1;1,0) counts all units. Replacing the
fixed-line count by its public Jacobi sign gives a complete sum of one. The
polynomially weighted Jacobi sums modulo the level agree with universal central
binomial coefficients in every degree below the smaller prime minus one.
-/

namespace PrimeFactors.ProjectiveWordMoments

open Finset PrimeFactors PrimeFactors.ProjectiveFixedLines

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- TᵗS with T=(1,1;0,1), S=(0,-1;1,0). -/
noncomputable def word (t : F) : Coeff F := ⟨t,-1,1,0⟩

noncomputable def traceUnit (u : Fˣ) : F := (u : F) + (u : F)⁻¹

omit [DecidableEq F] [Fintype F] in
theorem word_det (t : F) : det (word t)=1 := by simp [det, word]

omit [DecidableEq F] [Fintype F] in
theorem word_delta (t : F) : delta (word t)=t^2-4 := by simp [delta,word]; ring

private theorem finite_chart (t z : F) :
    some z ∈ fixed (word t) ↔ z*z-t*z+1=0 := by
  rw [finite_mem _ (by rw [word_det]; exact one_ne_zero)]
  simp [word,sub_eq_add_neg]

private theorem unit_chart (t : F) (u : Fˣ) :
    some (u:F) ∈ fixed (word t) ↔ traceUnit u=t := by
  rw [finite_chart]
  unfold traceUnit
  field_simp [u.ne_zero]
  constructor <;> intro h <;> linear_combination h

theorem fiber (t : F) :
    (fixed (word t)).card = (univ.filter fun u : Fˣ => traceUnit u = t).card := by
  symm
  apply card_bij (fun (u:Fˣ) _ => some (u:F))
  · intro u hu
    exact (unit_chart _ _).mpr (mem_filter.mp hu).2
  · intro u hu v hv eq
    exact Units.ext (Option.some.inj eq)
  · intro z hz
    cases z with
    | none => simp [infinity_mem,word] at hz
    | some z =>
      have nz : z ≠ 0 := by
        intro e
        subst z
        simp [finite_chart] at hz
      let u := Units.mk0 z nz
      exact ⟨u, mem_filter.mpr ⟨mem_univ _, (unit_chart t u).mp hz⟩, rfl⟩

theorem local_sum (p : ℕ) [Fact p.Prime] :
    ∑ t : ZMod p, (fixed (word t)).card = p-1 := by
  simp_rw [fiber]
  rw [sum_card_fiberwise_eq_card_filter]
  simp [Fintype.card_units,ZMod.card]

private theorem product_sum {p q : ℕ} [NeZero p] [NeZero q] {R : Type*}
    [CommSemiring R] (cop : p.Coprime q) (f : ZMod p → R) (h : ZMod q → R) :
    (∑ t : ZMod (p*q), f (ZMod.chineseRemainder cop t).1 * h (ZMod.chineseRemainder cop t).2)
      = (∑ u : ZMod p, f u)*(∑ v : ZMod q, h v) := by
  let e := ZMod.chineseRemainder cop
  calc
    _ = ∑ t : ZMod p × ZMod q, f t.1 * h t.2 := Fintype.sum_equiv e.toEquiv _ _ (fun _ => rfl)
    _ = _ := by rw [Fintype.sum_prod_type]; simp only [← mul_sum, ← sum_mul]

/-- Summing the fixed-line counts over every trace parameter gives the totient. -/
theorem full_fixed {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q) :
    (∑ t : ZMod (p*q), (both (word (ZMod.chineseRemainder cop t).1)
      (word (ZMod.chineseRemainder cop t).2)).card) = (p-1)*(q-1) := by
  simp_rw [both_count]
  rw [product_sum cop (fun t => (fixed (word t)).card) (fun t => (fixed (word t)).card), local_sum, local_sum]

private theorem local_signed {p : ℕ} [Fact p.Prime] (odd : p ≠ 2) :
    ∑ t : ZMod p, quadraticChar (ZMod p) (t^2-4) = -1 := by
  have distinct : (2:ZMod p) ≠ -2 := by
    have hh : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    intro h
    apply mul_ne_zero hh hh
    linear_combination h
  have eq (t : ZMod p) : t^2-4 = (t+2)*(t+(-2)) := by ring
  simpa only [eq] using phaseCharacters_shift_sum (F := ZMod p)
    (by rwa [ZMod.ringChar_zmod_n]) distinct

private theorem actual_symbol {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (t : ZMod (p*q)) :
    jacobiSym ((t.val:ℤ)^2-4) (p*q) =
      quadraticChar (ZMod p) ((ZMod.chineseRemainder cop t).1^2-4) *
      quadraticChar (ZMod q) ((ZMod.chineseRemainder cop t).2^2-4) := by
  rw [jacobiSym.mul_right, ← jacobiSym.legendreSym.to_jacobiSym, ← jacobiSym.legendreSym.to_jacobiSym]
  have cast : ZMod.chineseRemainder cop t = ((t.val : ZMod p),(t.val : ZMod q)) := by
    conv_lhs => arg 2; rw [← ZMod.natCast_zmod_val t]
    rw [map_natCast]
    rfl
  simp [legendreSym,cast]

/-- The unweighted signed sum is exactly one as an integer. -/
theorem full_signed {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p ≠ 2) (hq : q ≠ 2) :
    ∑ t : ZMod (p*q), jacobiSym ((t.val:ℤ)^2-4) (p*q) = 1 := by
  simp_rw [actual_symbol cop]
  rw [product_sum cop (fun t => quadraticChar _ (t^2-4)) (fun t => quadraticChar _ (t^2-4)),
    local_signed hp, local_signed hq]
  norm_num

/-- Constant coefficient of the Laurent polynomial (X + 1/X)^k. -/
def central (k : ℕ) := if k%2=0 then k.choose (k/2) else 0

private theorem monomial_sum (i j : ℕ) (hi : i < Fintype.card F-1) (hj : j < Fintype.card F-1) :
    (∑ u : Fˣ, (u:F)^i * (u:F)⁻¹^j) = if i=j then (-1 : F) else 0 := by
  by_cases h : j ≤ i
  · have eq (u : Fˣ) : (u:F)^i*(u:F)⁻¹^j = (u:F)^(i-j) := by
      conv_lhs => rw [show i = i-j+j by omega, pow_add]
      simp [inv_pow,u.ne_zero]
    simp_rw [eq]
    rw [FiniteField.sum_pow_units F]
    by_cases same : i=j
    · simp [same]
    · have nd : ¬Fintype.card F-1 ∣ i-j := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      simp [nd,same]
  · have eq (u : Fˣ) : (u:F)^i*(u:F)⁻¹^j = ((u⁻¹ : Fˣ):F)^(j-i) := by
      conv_lhs => rw [show j = i+(j-i) by omega, pow_add]
      simp [mul_assoc, ← mul_assoc, inv_pow, u.ne_zero]
    simp_rw [eq]
    have perm := Equiv.sum_comp (Equiv.inv Fˣ) (fun x : Fˣ => (x : F)^(j-i))
    change (∑ x : Fˣ, ((x⁻¹ : Fˣ):F)^(j-i)) = _ at perm
    rw [perm, FiniteField.sum_pow_units F]
    have nd : ¬Fintype.card F-1 ∣ j-i := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    simp [nd,show i ≠ j by omega]

omit [DecidableEq F] [Fintype F] in
private theorem diagonal_sum (k : ℕ) :
    (∑ i ∈ range (k+1), if 2*i=k then -(k.choose i : F) else 0) = -(central k : F) := by
  by_cases even : k%2=0
  · have eq (i : ℕ) : 2*i = k ↔ i=k/2 := by omega
    simp [eq,central,even, show k/2 < k+1 by omega]
  · have eq (i : ℕ) : 2*i ≠ k := by omega
    simp [eq,central,even]

theorem trace_moment (k : ℕ) (small : k < Fintype.card F-1) :
    (∑ x : Fˣ, (traceUnit x)^k) = -(central k : F) := by
  calc
    _ = ∑ i ∈ range (k+1), (if 2*i=k then -(k.choose i : F) else 0) := by
      simp_rw [traceUnit,add_pow]
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      have bound := mem_range.mp hi
      rw [← sum_mul, monomial_sum i (k-i) (by omega) (by omega)]
      by_cases h : i=k-i
      · rw [if_pos h, if_pos (show 2*i=k by omega)]; simp
      · simp [h, show 2*i≠k by omega]
    _ = _ := diagonal_sum k

private theorem card_sign [NeZero (2:F)] (t : F) :
    ((fixed (word t)).card : ℤ) = 1+quadraticChar F (t^2-4) := by
  rw [nonscalar_count _ (by rw [word_det];exact one_ne_zero)
    (by simp [scalar,word]), word_delta]
  classical
  by_cases z : t^2-4=0
  · simp [squareCount,z]
  · by_cases s : IsSquare (t^2-4)
    · simp [squareCount,z,s,(quadraticChar_one_iff_isSquare z).mpr s]
    · simp [squareCount,z,s,quadraticChar_neg_one_iff_not_isSquare.mpr s]

private theorem signed_pullback {p : ℕ} [Fact p.Prime] (odd : p≠2) (k : ℕ) :
    (∑ t : ZMod p, t^k*((quadraticChar (ZMod p) (t^2-4) : ℤ) : ZMod p)) = (∑ u : (ZMod p)ˣ, (traceUnit u)^k) - ∑ t : ZMod p, t^k := by
  let F := ZMod p
  letI : NeZero (2 : ZMod p) := ⟨Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])⟩
  have term (t : F) : ((quadraticChar F (t^2-4) : ℤ) : F) =
      ((univ.filter fun u : Fˣ => traceUnit u=t).card : F)-1 := by
    have eq := congrArg (fun v : ℤ => (v : F)) (card_sign t)
    rw [← fiber]
    push_cast at eq
    linear_combination -eq
  change (∑ t : F, t^k*((quadraticChar F (t^2-4) : ℤ):F))=_
  simp_rw [term,mul_sub,mul_one]
  rw [sum_sub_distrib]
  congr 1
  rw [← sum_fiberwise_of_maps_to' (s := (univ : Finset Fˣ)) (t := (univ : Finset F))
      (g := traceUnit) (fun _ _ => mem_univ _) (fun x : F => x^k)]
  apply sum_congr rfl
  intro t _
  simp [mul_comm]

private theorem signed_moment {p : ℕ} [Fact p.Prime] (odd : p≠2) (k : ℕ) (small : k<p-1) :
    (∑ t : ZMod p, t^k*((quadraticChar (ZMod p) (t^2-4) : ℤ) : ZMod p)) = -(central k : ZMod p) := by
  have small' : k < Fintype.card (ZMod p)-1 := by simpa only [ZMod.card] using small
  rw [signed_pullback odd, trace_moment k small', FiniteField.sum_pow_lt_card_sub_one _ _ small', sub_zero]

/-- Complete weighted Jacobi sum reduced modulo its level. -/
noncomputable def moment (n k : ℕ) [NeZero n] : ZMod n :=
  ∑ t : ZMod n, t^k*((jacobiSym ((t.val:ℤ)^2-4) n : ℤ) : ZMod n)

private theorem components {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (k : ℕ) :
    ZMod.chineseRemainder cop (moment (p*q) k) =
      (-(∑ t : ZMod p, t^k*((quadraticChar (ZMod p) (t^2-4) : ℤ) : ZMod p)),
       -(∑ t : ZMod q, t^k*((quadraticChar (ZMod q) (t^2-4) : ℤ) : ZMod q))) := by
  unfold moment
  let e := ZMod.chineseRemainder cop
  let left := (RingHom.fst (ZMod p) (ZMod q)).comp e.toRingHom
  let right := (RingHom.snd (ZMod p) (ZMod q)).comp e.toRingHom
  let lp (x : ZMod p) := quadraticChar (ZMod p) (x^2-4)
  let lq (x : ZMod q) := quadraticChar (ZMod q) (x^2-4)
  apply Prod.ext
  · change left _ = -_
    simp only [map_sum, map_mul, map_pow, map_intCast, map_natCast, actual_symbol cop, Int.cast_mul]
    calc
      _ = ∑ t : ZMod (p*q), (((e t).1)^k * (lp (e t).1 : ZMod p)) * (lq (e t).2 : ZMod p) := by
        apply sum_congr rfl
        intro t _
        change (e t).1^k * (↑(lp (e t).1) * ↑(lq (e t).2)) = _
        ring
      _ = (∑ t : ZMod p, t^k*(lp t : ZMod p)) * ∑ t : ZMod q, (lq t : ZMod p) :=
        product_sum cop (fun t => t^k*(lp t : ZMod p)) (fun t => (lq t : ZMod p))
      _ = _ := by
        simp only [lp,lq, ← Int.cast_sum, local_signed hq,Int.cast_neg,Int.cast_one]
        ring
  · change right _ = -_
    simp only [map_sum, map_mul, map_pow, map_intCast, map_natCast, actual_symbol cop, Int.cast_mul]
    calc
      _ = ∑ t : ZMod (p*q), (lp (e t).1 : ZMod q) * (((e t).2)^k * (lq (e t).2 : ZMod q)) := by
        apply sum_congr rfl
        intro t _
        change (e t).2^k * (↑(lp (e t).1) * ↑(lq (e t).2)) = _
        ring
      _ = (∑ t : ZMod p, (lp t : ZMod q)) * ∑ t : ZMod q, t^k*(lq t : ZMod q) :=
        product_sum cop (fun t => (lp t : ZMod q)) (fun t => t^k*(lq t : ZMod q))
      _ = _ := by
        simp only [lp,lq, ← Int.cast_sum, local_signed hp,Int.cast_neg,Int.cast_one]
        ring

private theorem weighted_odd {p : ℕ} [Fact p.Prime] (hp : p≠2) (k : ℕ) (ok : Odd k) :
    (∑ t : ZMod p, t^k*((quadraticChar (ZMod p) (t^2-4) : ℤ) : ZMod p)) = 0 := by
  let f (t : ZMod p) := t^k*((quadraticChar (ZMod p) (t^2-4) : ℤ) : ZMod p)
  have neg (t : ZMod p) : f (-t) = -f t := by simp [f,ok.neg_pow]
  have same := Equiv.sum_comp (Equiv.neg (ZMod p)) f
  change (∑ t, f (-t)) = ∑ t, f t at same
  simp only [neg,sum_neg_distrib] at same
  have two : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  apply (mul_eq_zero.mp (show 2 * (∑ t, f t) = 0 by linear_combination -same)).resolve_left two

/-- Odd powers cancel at every degree, including those above the first exception. -/
theorem odd_moment {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (k : ℕ) (ok : Odd k) : moment (p*q) k = 0 := by
  apply (ZMod.chineseRemainder cop).injective
  rw [components cop hp hq, weighted_odd hp k ok, weighted_odd hq k ok, map_zero]
  simp

/-- Every complete low-degree Jacobi moment has a universal constant-term formula modulo pq. -/
theorem jacobi_moment {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (k : ℕ) (kp : k<p-1) (kq : k<q-1) :
    moment (p*q) k = (central k : ZMod (p*q)) := by
  apply (ZMod.chineseRemainder cop).injective
  rw [components cop hp hq, signed_moment hp k kp, signed_moment hq k kq, map_natCast]
  simp only [neg_neg]
  rfl

private theorem trace_endpoint (k : ℕ) (eq : k=Fintype.card F-1) (pos : 0<k) :
    (∑ x : Fˣ, (traceUnit x)^k) = -(central k : F)-2 := by
  have unitSum : (∑ u : Fˣ, (u:F)^k) = -1 := by rw [FiniteField.sum_pow_units F,eq,if_pos dvd_rfl]
  have invSum' : (∑ u : Fˣ, ((u:F)^k)⁻¹) = -1 := by
    have h := (Equiv.sum_comp (Equiv.inv Fˣ) (fun u : Fˣ => (u:F)^k)).trans unitSum
    change (∑ u : Fˣ, ((u⁻¹ : Fˣ):F)^k) = -1 at h
    simpa only [Units.val_inv_eq_inv_val,inv_pow] using h
  calc
    _ = ∑ i ∈ range (k+1), ((if 2*i=k then -(k.choose i : F) else 0)
        + (if i=0 then -1 else 0) + (if i=k then -1 else 0)) := by
      simp_rw [traceUnit,add_pow]
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      rw [← sum_mul]
      by_cases iz : i=0
      · subst i
        simp [pos.ne',pos.ne,invSum']
      by_cases ik : i=k
      · subst i
        simp [pos.ne', unitSum, show 2*k ≠ k by omega]
      have bound := mem_range.mp hi
      rw [monomial_sum i (k-i) (by omega) (by omega)]
      by_cases h : i=k-i
      · rw [if_pos h, if_pos (show 2*i=k by omega), if_neg iz, if_neg ik]
        simp
      · simp [h, show 2*i≠k by omega, iz, ik]
    _ = _ := by simp [sum_add_distrib, diagonal_sum]; ring

private theorem signed_boundary {p : ℕ} [Fact p.Prime] (odd : p≠2) :
    (∑ t : ZMod p, t^(p-1)*((quadraticChar (ZMod p) (t^2-4) : ℤ) : ZMod p)) =
      -(central (p-1) : ZMod p)-1 := by
  have op := (Fact.out : p.Prime).one_lt
  have pos : 0 < p-1 := by omega
  have ek : p-1=Fintype.card (ZMod p)-1 := by rw [ZMod.card]
  have fieldSum : (∑ t : ZMod p, t^(p-1)) = -1 := by
    have term (t : ZMod p) : t^(p-1) = (if t=0 then 0 else 1) := by
      by_cases z : t=0
      · simp [z,pos.ne']
      · simpa [z,ZMod.card] using (FiniteField.pow_card_sub_one_eq_one t z)
    simp_rw [term, show ∀x : ZMod p, (if x=0 then (0:ZMod p) else 1) =
      1-(if x=0 then 1 else 0) by intro t;split <;> simp]
    simp [sum_sub_distrib,ZMod.card]
  rw [signed_pullback odd,trace_endpoint _ ek pos,fieldSum]
  ring

/-- The first exceptional moment differs from the uniform prediction by the CRT pair (1,0). -/
theorem boundary {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (order : p<q) :
    ZMod.chineseRemainder cop (moment (p*q) (p-1) - (central (p-1) : ZMod (p*q))) = (1,0) := by
  have op := (Fact.out : p.Prime).one_lt
  rw [map_sub, components cop hp hq, signed_boundary hp, signed_moment hq _ (by omega), map_natCast]
  apply Prod.ext <;> simp


/-- The canonical nonnegative representative of the boundary discrepancy has
gcd exactly q with pq. The degree in this theorem is p−1. -/
theorem boundary_gcd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (order : p<q) :
    (p*q).gcd (moment (p*q) (p-1) - (central (p-1) : ZMod (p*q))).val = q := by
  let d := moment (p*q) (p-1) - (central (p-1) : ZMod (p*q))
  have crt : ZMod.chineseRemainder cop d = (1,0) := boundary cop hp hq order
  have casts : ((d.val : ZMod p), (d.val : ZMod q)) = (1,0) := calc
    _ = ZMod.chineseRemainder cop (d.val : ZMod (p*q)) := by rw [map_natCast]; rfl
    _ = (1,0) := by rw [ZMod.natCast_zmod_val, crt]
  have qd := (ZMod.natCast_zmod_eq_zero_iff_dvd d.val q).mp (congrArg Prod.snd casts)
  have pd : ¬p ∣ d.val := by
    intro h
    exact (zero_ne_one : (0 : ZMod p) ≠ 1) (((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr h).symm.trans
      (congrArg Prod.fst casts))
  obtain ⟨w, hw⟩ := qd
  have pw : p.Coprime w := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun h =>
    pd (hw ▸ h.trans (dvd_mul_left w q)))
  change (p*q).gcd d.val = q
  rw [hw, mul_comm q w, Nat.gcd_mul_right, pw, one_mul]

/-- Linear combinations of low powers provide no further information modulo the level. -/
theorem polynomial_moment {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (d : ℕ) (a : Fin d → ZMod (p*q))
    (sp : d≤p-1) (sq : d≤q-1) :
    (∑ t : ZMod (p*q), (∑ i : Fin d, a i*t^(i:ℕ)) *
      ((jacobiSym ((t.val:ℤ)^2-4) (p*q) : ℤ) : ZMod (p*q))) =
    ∑ i : Fin d, a i*(central i : ZMod (p*q)) := by
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp_rw [mul_assoc]
  rw [← mul_sum, ←jacobi_moment cop hp hq i (lt_of_lt_of_le i.isLt sp) (lt_of_lt_of_le i.isLt sq)]
  rfl

/-- The smaller prime minus one is the first degree whose complete moment departs
from the low-degree formula. -/
theorem first_exception {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (order : p<q) :
    IsLeast {k : ℕ | moment (p*q) k ≠ (central k : ZMod (p*q))} (p-1) := by
  constructor
  · intro same
    have h := boundary cop hp hq order
    rw [same,sub_self,map_zero] at h
    exact zero_ne_one (congrArg Prod.fst h : (0 : ZMod p) = 1)
  · intro k bad
    by_contra! small
    have pp := (Fact.out : p.Prime).one_lt
    exact bad (jacobi_moment cop hp hq k small (by omega))


private theorem local_nonzero_count {p : ℕ} [Fact p.Prime] (odd : p≠2) :
    (univ.filter fun t : ZMod p => quadraticChar (ZMod p) (t^2-4) ≠ 0).card = p-2 := by
  have two : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have distinct : (2:ZMod p) ≠ -2 := by
    intro h
    apply mul_ne_zero two two
    linear_combination h
  have zeros : (univ.filter fun t : ZMod p => quadraticChar (ZMod p) (t^2-4)=0) = {2,-2} := by
    ext t
    simp only [mem_filter,mem_univ,true_and,quadraticChar_eq_zero_iff,mem_insert,mem_singleton]
    rw [show t^2-4 = (t-2)*(t+2) by ring,mul_eq_zero,sub_eq_zero,add_eq_zero_iff_eq_neg]
  have total := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (ZMod p)))
    (fun t => quadraticChar (ZMod p) (t^2-4)=0)
  rw [zeros,card_pair distinct,card_univ,ZMod.card] at total
  exact Nat.eq_sub_of_add_eq' total

/-- The zeros of the public Jacobi sign are exactly the nonunit discriminants.
Counting all these zeros would supply the same factor-sum information. -/
theorem zero_count {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) :
    (univ.filter fun t : ZMod (p*q) => jacobiSym ((t.val:ℤ)^2-4) (p*q)=0).card =
      2*(p+q)-4 := by
  let j (t : ZMod (p*q)) := jacobiSym ((t.val:ℤ)^2-4) (p*q)
  let s (l : ℕ) [Fact l.Prime] := univ.filter fun t : ZMod l => quadraticChar (ZMod l) (t^2-4) ≠ 0
  have reg : (univ.filter fun t => j t ≠ 0).card = ((s p) ×ˢ (s q)).card := by
    apply card_equiv (ZMod.chineseRemainder cop).toEquiv
    intro t
    simp only [j,s,mem_filter,mem_univ,true_and,mem_product,actual_symbol cop,mul_ne_zero_iff]
    rfl
  rw [card_product, local_nonzero_count hp,local_nonzero_count hq] at reg
  have all := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (ZMod (p*q)))) (fun t => j t=0)
  rw [reg,card_univ,ZMod.card] at all
  change (univ.filter fun t => j t=0).card=_
  have rp := (Fact.out : p.Prime).two_le
  have rq := (Fact.out : q.Prime).two_le
  have identity : p*q=(p-2)*(q-2)+ (2*(p+q)-4) := by
    have pe : p=p-2+2 := by omega
    have qe : q=q-2+2 := by omega
    have both : 2*(p+q)-4+4=2*(p+q) := by omega
    nlinarith only [congrArg₂ Nat.mul pe qe,both,pe,qe]
  omega

/-- Even-degree equality returns after the first even-degree failure. -/
theorem even_equality_returns :
    moment 15 2 = 12 ∧ (central 2 : ZMod 15) = 2 ∧
    moment 15 10 = 12 ∧ (central 10 : ZMod 15) = 12 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let cop : Nat.Coprime 3 5 := by decide
  have bd := boundary cop (by decide) (by decide) (by decide)
  change ZMod.chineseRemainder cop (moment 15 2 - 2) = (1,0) at bd
  have value : ZMod.chineseRemainder cop (12-2) = (1,0) := by
    rw [map_sub, map_ofNat, map_ofNat]
    decide +kernel
  have two : moment 15 2 = 12 := by
    have eq := (ZMod.chineseRemainder cop).injective (bd.trans value.symm)
    linear_combination eq
  have same : ∀ x : ZMod 15, x^10=x^2 := by decide +kernel
  have ten : moment 15 10 = moment 15 2 := by simp only [moment, same]
  exact ⟨two, by decide, ten.trans two, by decide⟩

/-- Exact prime factors for the five bounded primitive-coordinate comparisons. -/
theorem toy_factorizations :
    ExactFactorization 15 [3,5] ∧ ExactFactorization 35 [5,7] ∧
    ExactFactorization 77 [7,11] ∧ ExactFactorization 143 [11,13] ∧
    ExactFactorization 221 [13,17] := by
  norm_num [ExactFactorization]

end PrimeFactors.ProjectiveWordMoments
