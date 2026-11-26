import PrimeFactors.HasseShiftDegree
import PrimeFactors.SieveInterval
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic

/-! Translated central coefficients of powers of the cubic X³ − X. -/
noncomputable section
open Polynomial
open scoped Polynomial

namespace PrimeFactors.TranslatedHasse

variable {R : Type*} [CommRing R]

/-- The translation parameter is the argument of this polynomial. -/
def shiftPoly (R : Type*) [CommRing R] (h : ℕ) : R[X] :=
  hasseDeriv (2*h) ((X^3-X)^h)

/-- Integer or residue-ring computation at the half-index h=(n−1)/2. -/
def value (h : ℕ) (c : R) : R :=
  (((X+C c)^3-(X+C c))^h).coeff (2*h)

theorem shift_eval (h : ℕ) (c : R) : (shiftPoly R h).eval c = value h c := by
  rw [shiftPoly, ← taylor_coeff, taylor_apply]
  simp [value]

private theorem cubic_degree (c : R) (h : ℕ) :
    ((((X+C c)^3-(X+C c))^h) : R[X]).natDegree ≤ 3*h := by
  have d : ((X+C c) : R[X]).natDegree ≤ 1 := by compute_degree
  calc
    _ ≤ _ := natDegree_pow_le
    _ ≤ 3*h := by
      have d' := natDegree_sub_le ((X+C c : R[X])^3) (X+C c)
      have d'' := natDegree_pow_le (p := (X+C c : R[X])) (n := 3)
      have ds : (((X+C c)^3-(X+C c)) : R[X]).natDegree ≤ 3 := by omega
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right h ds

theorem shift_degree (h : ℕ) : (shiftPoly R h).natDegree ≤ h := by
  have d := cubic_degree (0:R) h
  simp only [map_zero, add_zero] at d
  exact (natDegree_hasseDeriv_le _ _).trans (by omega)

private theorem extract {h p j : ℕ} (halfp : p=2*h+1)
    (A B : R[X]) (degA : A.natDegree ≤ 3*h) :
    (A * expand R p B).coeff (2*h+p*j) = A.coeff (2*h)*B.coeff j := by
  classical
  have pp : 0 < p := by omega
  rw [coeff_mul, Finset.sum_eq_single (2*h,p*j), coeff_expand_mul' pp]
  · rintro ⟨i,l⟩ hi ne
    have eqn := Finset.mem_antidiagonal.mp hi
    change i + l = 2*h+p*j at eqn
    change A.coeff i * (expand R p B).coeff l = 0
    by_cases dhi : A.natDegree < i
    · simp [coeff_eq_zero_of_natDegree_lt dhi]
    by_cases dl : p ∣ l
    · obtain ⟨k,rfl⟩ := dl
      have kj : k=j := by
        rcases lt_trichotomy k j with lt|eq|gt
        · have mul := Nat.mul_le_mul_left p (show k+1≤j by omega)
          rw [Nat.mul_succ] at mul
          omega
        · exact eq
        · have mul := Nat.mul_le_mul_left p (show j+1≤k by omega)
          rw [Nat.mul_succ] at mul
          omega
      subst k
      exact (ne (Prod.ext (by simpa using eqn) rfl)).elim
    · simp [coeff_expand pp, dl]
  · simp [Finset.mem_antidiagonal]

/-- Frobenius leaves only one coefficient in the convolution. -/
theorem product_local {p h : ℕ} [Fact p.Prime] (halfp : p=2*h+1)
    (k : ℕ) (c : ZMod p) : value (h+p*k) c = value h c * value k c := by
  let f : (ZMod p)[X] := (X+C c)^3-(X+C c)
  change (f^(h+p*k)).coeff (2*(h+p*k)) = (f^h).coeff (2*h)*(f^k).coeff (2*k)
  rw [show 2*(h+p*k)=2*h+p*(2*k) by ring, pow_add, mul_comm p k, pow_mul,
    ← ZMod.expand_card]
  exact extract halfp _ _ (cubic_degree c h)

/-- A prime's own central coefficient is independent of translation in its residue field. -/
theorem own_constant {p h : ℕ} [Fact p.Prime] (halfp : p=2*h+1) :
    shiftPoly (ZMod p) h = C (((X^3-X) ^ h : (ZMod p)[X]).coeff (2*h)) := by
  ext j
  by_cases jzero : j=0
  · subst j
    simp [shiftPoly, hasseDeriv_coeff]
  rw [coeff_C, if_neg jzero]
  by_cases jb : h < j
  · exact coeff_eq_zero_of_natDegree_lt ((shift_degree h).trans_lt jb)
  rw [shiftPoly, hasseDeriv_coeff]
  have pd := (Fact.out : p.Prime).dvd_choose (a:=2*h) (b:=j+2*h)
    (by omega) (by omega) (by omega)
  rw [(ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr pd, zero_mul]

/-- Coefficients of the translated family before applying the Hasse derivative. -/
theorem cubic_coeff (h l : ℕ) :
    (((X^3-X)^h : R[X]).coeff (h+l)) =
      if 2∣l then (-1:R)^(h-l/2)*(h.choose (l/2):R) else 0 := by
  have rep : (X^3-X : R[X]) = X * expand R 2 (X + C (-1)) := by simp; ring
  rw [rep, mul_pow, ← map_pow, Nat.add_comm h l, coeff_X_pow_mul, coeff_expand (by decide : 0<2),
    coeff_X_add_C_pow]

private theorem choose_unit {q h j : ℕ} [Fact q.Prime] (hq : h<q) (hj : j≤h) :
    (h.choose j : ZMod q) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_zmod_eq_zero_iff_dvd]
  intro dv
  have d : q ∣ h.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hj]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left dv _) _
  exact (Nat.not_le_of_lt hq) ((Fact.out : q.Prime).dvd_factorial.mp d)

theorem inert_zero {r h : ℕ} [Fact r.Prime] (hr : r=2*h+1) (odd : h%2=1)
    (c : ZMod r) : value h c = 0 := by
  rw [← shift_eval, own_constant hr, eval_C, two_mul, cubic_coeff h h]
  simp [show ¬2∣h by omega]

theorem split_nonzero {q k : ℕ} [Fact q.Prime] (hq : q=2*k+1) (even : k%2=0)
    (c : ZMod q) : value k c ≠ 0 := by
  rw [← shift_eval, own_constant hq, eval_C, two_mul, cubic_coeff k k,
    if_pos (show 2∣k by omega)]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (choose_unit (by omega) (by omega))

/-- The linear coefficient survives modulo the other prime. -/
theorem mixed_poly_nonzero {r q h : ℕ} [Fact r.Prime] [Fact q.Prime]
    (hr : r=2*h+1) (odd : h%2=1) (distinct : r≠q) (small : h<q) :
    shiftPoly (ZMod q) h ≠ 0 := by
  have rne : (r:ZMod q) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact fun d => distinct ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime)
      (Fact.out : r.Prime)).mp d).symm
  intro z
  have hz := congrArg (fun f : (ZMod q)[X] => f.coeff 1) z
  change (hasseDeriv (2*h) ((X^3-X)^h : (ZMod q)[X])).coeff 1 = (0:(ZMod q)[X]).coeff 1 at hz
  rw [hasseDeriv_coeff, show 1+2*h=(2*h)+1 by omega, Nat.choose_succ_self_right,
    show 2*h+1 = h+(h+1) by omega, cubic_coeff h (h+1), if_pos (show 2∣h+1 by omega),
    coeff_zero] at hz
  have hcast : ((2*h+1:ℕ):ZMod q) ≠ 0 := hr ▸ rne
  apply (mul_ne_zero hcast (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (choose_unit small (show (h+1)/2≤h by omega))))
  simpa only [show h+(h+1)=2*h+1 by omega] using hz

/-- The public integer coefficient, indexed by the product itself. -/
def reading (n : ℕ) (c : ℤ) : ℤ := value ((n-1)/2) c

theorem cast_value (m h : ℕ) (c : ℤ) :
    ((value h c : ℤ) : ZMod m) = value h (c : ZMod m) := by
  change (Int.castRingHom (ZMod m)) _ = _
  rw [value, ← coeff_map]
  simp [value]

private theorem product_half {p q h k : ℕ} (hp : p=2*h+1) (hq : q=2*k+1) :
    (p*q-1)/2 = h+p*k := by
  rw [hq, Nat.mul_add, Nat.mul_one, show p*(2*k)=2*(p*k) by ring]
  omega

/-- Multiplicativity for the translated integer coefficients holds modulo the
whole product of distinct odd primes, including when both local readings vanish. -/
theorem product_congruence {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (po : Odd p) (qo : Odd q) (distinct : p≠q) (c : ℤ) :
    reading (p*q) c ≡ reading p c * reading q c [ZMOD (p:ℤ)*q] := by
  obtain ⟨h,hp⟩ := po
  obtain ⟨k,hq⟩ := qo
  have localRead {a b s t : ℕ} [Fact a.Prime] (ha : a=2*s+1) (hb : b=2*t+1) :
      reading (a*b) c ≡ reading a c * reading b c [ZMOD (a:ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff ..).mp
    simp only [reading, Int.cast_mul, cast_value, product_half ha hb, product_local ha,
      show (a-1)/2=s by omega, show (b-1)/2=t by omega]
  apply (Int.modEq_and_modEq_iff_modEq_mul (m := (p:ℤ)) (n := (q:ℤ)) ?_).mp
  · exact ⟨localRead hp hq, by simpa [mul_comm] using localRead hq hp⟩
  · simpa using ((Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr distinct)

/-- Exactly the zeros of the other prime's translation polynomial block the gcd. -/
theorem readout_iff {r q h k : ℕ} [Fact r.Prime] [Fact q.Prime]
    (hr : r=2*h+1) (hq : q=2*k+1) (odd : h%2=1) (even : k%2=0)
    (distinct : r≠q) (c : ℤ) :
    (r*q).gcd (reading (r*q) c).natAbs = r ↔ (shiftPoly (ZMod q) h).eval (c:ZMod q) ≠ 0 := by
  let z := reading (r*q) c
  have left : (z:ZMod r) = 0 := by
    rw [show z=value ((r*q-1)/2) c by rfl, cast_value,
      product_half hr hq, product_local hr, inert_zero hr odd, zero_mul]
  have right : (z:ZMod q) = 0 ↔ (shiftPoly (ZMod q) h).eval (c:ZMod q) = 0 := by
    rw [show z=value ((r*q-1)/2) c by rfl, cast_value, Nat.mul_comm r q,
      product_half hq hr, product_local hq, shift_eval, mul_eq_zero]
    simp [split_nonzero hq even]
  have cast_dvd (p : ℕ) : (z : ZMod p)=0 ↔ p∣z.natAbs := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← Int.natAbs_dvd_natAbs]
    simp
  obtain ⟨a,ha⟩ := (cast_dvd r).mp left
  change (r*q).gcd z.natAbs = r ↔ _
  refine Iff.trans ?_ (not_congr right)
  rw [cast_dvd q, ha, Nat.gcd_mul_left]
  have qr := (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
    (fun d => distinct ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime)
      (Fact.out : r.Prime)).mp d).symm)
  have rp := (Fact.out : r.Prime).pos
  rw [(Fact.out : q.Prime).dvd_mul, or_iff_right ((Fact.out : q.Prime).coprime_iff_not_dvd.mp qr),
    ← (Fact.out : q.Prime).coprime_iff_not_dvd, Nat.coprime_iff_gcd_eq_one]
  exact ⟨fun eqn => Nat.eq_of_mul_eq_mul_left rp (eqn.trans (Nat.mul_one r).symm),
    fun eqn => by rw [eqn, Nat.mul_one]⟩

/-- Actual successful public gcds among the representatives 0,…,q−1. -/
def successful (r q : ℕ) [Fact q.Prime] : Finset (ZMod q) :=
  Finset.univ.filter fun c => (r*q).gcd (reading (r*q) (c.val:ℤ)).natAbs = r

theorem mixed_count {r q h k : ℕ} [Fact r.Prime] [Fact q.Prime]
    (hr : r=2*h+1) (hq : q=2*k+1) (odd : h%2=1) (even : k%2=0)
    (distinct : r≠q) (small : h<q) :
    q ≤ (successful r q).card + (shiftPoly (ZMod q) h).natDegree := by
  classical
  let G := shiftPoly (ZMod q) h
  have nz : G ≠ 0 := mixed_poly_nonzero hr odd distinct small
  have neg : (Finset.univ.filter (fun c : ZMod q => G.eval c=0)).card ≤ G.natDegree := by
    apply card_le_degree_of_subset_roots
    intro c hc
    exact (mem_roots nz).mpr (Finset.mem_filter.mp hc).2
  have good : successful r q = Finset.univ.filter (fun c : ZMod q => G.eval c ≠ 0) := by
    ext c
    simpa only [successful, Finset.mem_filter, Finset.mem_univ, true_and, Int.cast_natCast,
      ZMod.natCast_zmod_val] using (readout_iff hr hq odd even distinct (c.val:ℤ))
  have all := Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ)
    (fun c : ZMod q => G.eval c=0)
  rw [← good, Finset.card_univ, ZMod.card] at all
  change q ≤ (successful r q).card + G.natDegree
  omega

/-- A third of shifts always work for balanced mixed primes. If the inert prime
is smaller, two thirds work. Bounds count distinct residues modulo the split prime. -/
theorem mixed_thirds {r q : ℕ} [Fact r.Prime] [Fact q.Prime]
    (inert : r%4=3) (split : q%4=1) (balanced : r<2*q) :
    q ≤ 3*(successful r q).card ∧ (r<q → 2*q ≤ 3*(successful r q).card) := by
  let h := r/2
  let k := q/2
  have hr : r=2*h+1 := by dsimp [h]; omega
  have hq : q=2*k+1 := by dsimp [k]; omega
  have odd : h%2=1 := by dsimp [h]; omega
  have even : k%2=0 := by dsimp [k]; omega
  let F := ((X^3-X)^h : (ZMod q)[X])
  have size : F.natDegree ≤ 3*h := by simpa [F] using cubic_degree (0:ZMod q) h
  have ct := mixed_count hr hq odd even (by omega) (by omega)
  change q ≤ _ + (hasseDeriv (2*h) F).natDegree at ct
  by_cases order : r<q
  · have b := PrimeFactors.HasseShiftDegree.degree_small_partner F size hr.symm order
    omega
  · have b := PrimeFactors.HasseShiftDegree.degree_large_partner F size hr.symm (by omega) balanced
    omega

/-- Number of successful shifts in a complete, product-only period. -/
def publicHits (n r : ℕ) :=
  Nat.card {c : Fin n // n.gcd (reading n (c.val:ℤ)).natAbs = r}

/-- Uniform shifts below the public input expose either prime orientation with
probability at least one third, and the smaller inert prime with probability
at least two thirds. Each gcd uses only the product and the shift. -/
theorem public_thirds {r q : ℕ} [Fact r.Prime] [Fact q.Prime]
    (inert : r%4=3) (split : q%4=1) (balanced : r<2*q) :
    r*q ≤ 3*publicHits (r*q) r ∧ (r<q → 2*(r*q) ≤ 3*publicHits (r*q) r) := by
  have hr : r=2*(r/2)+1 := by omega
  have hq : q=2*(q/2)+1 := by omega
  have iffC (c : ℤ) := readout_iff hr hq (by omega) (by omega) (by omega) c
  let P (v : ZMod q) := v ∈ successful r q
  have period := PrimeFactors.periodic_interval_lower_bound (Fact.out : q.Prime).pos P 0 (r*q)
  have res : Nat.card {v : ZMod q // P v} = (successful r q).card := by
    change Nat.card ↥(successful r q) = _
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have equiv' (c : Fin (r*q)) : P (((0+c.val : ℕ):ZMod q)) ↔
      (r*q).gcd (reading (r*q) (c.val:ℤ)).natAbs = r := by
    simp only [P, successful, Finset.mem_filter, Finset.mem_univ, true_and, zero_add, iffC,
      Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [res, Nat.mul_div_cancel _ (Fact.out : q.Prime).pos,
    Nat.card_congr (Equiv.subtypeEquivRight equiv')] at period
  change r*(successful r q).card ≤ publicHits (r*q) r at period
  have thirds := mixed_thirds inert split balanced
  constructor
  · have mult := Nat.mul_le_mul_left r thirds.1
    nlinarith only [mult,period]
  · intro ord
    have mult := Nat.mul_le_mul_left r (thirds.2 ord)
    nlinarith only [mult,period]

end PrimeFactors.TranslatedHasse
