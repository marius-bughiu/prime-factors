import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic.Ring

/-! A second digit of a band product can recover the factor sum when the product itself
vanishes modulo the semiprime. Both observations are values of the same block polynomial.
The band must contain the factors themselves once each, with no other nonunit entries. -/

namespace PrimeFactors.DivisorProductDerivative

/-- First derivative of the product when the factor at entry z has velocity g(z). -/
noncomputable def tagged (g : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | z :: rest => g z * rest.prod + z * tagged g rest

theorem tagged_perm (g : ℕ → ℕ) {xs ys : List ℕ} (h : xs.Perm ys) :
    tagged g xs = tagged g ys := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [tagged, h.prod_eq, ih]
  | swap a b xs => simp [tagged]; ring
  | trans _ _ ih ij => exact ih.trans ij

/-- A polynomial-type tag g(z)=c+z*h(z) supplies only the ordinary derivative modulo
the product. The identity also exhibits exactly what is lost on reduction. -/
theorem affine_tag (c : ℕ) (h : ℕ → ℕ) (xs : List ℕ) :
    tagged (fun z => c+z*h z) xs =
      c * tagged (fun _ => 1) xs + xs.prod * (xs.map h).sum := by
  induction xs with
  | nil => simp [tagged]
  | cons z xs ih => simp [tagged, ih]; ring

/-- The tagged derivative records the two exceptional tags with the opposite factors
as coefficients. Every other summand is a multiple of the original product p*q. -/
theorem two_tags {p q : ℕ} {xs rest : List ℕ} (h : xs.Perm (p :: q :: rest))
    (g : ℕ → ℕ) :
    tagged g xs = (g p * q + g q * p) * rest.prod + (p*q)*tagged g rest := by
  rw [tagged_perm g h]
  simp [tagged]
  ring

/-- The base-n digit at place one of the canonical residue modulo n². -/
def digit (n a : ℕ) : ℕ := (a % n^2) / n

theorem digit_mul {n : ℕ} (hn : 0<n) (c : ℕ) : digit n (n*c) = c%n := by
  simp [digit, pow_two, Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ hn]

/-- All translations by n preserve the product modulo n. -/
theorem translated_cast (xs : List ℕ) (n a : ℕ) :
    (((xs.map (· + a*n)).prod : ℕ) : ZMod n) = (xs.prod : ZMod n) := by
  induction xs with
  | nil => simp
  | cons z xs ih => simp [ih]

/-- With both prime factors in the block, every second-digit observation at a
multiple of n lies on the same affine line. Its intercept is the remaining unit C
and its slope is C*(p+q). Arbitrarily many such translations carry no extra coordinate. -/
theorem digit_line {p q : ℕ} {xs rest : List ℕ}
    (h : xs.Perm (p :: q :: rest)) (hn : 0<p*q) (a : ℕ) :
    let n := p*q
    ((digit n (xs.map (· + a*n)).prod : ℕ) : ZMod n) =
      (1 + (a : ZMod n)*(p+q))*(rest.prod : ZMod n) := by
  let n := p*q
  change ((digit n (xs.map (· + a*n)).prod : ℕ) : ZMod n) = _
  have shifted : (xs.map (· + a*n)).prod =
      n * (((1+a*q)*(1+a*p))*(rest.map (· + a*n)).prod) := by
    rw [(h.map _).prod_eq]
    simp [n]
    ring
  have hz : (p : ZMod n)*q=0 := by
    rw [← Nat.cast_mul]; exact ZMod.natCast_self n
  rw [shifted, digit_mul hn, ZMod.natCast_mod]
  push_cast
  rw [translated_cast]
  congr 1
  calc
    _ = 1+(a:ZMod n)*(p+q)+a^2*((p:ZMod n)*q) := by ring
    _ = _ := by rw [hz]; ring

/-- The two second-digit measurements are computable before knowing which entries are
the factors. The difference removes the common unit and gives the actual sum. -/
noncomputable def readSum (n a b : ℕ) : ℕ :=
  (((digit n b : ℕ) : ZMod n) * (((digit n a : ℕ) : ZMod n))⁻¹ - 1).val

theorem readSum_of_perm {p q : ℕ} {xs rest : List ℕ}
    (h : xs.Perm (p :: q :: rest)) (hn : 0<p*q)
    (unit : rest.prod.Coprime (p*q)) (bound : p+q < p*q) :
    readSum (p*q) xs.prod (xs.map (· + p*q)).prod = p+q := by
  let n := p*q
  have hprod : xs.prod = n*rest.prod := by rw [h.prod_eq]; simp [n, Nat.mul_assoc]
  have line := digit_line h hn 1
  simp only [one_mul, Nat.cast_one] at line
  unfold readSum
  rw [line, hprod, digit_mul hn, ZMod.natCast_mod, mul_assoc, ZMod.coe_mul_inv_eq_one _ unit,
    mul_one, add_sub_cancel_left, ← Nat.cast_add, ZMod.val_natCast_of_lt bound]

/-- The theorem applies to any publicly listed band containing both primes, without using
their positions. The upper bounds prevent another multiple of either prime. -/
theorem readSum_of_band {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ne : p ≠ q)
    {xs : List ℕ} (nd : xs.Nodup) (ip : p ∈ xs) (iq : q ∈ xs)
    (band : ∀ z ∈ xs, 0 < z ∧ z < 2*p ∧ z < 2*q) (bound : p+q<p*q) :
    readSum (p*q) xs.prod (xs.map (· + p*q)).prod = p+q := by
  have iq' := (List.mem_erase_of_ne ne.symm).mpr iq
  let rest := (xs.erase p).erase q
  have perm : xs.Perm (p :: q :: rest) :=
    (List.perm_cons_erase ip).trans ((List.perm_cons_erase iq').cons p)
  have each : ∀ z ∈ rest, z.Coprime (p*q) := by
    intro z iz
    have iz' := List.mem_of_mem_erase iz
    obtain ⟨pos, zp, zq⟩ := band z (List.mem_of_mem_erase iz')
    have np : z ≠ p := fun e => nd.not_mem_erase (e ▸ iz')
    have nq : z ≠ q := fun e => (nd.erase p).not_mem_erase (e ▸ iz)
    exact ((hp.coprime_iff_not_dvd.mpr fun d =>
      np (Nat.eq_of_dvd_of_lt_two_mul pos.ne' d zp)).symm).mul_right
      (hq.coprime_iff_not_dvd.mpr fun d => nq (Nat.eq_of_dvd_of_lt_two_mul pos.ne' d zq)).symm
  have unit : rest.prod.Coprime (p*q) := by
    suffices ∀ l : List ℕ, (∀ z ∈ l, z.Coprime (p*q)) → l.prod.Coprime (p*q) from
      this rest each
    intro l
    induction l with
    | nil => simp
    | cons z l ih =>
      intro all
      rw [List.prod_cons, Nat.coprime_mul_iff_left]
      exact ⟨all z (by simp), ih (fun w hw => all w (List.mem_cons_of_mem _ hw))⟩
  exact readSum_of_perm perm (Nat.mul_pos hp.pos hq.pos) unit bound

/-- A reciprocal lookup in an independently chosen modulus. Both true factors get
the *same* least nonnegative tag, equal to the sum modulo that modulus. -/
noncomputable def periodicTag (m n z : ℕ) : ℕ :=
  ((z : ZMod m) + (n : ZMod m)*(z : ZMod m)⁻¹).val

theorem periodicTag_at_factor {p q m : ℕ} (unit : p.Coprime m) :
    periodicTag m (p*q) p = (p+q)%m := by
  unfold periodicTag
  push_cast
  rw [mul_comm (p : ZMod m) q, mul_assoc, ZMod.coe_mul_inv_eq_one _ unit, mul_one,
    ← Nat.cast_add, ZMod.val_natCast]

/-- A common tag at the two exceptional entries is read exactly by one modular
division. The product and ordinary derivative can both fail to split the input by gcd. -/
theorem common_tag_readout {p q a : ℕ} {xs rest : List ℕ}
    (h : xs.Perm (p :: q :: rest)) (g : ℕ → ℕ) (gp : g p=a) (gq : g q=a)
    (unit : rest.prod.Coprime (p*q)) (pq : p.Coprime q) (bound : a<p*q) :
    (((tagged g xs : ℕ) : ZMod (p*q)) *
      (((tagged (fun _ => 1) xs : ℕ) : ZMod (p*q)))⁻¹).val = a := by
  let n := p*q
  have cast_zero : (p : ZMod n)*q=0 := by
    rw [← Nat.cast_mul]; exact ZMod.natCast_self n
  have ordinary : (tagged (fun _ => 1) xs : ZMod n) =
      ((p+q : ℕ) : ZMod n)*(rest.prod : ZMod n) := by
    rw [two_tags h]
    push_cast
    rw [cast_zero]
    ring
  have weighted : (tagged g xs : ZMod n) = (a : ZMod n) * (tagged (fun _ => 1) xs : ZMod n) := by
    rw [ordinary, two_tags h, gp, gq]
    push_cast
    rw [cast_zero]
    ring
  have sp : (p+q).Coprime p := by simpa [Nat.add_comm p q] using
    (Nat.coprime_add_self_left.mpr pq.symm)
  have sq : (p+q).Coprime q := Nat.coprime_add_self_left.mpr pq
  have su : IsUnit (((p+q : ℕ) : ZMod n)) := (ZMod.isUnit_iff_coprime _ _).mpr (sp.mul_right sq)
  have cu : IsUnit (rest.prod : ZMod n) := (ZMod.isUnit_iff_coprime _ _).mpr unit
  have du : IsUnit (tagged (fun _ => 1) xs : ZMod n) := ordinary ▸ su.mul cu
  change (((tagged g xs : ℕ) : ZMod n) * (((tagged (fun _ => 1) xs : ℕ) : ZMod n))⁻¹).val=a
  rw [weighted, mul_assoc, ZMod.mul_inv_of_unit _ du, mul_one, ZMod.val_natCast_of_lt bound]

theorem periodic_readout {p q m : ℕ} {xs rest : List ℕ}
    (h : xs.Perm (p :: q :: rest)) (unit : rest.prod.Coprime (p*q)) (pq : p.Coprime q)
    (pm : p.Coprime m) (qm : q.Coprime m) (hm : 0<m) (limit : m≤p*q) :
    (((tagged (periodicTag m (p*q)) xs : ℕ) : ZMod (p*q)) *
      (((tagged (fun _ => 1) xs : ℕ) : ZMod (p*q)))⁻¹).val = (p+q)%m := by
  apply common_tag_readout h _ (periodicTag_at_factor pm) _ unit pq
    ((Nat.mod_lt _ hm).trans_le limit)
  simpa [Nat.mul_comm q p, Nat.add_comm q p] using periodicTag_at_factor (q := p) qm

/-- On this full four-entry odd band the product gcd is all of 143, and the untagged
derivative gcd is 1. Both second digits can be checked on a calculator. -/
theorem band_143 :
    let xs := [9,11,13,15]
    Nat.gcd xs.prod 143 = 143 ∧ Nat.gcd (tagged (fun _ => 1) xs) 143 = 1 ∧
    digit 143 xs.prod = 135 ∧ digit 143 (xs.map (· + 143)).prod = 86 ∧
    readSum 143 xs.prod (xs.map (· + 143)).prod = 24 ∧
    Nat.Prime 11 ∧ Nat.Prime 13 ∧ 11*13=143 := by
  dsimp only
  refine ⟨by decide, by decide, by decide, by decide, ?_, by decide, by decide, rfl⟩
  apply readSum_of_band (p:=11) (q:=13) <;> decide

end PrimeFactors.DivisorProductDerivative
