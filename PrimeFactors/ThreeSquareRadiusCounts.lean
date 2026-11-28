import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-! Counts of signed, ordered three-square representations of an odd radius
squared. The classical Hurwitz and Gauss formulas appear as explicit premises.
Their use here does not supply a fast way to evaluate a primitive count. -/
namespace PrimeFactors.ThreeSquareRadiusCounts

open Finset

private def signs (x : ℕ) : ℕ := if x=0 then 1 else 2

/-- Count the signs of all triples with first coordinates of magnitudes x
and y. A nonnegative third magnitude, when it exists, is unique. -/
private noncomputable def slice (r x y : ℕ) (prim : Bool) : ℕ :=
  let z := (r^2-x^2-y^2).sqrt
  if x^2+y^2+z^2=r^2 ∧ (prim=true → (x.gcd y).gcd z=1)
  then signs x * signs y * signs z else 0

/-- Zeros are included and permutations count separately. The primitive
count retains exactly those triples whose three coordinates are coprime. -/
noncomputable def count (r : ℕ) (prim : Bool) : ℕ :=
  ∑ x∈range (r+1), ∑ y∈range (r+1), slice r x y prim

/-- The character of −1 on an odd prime. -/
def sign (p : ℕ) : ℤ := if p%4=1 then 1 else -1

/-- The local factor at exponent e in the Hurwitz formula, expressed as
p^e+(1−χ(p))(1+p+...+p^(e−1)). -/
noncomputable def localFactor (p e : ℕ) : ℤ :=
  (p:ℤ)^e+(1-sign p)*(∑ i∈range e, (p:ℤ)^i)

noncomputable def eulerProduct (r : ℕ) : ℤ :=
  ∏ p∈r.primeFactors, localFactor p (r.factorization p)

/-- Hürlimann, *Exact and Asymptotic Evaluation of the Number of Distinct
Primitive Cuboids*, Theorem 2
for odd radii. This statement is an input to the general raw-count results. -/
def HurwitzFormula : Prop :=
  ∀ r : ℕ, Odd r → (count r false : ℤ)=6*eulerProduct r

/-- Gauss's primitive count at the square of a product of distinct odd primes.
See Hürlimann, equation (2), or Cooper–Hirschhorn, equation (1.19). -/
def GaussFormula (p q : ℕ) : Prop :=
  (count (p*q) true : ℤ)=6*((p:ℤ)-sign p)*((q:ℤ)-sign q)

private theorem euler_mul {a b : ℕ} (ha : a≠0) (hb : b≠0) (cop : a.Coprime b) :
    eulerProduct (a*b)=eulerProduct a*eulerProduct b := by
  unfold eulerProduct
  rw [Nat.primeFactors_mul ha hb,prod_union cop.disjoint_primeFactors]
  congr 1
  · apply prod_congr rfl
    intro p hp
    have miss : p∉b.primeFactors := fun h => disjoint_left.mp cop.disjoint_primeFactors hp h
    have zero : b.factorization p=0 := by simpa [←Nat.support_factorization] using miss
    rw [Nat.factorization_mul ha hb,Finsupp.add_apply,zero,add_zero]
  · apply prod_congr rfl
    intro p hp
    have miss : p∉a.primeFactors := fun h => disjoint_left.mp cop.disjoint_primeFactors h hp
    have zero : a.factorization p=0 := by simpa [←Nat.support_factorization] using miss
    rw [Nat.factorization_mul ha hb,Finsupp.add_apply,zero,zero_add]

private theorem euler_prime {p : ℕ} (pp : p.Prime) :
    eulerProduct p=(p:ℤ)+1-sign p := by
  simp [eulerProduct,pp.primeFactors,pp.factorization_self,localFactor]
  ring

theorem semiprime_total (formula : HurwitzFormula) {p q : ℕ} (pp : p.Prime)
    (qp : q.Prime) (ne : p≠q) (op : Odd p) (oq : Odd q) :
    (count (p*q) false : ℤ)=6*((p:ℤ)+1-sign p)*((q:ℤ)+1-sign q) := by
  rw [formula _ (op.mul oq),euler_mul pp.ne_zero qp.ne_zero ((Nat.coprime_primes pp qp).mpr ne),
    euler_prime pp,euler_prime qp]
  ring

/-- Every unfiltered readout at an odd coprime dilation is proportional
to the initial readout, including when the multiplier has repeated primes. -/
theorem dilation (formula : HurwitzFormula) {m N : ℕ} (mo : Odd m) (no : Odd N)
    (cop : m.Coprime N) :
    (6:ℤ)*count (m*N) false=(count m false : ℤ)*count N false := by
  rw [formula _ (mo.mul no),formula _ mo,formula _ no,euler_mul (by obtain ⟨k,hk⟩ := mo; omega) (by obtain ⟨k,hk⟩ := no; omega) cop]
  ring

/-- Multiplying by a prime congruent to one modulo four multiplies the
unfiltered count by that prime, including at a radius it already divides. -/
theorem split_prime {m p : ℕ} (formula : HurwitzFormula) (pp : p.Prime)
    (sp : p%4=1) (mo : Odd m) : count (m*p) false=p*count m false := by
  have po : Odd p := Nat.odd_iff.mpr (by omega)
  have m0 : m≠0 := by obtain ⟨u,hu⟩ := mo; omega
  have step (a : ℕ) : localFactor a ((m*p).factorization a) =
      localFactor a (m.factorization a) * (if a=p then (p:ℤ) else 1) := by
    rw [Nat.factorization_mul m0 pp.ne_zero,Finsupp.add_apply,pp.factorization]
    by_cases same : a=p
    · subst a
      simp [sign,localFactor,sp,pow_succ]
    · simp [Finsupp.single_apply,same,Ne.symm same]
  have co : eulerProduct (m*p) = eulerProduct m*(p:ℤ) := by
    by_cases already : p∈m.primeFactors
    · unfold eulerProduct
      rw [Nat.primeFactors_mul m0 pp.ne_zero,pp.primeFactors,
        union_eq_left.mpr (singleton_subset_iff.mpr already)]
      simp_rw [step]
      rw [prod_mul_distrib]
      simp [already]
    · have cop : m.Coprime p := (pp.coprime_iff_not_dvd.mpr (by
        intro div; exact already ((Nat.mem_primeFactors_of_ne_zero m0).mpr ⟨pp,div⟩))).symm
      rw [euler_mul m0 pp.ne_zero cop,euler_prime pp,sign,if_pos sp,add_sub_cancel_right]
  exact_mod_cast (show (count (m*p) false : ℤ)=(p:ℤ)*count m false by
    rw [formula _ (mo.mul po),formula _ mo,co]; ring)

/-- For any odd multiplier, the unfiltered count reports a known multiple
of the multiplier's own count when both primes are one modulo four. -/
theorem blind {m p q : ℕ} (formula : HurwitzFormula) (pp : p.Prime) (qp : q.Prime)
    (sp : p%4=1) (sq : q%4=1) (mo : Odd m) :
    count (m*(p*q)) false=(p*q)*count m false := by
  have op : Odd p := Nat.odd_iff.mpr (by omega)
  rw [←Nat.mul_assoc,split_prime formula qp sq (mo.mul op),split_prime formula pp sp mo]
  ring

private theorem sign_cases {p : ℕ} (op : Odd p) : p%4=1 ∨ p%4=3 := by
  obtain ⟨k,hk⟩ := op
  omega

/-- Absolute distance from the public center reads either the sum or the
nonnegative difference of the two factors from the primitive count. -/
theorem signed_recovery {p q : ℕ} (ord : p≤q) (op : Odd p) (oq : Odd q)
    (formula : GaussFormula p q) :
    |(count (p*q) true : ℤ)/6 - ((p*q:ℕ):ℤ) - (if (p*q)%4=1 then 1 else -1)| =
      if (p*q)%4=1 then (p:ℤ)+q else (q:ℤ)-p := by
  have cnt : (count (p*q) true : ℤ)/6=((p:ℤ)-sign p)*((q:ℤ)-sign q) := by
    rw [formula]
    ring_nf
    omega
  rw [cnt,Nat.cast_mul]
  have ord' : (p:ℤ)≤q := by exact_mod_cast ord
  rcases sign_cases op with hp|hp <;> rcases sign_cases oq with hq|hq <;>
    simp [Nat.mul_mod,sign,hp,hq] <;>
    first | (rw [abs_of_nonneg (by nlinarith)]; ring) | (rw [abs_of_nonpos (by nlinarith)]; ring)

private theorem four_dvd {p : ℕ} (op : Odd p) : (4:ℤ)∣(p:ℤ)-sign p := by
  rcases sign_cases op with hp|hp <;> simp [sign,hp] <;> omega

/-- In particular an error below twelve is safe. The factor of sixteen
in the normalized primitive count allows rounding throughout the larger
open interval of radius forty-eight. -/
theorem rounded {p q : ℕ} (op : Odd p) (oq : Odd q) (formula : GaussFormula p q)
    (v : ℤ) (error : |v-(count (p*q) true : ℤ)|<48) :
    96*((v+48)/96)=(count (p*q) true : ℤ) := by
  obtain ⟨a,ha⟩ := four_dvd op
  obtain ⟨b,hb⟩ := four_dvd oq
  have grid : (count (p*q) true : ℤ)=96*(a*b) := by
    rw [formula,ha,hb]; ring
  rw [grid] at error ⊢
  rw [abs_lt] at error
  omega

/-- At radius fifteen the values come directly from the coordinates. -/
theorem toy_fifteen : count 15 false=150 ∧ count 15 true=96 := by decide +kernel

-- Executable census of total and primitive points. These numerical checks
-- enumerate the coordinates independently of both classical formulas.
#guard Id.run do
  for (r,raw,primitive) in [(65,390,288),(77,702,576),(91,702,576)] do
    let mut total := 0
    let mut visible := 0
    for x in [:r+1] do
      for y in [:r+1] do
        let z := (r*r-x*x-y*y).sqrt
        if x*x+y*y+z*z == r*r then
          let w := signs x * signs y * signs z
          total := total+w
          if (x.gcd y).gcd z == 1 then visible := visible+w
    if (total,visible) != (raw,primitive) then return false
  return true

end PrimeFactors.ThreeSquareRadiusCounts
