import PrimeFactors.ExtensionTrace
import PrimeFactors.ThreeSquarePointDensity

/-! A binary circle modulo a product of two distinct odd primes and the
primitive integer sphere at that radius have proportional counts. Local
circle counts use only a finite-field character sum. The sphere comparison
uses the classical primitive representation formula as an explicit premise.
For the congruence counts see L. Tóth, *Counting Solutions of Quadratic
Congruences in Several Variables Revisited* (2014), Corollaries 6 and 35. -/
namespace PrimeFactors.SphereCircleIdentity

open Finset ThreeSquareRadiusCounts
open private PrimeFactors.ExtensionTrace.shifted_square from PrimeFactors.ExtensionTrace

/-- Ordered residue pairs representing a prescribed sum of two squares. -/
noncomputable def circle (F : Type*) [CommRing F] [Fintype F] [DecidableEq F] (t : F) :
    Finset (F×F) := univ.filter (fun w => w.1^2+w.2^2=t)

@[simp] theorem mem_circle {F : Type*} [CommRing F] [Fintype F] [DecidableEq F]
    {t : F} {w : F×F} : w∈circle F t ↔ w.1^2+w.2^2=t := by
  simp [circle]

/-- Binary circle counts over any finite field of odd characteristic,
including the exceptional target zero. -/
theorem field_count (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (odd : ringChar F≠2) (t : F) :
    ((circle F t).card : ℤ)=(Fintype.card F:ℤ)+quadraticChar F (-1)*
      ((if t=0 then (Fintype.card F:ℤ) else 0)-1) := by
  have fiber (x : F) : (∑ y : F, if x^2+y^2=t then (1:ℤ) else 0)=
      quadraticChar F (t-x^2)+1 := by
    have eq (y : F) : x^2+y^2=t ↔ y^2=t-x^2 :=
      ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
    simp_rw [eq,sum_boole]
    simpa only [Set.toFinset_setOf] using quadraticChar_card_sqrts odd (t-x^2)
  have flip (x : F) : t-x^2=(-1)*(x^2-t) := by ring
  simp only [circle,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    Fintype.sum_prod_type,fiber,sum_add_distrib,flip,map_mul,←mul_sum,
    PrimeFactors.ExtensionTrace.shifted_square odd,sum_const,card_univ,nsmul_eq_mul,mul_one]
  ring

/-- The local cardinality is independent of the nonzero target. -/
theorem prime_unit {p : ℕ} [Fact p.Prime] (odd : p≠2) (t : ZMod p) (nz : t≠0) :
    ((circle (ZMod p) t).card : ℤ)=(p:ℤ)-sign p := by
  have ch : ringChar (ZMod p)≠2 := by rwa [ZMod.ringChar_zmod_n]
  rw [field_count _ ch,if_neg nz,quadraticChar_neg_one ch,ZMod.card]
  obtain ⟨a,ha⟩ := (Fact.out : p.Prime).odd_of_ne_two odd
  by_cases cls : p%4=1
  · simp [sign, cls, ZMod.χ₄_nat_one_mod_four cls]
    ring
  · have other : p%4=3 := by omega
    simp [sign, cls, ZMod.χ₄_nat_three_mod_four other]

/-- Circle counts multiply under the ring CRT, for every target. -/
theorem circle_crt {m n : ℕ} [NeZero m] [NeZero n] (cop : m.Coprime n)
    (t : ZMod (m*n)) : (circle (ZMod (m*n)) t).card =
      (circle (ZMod m) ((ZMod.chineseRemainder cop t).1)).card *
      (circle (ZMod n) ((ZMod.chineseRemainder cop t).2)).card := by
  let e := ZMod.chineseRemainder cop
  let f := (e.toEquiv.prodCongr e.toEquiv).trans
    (Equiv.prodProdProdComm (ZMod m) (ZMod n) (ZMod m) (ZMod n))
  have eq : (circle (ZMod (m*n)) t).map f.toEmbedding =
      circle (ZMod m) (e t).1 ×ˢ circle (ZMod n) (e t).2 := by
    ext w
    obtain ⟨v,rfl⟩ := f.surjective w
    simp only [mem_map_equiv,Equiv.symm_apply_apply,mem_product,mem_circle]
    rw [←e.injective.eq_iff,map_add,map_pow,map_pow,Prod.ext_iff]
    rfl
  simpa only [card_map,card_product] using congrArg Finset.card eq

/-- All unit targets give the same count for a squarefree semiprime. -/
theorem semiprime {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ne : p≠q)
    (op : p≠2) (oq : q≠2) {t : ZMod (p*q)} (unit : IsUnit t) :
    ((circle (ZMod (p*q)) t).card : ℤ)=((p:ℤ)-sign p)*((q:ℤ)-sign q) := by
  have cop := (Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr ne
  let e := ZMod.chineseRemainder cop
  have lu : (e t).1≠0 := (unit.map ((RingHom.fst _ _).comp e.toRingHom)).ne_zero
  have ru : (e t).2≠0 := (unit.map ((RingHom.snd _ _).comp e.toRingHom)).ne_zero
  rw [circle_crt cop, Nat.cast_mul, prime_unit op _ lu, prime_unit oq _ ru]

/-- Six times the unit-target circle count is the signed, ordered count of
primitive integer sphere points. -/
theorem sphere_eq_six {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ne : p≠q)
    (op : p≠2) (oq : q≠2) {t : ZMod (p*q)} (unit : IsUnit t)
    (formula : GaussFormula p q) :
    count (p*q) true=6*(circle (ZMod (p*q)) t).card := by
  have h := semiprime ne op oq unit
  exact_mod_cast (show (count (p*q) true:ℤ)=6*((circle (ZMod (p*q)) t).card:ℤ) by
    rw [formula,h]; ring)

/-- Alternatively the total-sphere formula on odd radii supplies the
primitive count, so no separate primitive identity is needed. -/
theorem sphere_div_six {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ne : p≠q)
    (op : p≠2) (oq : q≠2) {t : ZMod (p*q)} (unit : IsUnit t)
    (formula : HurwitzFormula) :
    count (p*q) true / 6=(circle (ZMod (p*q)) t).card := by
  have pp : p.Prime := Fact.out
  have qp : q.Prime := Fact.out
  rw [sphere_eq_six ne op oq unit (ThreeSquarePointDensity.gauss_of_hurwitz formula
    pp qp ne (pp.odd_of_ne_two op) (qp.odd_of_ne_two oq))]
  omega

/-- At radius 15, direct counts at two units agree and the singular
target zero gives a different count. -/
theorem fifteen : (circle (ZMod 15) 1).card=16 ∧ (circle (ZMod 15) 2).card=16 ∧
    (circle (ZMod 15) 0).card=9 ∧ count 15 true=96 := by
  refine ⟨?_,?_,?_,toy_fifteen.2⟩ <;> decide +kernel

end PrimeFactors.SphereCircleIdentity
