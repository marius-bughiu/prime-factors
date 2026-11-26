import PrimeFactors.CharacterColumnSpan
import PrimeFactors.FoldedFactorial
import Mathlib.Algebra.Polynomial.Monic

/-! A fixed wheel period and a Jacobi selector determine which offsets can
be paired inside a single block. This involution differs from pairing two
whole blocks across the midpoint of a longer interval. -/
namespace PrimeFactors.CharacterColumnReflection

open Finset Polynomial
open scoped Polynomial

/-- The denominator class −1 has positive symbol for a positive numerator.
We use supplementary reciprocity at 2 and ordinary reciprocity for the
odd part. The modulus can have additional wheel factors. -/
theorem positive_at_last (d P : ℕ) (dp : 0<d) (pp : 0<P) (period : 4*d∣P) :
    jacobiSym (d:ℤ) (P-1)=1 := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    have four : 4∣P := (dvd_mul_right 4 d).trans period
    have last4 : (P-1)%4=3 := by omega
    have odd : Odd (P-1) := Nat.odd_iff.mpr (by omega)
    rcases Nat.even_or_odd' d with ⟨k,hk|hk⟩
    · have kd : 0<k := by omega
      have dk : d=2*k := by omega
      have halve : 4*k ∣ P := (show 4*k∣4*d by rw [dk]; exact ⟨2,by ring⟩).trans period
      have eight : 8∣P := (show 8∣4*d by rw [dk]; exact ⟨k,by ring⟩).trans period
      rw [dk,Nat.cast_mul,Nat.cast_ofNat,jacobiSym.mul_left,ih k (by omega) kd halve,
        mul_one,jacobiSym.at_two odd,ZMod.χ₈_nat_mod_eight,show (P-1)%8=7 by omega]
      decide
    · have do' : Odd d := Nat.odd_iff.mpr (by omega)
      have dm := (dvd_mul_left d 4).trans period
      have cast : ((P-1 : ℕ):ℤ)=(P:ℤ)-1 := by rw [Nat.cast_sub pp]; rfl
      have modEq : Int.ModEq (d:ℤ) ((P-1 : ℕ):ℤ) (-1) := by
        apply Int.modEq_iff_dvd.mpr
        rw [cast]
        rw [show -1-((P:ℤ)-1)= -(P:ℤ) by ring]
        exact Int.dvd_neg.mpr (Int.natCast_dvd_natCast.mpr dm)
      have flip := jacobiSym.mod_left' modEq
      rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp do') with one|three
      · rw [jacobiSym.quadratic_reciprocity_one_mod_four one odd,flip,jacobiSym.at_neg_one do',
          ZMod.χ₄_nat_one_mod_four one]
      · rw [jacobiSym.quadratic_reciprocity_three_mod_four three last4,flip,
          jacobiSym.at_neg_one do',ZMod.χ₄_nat_three_mod_four three,neg_neg]

/-- For signed d the classification is exactly its ordinary real sign. -/
theorem at_last {d : ℤ} {P : ℕ} (dn : d≠0) (pp : 0<P) (period : 4*d.natAbs∣P) :
    jacobiSym d (P-1)=if 0<d then 1 else -1 := by
  have pos := positive_at_last d.natAbs P (Int.natAbs_pos.mpr dn) pp period
  rcases Int.natAbs_eq d with plus|minus
  · rw [if_pos (by omega)]
    exact plus ▸ pos
  · rw [if_neg (by omega),minus]
    have four : 4∣P := (dvd_mul_right 4 _).trans period
    have odd : Odd (P-1) := Nat.odd_iff.mpr (by omega)
    rw [jacobiSym.neg _ odd,pos,ZMod.χ₄_nat_three_mod_four (by omega),mul_one]

/-- A natural-number representative of reflection, with 0 and P excluded. -/
theorem reflect {d : ℤ} {P a : ℕ} (dn : d≠0) (pp : 0<P) (period : 4*d.natAbs∣P)
    (ap : 0<a) (al : a<P) (odd : Odd a) :
    jacobiSym d (P-a)=(if 0<d then 1 else -1)*jacobiSym d a := by
  have four : 4∣P := (dvd_mul_right 4 _).trans period
  have ao := Nat.odd_iff.mp odd
  have lo : Odd (P-1) := Nat.odd_iff.mpr (by omega)
  have ro : Odd (P-a) := Nat.odd_iff.mpr (by omega)
  have m : Nat.ModEq P (P-a) ((P-1)*a) := by
    apply Nat.modEq_iff_dvd.mpr
    refine ⟨(a:ℤ)-1,?_⟩
    push_cast [Nat.cast_sub pp,Nat.cast_sub al.le]
    ring
  rw [CharacterDivisorColumn.periodic ro (lo.mul odd) d (m.of_dvd period),
    jacobiSym.mul_right' _ lo.pos.ne' ap.ne',at_last dn pp period]

/-- Positive selectors preserve the same sign and negative selectors switch
it under zero-centered residue reflection. -/
theorem mirror_mem {P a : ℕ} {d ε : ℤ} (dn : d≠0) (pp : 0<P) (period : 4*d.natAbs∣P)
    (inSet : a∈CharacterColumnSpan.signed P d ε) :
    P-a ∈ CharacterColumnSpan.signed P d ((if 0<d then 1 else -1)*ε) := by
  obtain ⟨ha,sign⟩ := mem_filter.mp inSet
  obtain ⟨range,unit⟩ := mem_filter.mp ha
  have al := mem_range.mp range
  have two : 2∣P := (dvd_mul_of_dvd_left (by decide : 2∣4) _).trans period
  have odd := (unit.of_dvd_right two).odd_of_right
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by have := odd.pos; omega),
    (Nat.coprime_self_sub_left al.le).mpr unit⟩,
    by rw [reflect dn pp period odd.pos al odd,sign]⟩

/-- With cyclic residues there may be several possible axes. Fixing one
member a₀ restricts the proposals to a₀+b for b in the mask. Each proposed
axis is checked by one membership lookup per residue. -/
noncomputable def cyclicAxes {P : ℕ} (S : Finset (ZMod P)) (a₀ : ZMod P) : Finset (ZMod P) :=
  (S.image (a₀+·)).filter fun c => ∀ a∈S,c-a∈S

theorem cyclic_axis_iff {P : ℕ} {S : Finset (ZMod P)} {a₀ c : ZMod P} (start : a₀∈S) :
    c∈cyclicAxes S a₀ ↔ S.image (c-·)=S := by
  constructor
  · intro h
    have closed := (mem_filter.mp h).2
    ext a
    constructor
    · rintro ha
      obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
      exact closed b hb
    · intro ha
      exact mem_image.mpr ⟨c-a,closed a ha,by abel⟩
  · intro eq
    have closed (a : ZMod P) (ha : a∈S) : c-a∈S := by
      rw [←eq]
      exact mem_image.mpr ⟨a,ha,rfl⟩
    exact mem_filter.mpr ⟨mem_image.mpr ⟨c-a₀,closed a₀ start,by abel⟩,closed⟩

theorem cyclic_axis_count {P : ℕ} (S : Finset (ZMod P)) (a₀ : ZMod P) :
    (cyclicAxes S a₀).card≤S.card := (card_filter_le ..).trans card_image_le

/-- In a fixed set of integer representatives, the axis is forced by its
endpoints. Checking this single reflected list is an exact affine test,
also when the standard axis P swaps the signs. -/
theorem axis_iff {S : Finset ℕ} (ne : S.Nonempty) :
    (∃ c : ℕ, (∀ a∈S,a≤c) ∧ ∀ a∈S,c-a∈S) ↔
      ∀ a∈S,S.min' ne+S.max' ne-a∈S := by
  have lo := S.min'_mem ne
  have hi := S.max'_mem ne
  constructor
  · rintro ⟨c,bound,closed⟩
    have L := S.min'_le _ (closed _ hi)
    have H := S.le_max' _ (closed _ lo)
    have h₁ := bound _ lo
    have h₂ := bound _ hi
    have forced : c=S.min' ne+S.max' ne := by omega
    simpa [forced] using closed
  · intro closed
    exact ⟨_,fun a ha => by have := S.le_max' _ ha; omega,closed⟩

/-- A fixed integral offset set can be folded about any C for which all
partners C−a occur. The strict lower half contains one of each paired
offset. The pairing theorem below assumes the midpoint is absent. -/
noncomputable def left (S : Finset ℕ) (c : ℕ) := S.filter fun a => 2*a<c

noncomputable def packed (R : Type*) [CommRing R] (S : Finset ℕ) (c : ℕ) : R[X] :=
  ∏ a ∈ left S c, (X+C ((a:R)*((c-a:ℕ):R)))

private theorem mirror_inj {S : Finset ℕ} {c : ℕ} (bounds : ∀ a∈S,a≤c) :
    Set.InjOn (c-·) (left S c : Set ℕ) := by
  intro a ha b hb eq
  have al := bounds a (mem_filter.mp ha).1
  have bl := bounds b (mem_filter.mp hb).1
  change c-a=c-b at eq
  omega

private theorem parts {S : Finset ℕ} {c : ℕ} (bounds : ∀ a∈S,a≤c)
    (symm : ∀ a∈S,c-a∈S) :
    (left S c).image (c-·) = S.filter (fun a => c<2*a) := by
  ext a
  constructor
  · rintro ha
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
    obtain ⟨bS,bl⟩ := mem_filter.mp hb
    have := bounds b bS
    exact mem_filter.mpr ⟨symm b bS,by omega⟩
  · intro ha
    obtain ⟨aS,al⟩ := mem_filter.mp ha
    have := bounds a aS
    exact mem_image.mpr ⟨c-a,mem_filter.mpr ⟨symm a aS,by omega⟩,by omega⟩

private theorem partition {S : Finset ℕ} {c : ℕ} (bounds : ∀ a∈S,a≤c)
    (symm : ∀ a∈S,c-a∈S) (noMid : ∀ a∈S,2*a≠c) :
    left S c ∪ (left S c).image (c-·) = S ∧ Disjoint (left S c) ((left S c).image (c-·)) := by
  rw [parts bounds symm]
  constructor
  · ext a
    by_cases ha : a∈S
    · have := noMid a ha
      simp only [left,mem_union,mem_filter,ha,true_and,iff_true]
      omega
    · simp [left,ha]
  · apply disjoint_left.mpr
    intro a lo hi
    exact (Nat.lt_asymm (mem_filter.mp lo).2) (mem_filter.mp hi).2

theorem paired_degree {R : Type*} [CommRing R] [Nontrivial R] {S : Finset ℕ} {c : ℕ}
    (bounds : ∀ a∈S,a≤c) (symm : ∀ a∈S,c-a∈S) (noMid : ∀ a∈S,2*a≠c) :
    2*(packed R S c).natDegree=S.card := by
  have deg : (packed R S c).natDegree=(left S c).card := by
    unfold packed
    rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)]
    simp only [natDegree_X_add_C,sum_const,smul_eq_mul,mul_one]
  obtain ⟨eq,disj⟩ := partition bounds symm noMid
  have cnt := card_union_of_disjoint disj
  rw [eq,card_image_of_injOn (mirror_inj bounds)] at cnt
  omega

theorem paired_eval {R : Type*} [CommRing R] {S : Finset ℕ} {c : ℕ}
    (bounds : ∀ a∈S,a≤c) (symm : ∀ a∈S,c-a∈S) (noMid : ∀ a∈S,2*a≠c) (x : R) :
    (packed R S c).eval (x*(x+c))=∏ a ∈ S,(x+(a:R)) := by
  obtain ⟨eq,disj⟩ := partition bounds symm noMid
  calc
    _ = ∏ a ∈ left S c,(x+(a:R))*(x+((c-a:ℕ):R)) := by
      rw [packed,eval_prod]
      apply prod_congr rfl
      intro a ha
      have le := bounds a (mem_filter.mp ha).1
      simp only [eval_add,eval_X,eval_C,Nat.cast_sub le]
      ring
    _ = (∏ a ∈ left S c,(x+(a:R))) * (∏ a ∈ (left S c).image (c-·),(x+(a:R))) := by
      rw [prod_mul_distrib,prod_image (mirror_inj bounds)]
    _ = _ := by rw [←prod_union disj, eq]

/-- With a fixed midpoint one linear factor is left outside the paired
polynomial. This covers the single-offset case as well. -/
theorem midpoint_eval {R : Type*} [CommRing R] {S : Finset ℕ} {m : ℕ}
    (bounds : ∀ a∈S,a≤2*m) (symm : ∀ a∈S,2*m-a∈S) (mid : m∈S) (x : R) :
    (packed R (S.erase m) (2*m)).eval (x*(x+(2*m:ℕ))) * (x+(m:R))=
      ∏ a ∈ S,(x+(a:R)) := by
  have bound (a : ℕ) (ha : a∈S.erase m) := bounds a (mem_of_mem_erase ha)
  have closed (a : ℕ) (ha : a∈S.erase m) : 2*m-a∈S.erase m := by
    obtain ⟨ne,h⟩ := mem_erase.mp ha
    have := bounds a h
    exact mem_erase.mpr ⟨by omega,symm a h⟩
  have absent (a : ℕ) (ha : a∈S.erase m) : 2*a≠2*m := by have := (mem_erase.mp ha).1; omega
  rw [paired_eval bound closed absent,prod_erase_mul S _ mid]

/-- Node differences factor into two linear terms on the shifted quadratic
grid, over any commutative ring. An evaluator still needs their inverses
or needs to handle a nonunit. -/
theorem node_difference {R : Type*} [CommRing R] (b h c j i : R) :
    (b+h*j)*(b+h*j+c)-(b+h*i)*(b+h*i+c)=h*(j-i)*(2*b+h*(j+i)+c) := by ring

/-- The actual selected Jacobi residues supply all the hypotheses needed
for the new single-block folded polynomial, with no midpoint correction. -/
theorem positive_block {R : Type*} [CommRing R] [Nontrivial R] {P : ℕ} {d ε : ℤ}
    (pos : 0<d) (pp : 0<P) (period : 4*d.natAbs∣P) (x : R) :
    let S := CharacterColumnSpan.signed P d ε
    (packed R S P).eval (x*(x+P))=∏ a ∈ S,(x+(a:R)) ∧
      2*(packed R S P).natDegree=S.card := by
  let S := CharacterColumnSpan.signed P d ε
  have bounds (a : ℕ) (ha : a∈S) : a≤P :=
    (mem_range.mp (mem_filter.mp (mem_filter.mp ha).1).1).le
  have symm (a : ℕ) (ha : a∈S) : P-a∈S := by
    simpa only [if_pos pos,one_mul] using mirror_mem pos.ne' pp period ha
  have four : 4∣P := (dvd_mul_right 4 _).trans period
  have noMid (a : ℕ) (ha : a∈S) : 2*a≠P := by
    have unit := (mem_filter.mp (mem_filter.mp ha).1).2
    have odd := Nat.odd_iff.mp ((unit.of_dvd_right ((by decide : 2∣4).trans four)).odd_of_right)
    omega
  exact ⟨paired_eval bounds symm noMid x,paired_degree bounds symm noMid⟩

/-- For a positive separating selector the degree is exactly a quarter
of the shared wheel's number of unit residues. The variable is x(x+P).
This counts polynomial coefficients by degree, independently of how any
interpolation or product evaluation is implemented. -/
theorem degree_quarter {R : Type*} [CommRing R] [Nontrivial R] {P n : ℕ} {d ε : ℤ}
    (pos : 0<d) (pp : 0<P) (period : 4*d.natAbs∣P) (wheel : n.Coprime P)
    (select : jacobiSym d n= -1) (sign : ε=1 ∨ ε= -1) :
    4*(packed R (CharacterColumnSpan.signed P d ε) P).natDegree=(CharacterColumnSpan.units P).card := by
  have half := (positive_block (ε:=ε) pos pp period (0:R)).2
  have count := CharacterColumnSpan.signed_half pp period wheel select sign
  omega

/-- A negative selector can have another integral axis on a particular
sign mask. For d=−1 and P=8 its positive offsets are 1 and 5. They reflect
about c=6, whereas c=8 sends them to the opposite sign. -/
theorem example_affine : CharacterColumnSpan.signed 8 (-1) 1={1,5} ∧
    CharacterColumnSpan.signed 8 (-1) (-1)={3,7} ∧
    ∀ a∈CharacterColumnSpan.signed 8 (-1) 1,6-a∈CharacterColumnSpan.signed 8 (-1) 1 := by
  have eq (ε : ℤ) : CharacterColumnSpan.signed 8 (-1) ε=
      (CharacterColumnSpan.units 8).filter (fun a : ℕ => ZMod.χ₄ a=ε) := by
    ext a
    simp only [CharacterColumnSpan.signed,mem_filter]
    by_cases unit : a∈CharacterColumnSpan.units 8
    · have cop := (mem_filter.mp unit).2
      have odd := (cop.of_dvd_right (by decide : 2∣8)).odd_of_right
      simp [unit,jacobiSym.at_neg_one odd]
    · simp [unit]
  rw [eq,eq]
  decide +kernel

end PrimeFactors.CharacterColumnReflection
