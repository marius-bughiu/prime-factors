import PrimeFactors.ScaledQuarticMenuBound
import PrimeFactors.QuarticStripDenominators
import Mathlib.Data.Nat.Squarefree

/-! Cancellation of a common coordinate divisor on a rational quartic point.
Both strict fourth-root recognition gaps persist after cancellation. -/
namespace PrimeFactors.ReduceQuarticDenominator

/-- A fourth power in a product of a fourth power with a squarefree integer
has its fourth root in the original fourth root. -/
theorem root_divides {g d n : ℕ} (gp : 0<g) (dp : 0<d)
    (sf : Squarefree n) (div : g^4∣d^4*n) : g∣d := by
  apply (Nat.factorization_le_iff_dvd gp.ne' dp.ne').mp
  intro p
  have val := (Nat.factorization_le_iff_dvd (pow_ne_zero 4 gp.ne')
    (mul_ne_zero (pow_ne_zero 4 dp.ne') sf.ne_zero)).mpr div p
  simp only [Nat.factorization_mul (pow_ne_zero 4 dp.ne') sf.ne_zero,
    Nat.factorization_pow,Finsupp.smul_apply,Finsupp.add_apply,nsmul_eq_mul] at val
  have cap := sf.natFactorization_le_one p
  omega

/-- A strict gap at a multiple of the reduced coordinate implies the same
strict gap at the reduced coordinate, for either leading coefficient. -/
theorem gap_descends {g t n z c : ℕ} (gp : 0<g)
    (gap : (g*t)^4*n<c*(g*z+1)^4) : t^4*n<c*(z+1)^4 := by
  have inc : g*z+1≤g*(z+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
  apply Nat.lt_of_mul_lt_mul_left (a := g^4)
  calc
    g^4*(t^4*n) = (g*t)^4*n := by ring
    _ < c*(g*z+1)^4 := gap
    _ ≤ c*(g*(z+1))^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left inc 4)
    _ = g^4*(c*(z+1)^4) := by ring

/-- Reduce by precisely the gcd of the numerators. This holds for every
squarefree input, including even squarefree inputs. -/
theorem reduce {a b d n : ℕ} (ap : 0<a) (bp : 0<b) (dp : 0<d)
    (sf : Squarefree n) (point : d^4*n=a^4+4*b^4) :
    let g := a.gcd b
    ∃ x y t : ℕ, a=g*x ∧ b=g*y ∧ d=g*t ∧ 0<x ∧ 0<y ∧ 0<t ∧ t≤d ∧
      x.Coprime y ∧ t^4*n=x^4+4*y^4 ∧
      (d^4*n<(a+1)^4 → t^4*n<(x+1)^4) ∧
      (d^4*n<4*(b+1)^4 → t^4*n<4*(y+1)^4) := by
  intro g
  let x := a/g
  let y := b/g
  have gp : 0<g := Nat.gcd_pos_of_pos_left b ap
  have ax : g*x=a := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have by' : g*y=b := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have div : g^4∣d^4*n := by
    rw [point,←ax,←by',mul_pow,mul_pow]
    exact dvd_add (dvd_mul_right ..) (dvd_mul_of_dvd_right (dvd_mul_right ..) _)
  obtain ⟨t,dt⟩ := root_divides gp dp sf div
  have gcdxy : x.Coprime y := Nat.coprime_div_gcd_div_gcd gp
  have reduced : t^4*n=x^4+4*y^4 := Nat.eq_of_mul_eq_mul_left (pow_pos gp 4) (calc
    g^4*(t^4*n) = (g*t)^4*n := by ring
    _ = (g*x)^4+4*(g*y)^4 := by rw [←dt,ax,by',point]
    _ = g^4*(x^4+4*y^4) := by ring)
  refine ⟨x,y,t,ax.symm,by'.symm,dt,Nat.pos_of_mul_pos_left (ax ▸ ap),
    Nat.pos_of_mul_pos_left (by' ▸ bp),Nat.pos_of_mul_pos_left (dt ▸ dp),
    dt ▸ Nat.le_mul_of_pos_left _ gp,gcdxy,reduced,?_,?_⟩
  · intro gap
    apply (show t^4*n<1*(x+1)^4 → t^4*n<(x+1)^4 by simp)
    apply gap_descends gp
    simpa only [←dt,ax,one_mul] using gap
  · intro gap
    apply gap_descends gp
    rwa [←dt,by']

open ComplementaryQuarticProducts (choices mem_choices)
open Finset
open MixedPrefixSample (eligible)
open scoped Classical

/-- Every recognition descends to a primitive recognition at a divisor of
the original denominator. -/
theorem primitive_choice {d n : ℕ} (dp : 0<d) (sf : Squarefree n)
    (hit : (choices (d^4*n)).Nonempty) :
    ∃ t : ℕ, t∣d ∧ 0<t ∧ t≤d ∧ ∃ x y : ℕ, 0<x ∧ 0<y ∧ x.Coprime y ∧
      t^4*n=x^4+4*y^4 ∧ (t^4*n<(x+1)^4 ∨ t^4*n<4*(y+1)^4) := by
  obtain ⟨ab,mem⟩ := hit
  obtain ⟨a,b,ap,bp,point,gap,_⟩ := mem_choices.mp mem
  obtain ⟨x,y,t,_,_,eq,xp,yp,tp,small,cop,form,left,right⟩ := reduce ap bp dp sf point
  exact ⟨t,eq ▸ dvd_mul_left t (a.gcd b),tp,small,x,y,xp,yp,cop,form,gap.imp left right⟩

open private PrimeFactors.QuarticPrimePopulation.eligible_bounds from PrimeFactors.QuarticPrimePopulation

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible

theorem reduced_hit {p q d : ℕ} (mem : (p,q)∈eligible) (dp : 0<d) (fit : d≤2048)
    (hit : (choices (d^4*(p*q))).Nonempty) : ∃ t : ℕ, t∣d ∧ (t=1 ∨ t=725 ∨ t=1517) ∧
      (choices (t^4*(p*q))).Nonempty := by
  obtain ⟨pl,ord,qu,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp mem
  have bounds := PrimeFactors.QuarticPrimePopulation.eligible_bounds mem
  have sf := (Nat.squarefree_mul ((Nat.coprime_primes pp qp).mpr ord.ne)).mpr ⟨pp.squarefree,qp.squarefree⟩
  obtain ⟨t,div,tp,small,x,y,xp,yp,cop,form,gap⟩ := primitive_choice dp sf hit
  have pgt : 2<p := (by decide +kernel : 2<FullRangeResidueEstimates.X).trans_le pl
  have balanced : q≤2*p := qu.le.trans (Nat.mul_le_mul_left 2 pl)
  have menu := QuarticStripDenominators.primitive_menu pp qp (pp.odd_of_ne_two pgt.ne') (qp.odd_of_ne_two (pgt.trans ord).ne')
    ord.le balanced bounds.1 bounds.2.1 tp (small.trans fit) yp cop form gap
  exact ⟨t,div,menu,RecognizingQuarticProducts.factors x y,mem_choices.mpr ⟨x,y,xp,yp,form,gap,rfl⟩⟩

theorem menu_hit_iff {p q : ℕ} (mem : (p,q)∈eligible) :
    (∃ d∈Icc 1 2048, (choices (d^4*(p*q))).Nonempty) ↔
      (choices (p*q)).Nonempty ∨ (choices (725^4*(p*q))).Nonempty ∨
      (choices (1517^4*(p*q))).Nonempty := by
  constructor
  · rintro ⟨d,hd,hit⟩
    obtain ⟨dp,fit⟩ := mem_Icc.mp hd
    obtain ⟨t,_,menu,h⟩ := reduced_hit mem dp fit hit
    rcases menu with rfl|rfl|rfl
    · exact Or.inl (by simpa only [one_pow,one_mul] using h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (one|s|l)
    · exact ⟨1,mem_Icc.mpr (by decide),by simpa only [one_pow,one_mul] using one⟩
    · exact ⟨725,mem_Icc.mpr (by decide),s⟩
    · exact ⟨1517,mem_Icc.mpr (by decide),l⟩

theorem small_hit_iff {p q : ℕ} (mem : (p,q)∈eligible) :
    (∃ d∈Icc 1 724, (choices (d^4*(p*q))).Nonempty) ↔ (choices (p*q)).Nonempty := by
  constructor
  · rintro ⟨d,hd,hit⟩
    obtain ⟨dp,fit⟩ := mem_Icc.mp hd
    obtain ⟨t,div,menu,h⟩ := reduced_hit mem dp (by omega) hit
    have td := Nat.le_of_dvd dp div
    have one : t=1 := by omega
    simpa only [one,one_pow,one_mul] using h
  · exact fun h => ⟨1,mem_Icc.mpr (by decide),by simpa only [one_pow,one_mul] using h⟩

open ScaledQuarticMenuBound (covered family)

/-- The entire denominator budget has identical recognized inputs to the
three reduced denominators. -/
theorem menu_covered : covered (Icc 1 2048)=covered {1,725,1517} := by
  ext v
  simp only [covered,mem_biUnion]
  change (∃ d∈Icc 1 2048, v∈family d) ↔ ∃ d∈({1,725,1517}:Finset ℕ), v∈family d
  constructor
  · rintro ⟨d,hd,h⟩
    obtain ⟨dp,fit⟩ := mem_Icc.mp hd
    obtain ⟨e,hit⟩ := mem_filter.mp h
    obtain ⟨t,_,menu,newHit⟩ := reduced_hit e dp fit hit
    exact ⟨t,by simpa using menu,mem_filter.mpr ⟨e,newHit⟩⟩
  · rintro ⟨d,hd,h⟩
    simp only [mem_insert,mem_singleton] at hd
    exact ⟨d,mem_Icc.mpr (by omega),h⟩

theorem small_covered : covered (Icc 1 724)=family 1 := by
  ext v
  simp only [covered,mem_biUnion]
  change (∃ d∈Icc 1 724, v∈family d) ↔ _
  constructor
  · rintro ⟨d,hd,h⟩
    obtain ⟨e,hit⟩ := mem_filter.mp h
    have h1 := (small_hit_iff e).mp ⟨d,hd,hit⟩
    refine mem_filter.mpr ⟨e,?_⟩
    change (choices ((1:ℕ)^4*(v.1*v.2))).Nonempty
    simpa only [one_pow,one_mul] using h1
  · exact fun h => ⟨1,mem_Icc.mpr (by decide),h⟩


end PrimeFactors.ReduceQuarticDenominator
