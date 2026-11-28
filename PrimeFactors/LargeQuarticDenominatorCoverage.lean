import PrimeFactors.QuarticStripCoordinateBounds
import PrimeFactors.QuarticUnitLift
import PrimeFactors.QuarticPrimePopulation

/-! Counting the eligible prime products with a primitive quartic reading
at one prescribed denominator. For large denominators the congruence of the
long coordinate modulo d determines it once the short coordinate is fixed. -/
namespace PrimeFactors.LargeQuarticDenominatorCoverage

open Finset
open MixedPrefixSample (eligible)
open private PrimeFactors.QuarticPrimePopulation.eligible_bounds from PrimeFactors.QuarticPrimePopulation
open scoped Classical

set_option exponentiation.threshold 8192
set_option maxRecDepth 8192
attribute [local irreducible] eligible

/-- Both recognition strips, restricted to coprime numerator coordinates. -/
noncomputable def family (d : ℕ) : Finset (ℕ×ℕ) := eligible.filter fun v =>
  ∃ x y : ℕ, 0<x ∧ 0<y ∧ x.Coprime y ∧ d^4*(v.1*v.2)=x^4+4*y^4 ∧
    (d^4*(v.1*v.2)<(x+1)^4 ∨ d^4*(v.1*v.2)<4*(y+1)^4)

theorem mem_family {d : ℕ} {v : ℕ×ℕ} : v∈family d ↔ v∈eligible ∧
    ∃ x y : ℕ, 0<x ∧ 0<y ∧ x.Coprime y ∧ d^4*(v.1*v.2)=x^4+4*y^4 ∧
    (d^4*(v.1*v.2)<(x+1)^4 ∨ d^4*(v.1*v.2)<4*(y+1)^4) := mem_filter

private noncomputable def side (point : ℕ→ℕ→ℕ→Prop) := eligible.filter fun v =>
  ∃ a b, point (v.1*v.2) a b

private theorem mem_side {point : ℕ→ℕ→ℕ→Prop} {v : ℕ×ℕ} : v∈side point ↔
    v∈eligible ∧ ∃ a b, point (v.1*v.2) a b := mem_filter

attribute [local irreducible] side family

/-- The short coordinate and the encoded long coordinate determine the product. -/
private theorem count_side {d L S : ℕ} (dp : 0<d) (value : ℕ→ℕ→ℕ) (point : ℕ→ℕ→ℕ→Prop)
    (form : ∀ {n a b}, point n a b → d^4*n=value a b) (key : ℕ→ℕ)
    (bounds : ∀ {n a b}, n<2^2048 → point n a b → key a<L ∧ b<S)
    (unique : ∀ {n m a c b}, n<2^2048 → m<2^2048 → point n a b → point m c b →
      key a=key c → a=c) : (side point).card≤L*S := by
  let V := side point
  have eligibleV (v : V) : v.val∈eligible := (mem_side.mp v.property).1
  have width (v : V) := (PrimeFactors.QuarticPrimePopulation.eligible_bounds (eligibleV v)).2.1
  choose a b fits using (fun v : V =>
    (show ∃ a b : ℕ, point (v.val.1*v.val.2) a b from (mem_side.mp v.property).2))
  let encode (v : V) : Fin L×Fin S :=
    (⟨key (a v),(bounds (width v) (fits v)).1⟩,⟨b v,(bounds (width v) (fits v)).2⟩)
  have inject : Function.Injective encode := by
    intro u v eq
    have ka : key (a u)=key (a v) := congrArg (fun z : Fin L×Fin S => z.1.val) eq
    have kb : b u=b v := congrArg (fun z : Fin L×Fin S => z.2.val) eq
    have same := unique (width u) (width v) (kb ▸ fits u) (fits v) ka
    have scaled := (form (fits u)).trans ((congrArg₂ value same kb).trans (form (fits v)).symm)
    have prod := Nat.eq_of_mul_eq_mul_left (pow_pos dp 4) scaled
    obtain ⟨_,ord,_,p,q,_⟩ := SumGridPopulation.eligible_data.mp (eligibleV u)
    obtain ⟨_,order,_,p',_,_⟩ := SumGridPopulation.eligible_data.mp (eligibleV v)
    obtain ⟨left,right⟩ := ordered_semiprime_pair_unique p q ord.le order.le p'.one_lt prod.symm
    exact Subtype.ext (Prod.ext left.symm right.symm)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] using
    Nat.card_le_card_of_injective encode inject

private theorem side_bound {d : ℕ} (dp : 0<d) (fit : d≤2^512) (value : ℕ→ℕ→ℕ)
    (point : ℕ→ℕ→ℕ→Prop) (form : ∀ {n a b}, point n a b → d^4*n=value a b)
    (small_box : ∀ {n a b}, n<2^2048 → d≤2^200 → point n a b → a<2^712 ∧ b<2^535)
    (large_box : ∀ {n a b}, n<2^2048 → 2^200<d → point n a b → a<d^4 ∧ b<2^769)
    (lift : ∀ {n m a c b}, point n a b → point m c b → a ≡ c [MOD d] → a ≡ c [MOD d^4]) :
    (side point).card≤2^1281 := by
  by_cases small : d≤2^200
  · have count : (side point).card≤2^712*2^535 :=
      count_side dp value point form id (fun hn repr => small_box hn small repr) (fun _ _ _ _ eq => eq)
    exact count.trans (by decide +kernel)
  · have big : 2^200<d := by omega
    have count : (side point).card≤d*2^769 := by
      apply count_side dp value point form (fun a => a%d)
      · exact fun hn repr => ⟨Nat.mod_lt _ dp,(large_box hn big repr).2⟩
      · intro n m a c b hn hm first second eq
        exact (lift first second eq).eq_of_lt_of_lt (large_box hn big first).1
          (large_box hm big second).1
    exact count.trans ((Nat.mul_le_mul_right _ fit).trans_eq (by decide +kernel))

private def X (d n a b : ℕ) : Prop :=
  a.Coprime b ∧ d^4*n=a^4+4*b^4 ∧ d^4*n<(a+1)^4

private def Y (d n b a : ℕ) : Prop :=
  a.Coprime b ∧ d^4*n=a^4+4*b^4 ∧ d^4*n<4*(b+1)^4

/-- At a fixed denominator through 2⁵¹², each branch covers at most 2¹²⁸¹
eligible prime pairs, even when the primitive coordinates may vary by input. -/
theorem one {d : ℕ} (pos : 0<d) (fit : d≤2^512) : (family d).card≤2^1282 := by
  have cover : family d⊆side (X d) ∪ side (Y d) := by
    intro v hv
    obtain ⟨mem,x,y,_,_,cop,point,left|right⟩ := mem_family.mp hv
    · exact mem_union_left _ (mem_side.mpr ⟨mem,x,y,cop,point,left⟩)
    · exact mem_union_right _ (mem_side.mpr ⟨mem,y,x,cop,point,right⟩)
  have left : (side (X d)).card≤2^1281 := by
    apply side_bound pos fit (fun a b => a^4+4*b^4) (X d) (fun h => h.2.1)
    · intro n a b hn hd h
      exact (QuarticStripCoordinateBounds.small (n:=n) (d:=d) (x:=a) (y:=b) hn hd h.2.1).1 h.2.2
    · intro n a b hn hd h
      exact (QuarticStripCoordinateBounds.large (n:=n) (d:=d) (x:=a) (y:=b) hn hd fit h.2.1).1 h.2.2
    · exact fun first second eq => QuarticUnitLift.same_b second.1 first.2.1 second.2.1 eq
  have right : (side (Y d)).card≤2^1281 := by
    apply side_bound pos fit (fun b a => a^4+4*b^4) (Y d) (fun h => h.2.1)
    · intro n b a hn hd h
      exact (QuarticStripCoordinateBounds.small (n:=n) (d:=d) (x:=a) (y:=b) hn hd h.2.1).2 h.2.2
    · intro n b a hn hd h
      exact (QuarticStripCoordinateBounds.large (n:=n) (d:=d) (x:=a) (y:=b) hn hd fit h.2.1).2 h.2.2
    · exact fun first second eq => QuarticUnitLift.same_a second.1 first.2.1 second.2.1 eq
  exact (((card_le_card cover).trans (card_union_le ..)).trans
    (Nat.add_le_add left right)).trans_eq (by decide +kernel)

end PrimeFactors.LargeQuarticDenominatorCoverage
