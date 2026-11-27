import PrimeFactors.SmallBaseOrderPrimes
import PrimeFactors.LargeBaseOrderPairs
import PrimeFactors.SmoothOrderTail

/-! Bound every permitted integer base simultaneously. A hit at one prime
has either small order for some permitted base, or a large order satisfying
a product condition common to the entire base list. -/
namespace PrimeFactors.FixedBaseSmoothPopulation
open Finset
open SmallBaseOrderPrimes LargeBaseOrderPairs
set_option exponentiation.threshold 2050
set_option maxRecDepth 4096

/-- This includes every successful predecessor sweep checkpoint and also
counts projected identities which would be rejected during setup. -/
def localHit (A B p q : ℕ) : Prop := ∃ a : ℕ, a∈Icc 2 (2^A) ∧ ∃ E∈Nat.smoothNumbers B,
    (a : ZMod p)^((p*q-1)*E)=1

/-- A nontrivial public gcd on a positive modular-power checkpoint is among
the counted local events. The checkpoint may use a product-dependent smooth
exponent and any base in the permitted interval. -/
theorem of_gcd {A B p q a E v : ℕ} (pp : p.Prime) (qp : q.Prime)
    (base : a∈Icc 2 (2^A)) (smooth : E∈Nat.smoothNumbers B) (pos : 0<v)
    (checkpoint : Nat.ModEq (p*q) v (a^((p*q-1)*E)))
    (hit : 1 < (v-1).gcd (p*q)) : localHit A B p q ∨ localHit A B q p := by
  obtain ⟨l,prime,d⟩ := Nat.exists_prime_and_dvd (by omega : (v-1).gcd (p*q)≠1)
  have shift := d.trans (Nat.gcd_dvd_left ..)
  have divisor := d.trans (Nat.gcd_dvd_right ..)
  have equal := (checkpoint.of_dvd divisor).symm.trans ((Nat.modEq_iff_dvd' pos).mpr shift).symm
  have killed : (a : ZMod l)^((p*q-1)*E)=1 := by
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr equal
  rcases prime.dvd_mul.mp divisor with left | right
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq prime pp).mp left
    exact Or.inl ⟨a,base,E,smooth,killed⟩
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq prime qp).mp right
    exact Or.inr ⟨a,base,E,smooth,by simpa only [Nat.mul_comm p _] using killed⟩

private noncomputable def localCover (A b U B T : ℕ) : Finset (ℕ × ℕ) :=
  basePrefix A b T U ×ˢ range U ∪ (admissible U B T).image (fun v => (v.1+1,v.2+1))

private theorem mem_cover {A b U B T p q : ℕ} (pp : p.Prime) (pq : 1<q)
    (width : 2^b≤p) (pu : p<U) (qu : q<U) (gap : 2^A<2^b) (hit : localHit A B p q) :
    (p,q) ∈ localCover A b U B T := by
  classical
  letI : Fact p.Prime := ⟨pp⟩
  obtain ⟨a,ha,E,he,killed⟩ := hit
  have size := mem_Icc.mp ha
  by_cases short : orderOf (a : ZMod p)<T
  · apply mem_union_left
    apply mem_product.mpr
    exact ⟨mem_basePrefix_of_order size.1 size.2 (by omega) width pu pp short,mem_range.mpr qu⟩
  · apply mem_union_right
    apply mem_image.mpr
    refine ⟨(p-1,q-1),mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by have := pp.two_le; omega,by omega⟩,
      mem_Icc.mpr ⟨by omega,by omega⟩⟩,?_⟩,Prod.ext (by dsimp; omega) (by dsimp; omega)⟩
    apply of_power (by omega : 0<q) _ (Nat.le_of_not_gt short) he killed
    exact fun h => Nat.not_dvd_of_pos_of_lt (by omega : 0<a) (by omega : a<p)
      ((ZMod.natCast_zmod_eq_zero_iff_dvd a p).mp h)

/-- The large-order term is charged once for the entire list of bases. -/
theorem count {A b U B T : ℕ} (inputs : Finset (ℕ × ℕ)) (gap : 2^A<2^b)
    (fits : ∀ v∈inputs, v.1.Prime ∧ v.2.Prime ∧ 2^b≤v.1 ∧ v.1<U ∧ 2^b≤v.2 ∧ v.2<U)
    (hits : ∀ v∈inputs, localHit A B v.1 v.2 ∨ localHit A B v.2 v.1) :
    inputs.card ≤ 2*((basePrefix A b T U).card*U+(admissible U B T).card) := by
  classical
  let C := localCover A b U B T
  have sub : inputs ⊆ C ∪ C.image Prod.swap := by
    rintro ⟨p,q⟩ h
    obtain ⟨pp,qp,pl,pu,ql,qu⟩ := fits _ h
    rcases hits _ h with hp | hq
    · exact mem_union_left _ (mem_cover pp qp.one_lt pl pu qu gap hp)
    · exact mem_union_right _ (mem_image.mpr ⟨(q,p),mem_cover qp pp.one_lt ql qu pu gap hq,rfl⟩)
  have bound : C.card ≤ (basePrefix A b T U).card*U+(admissible U B T).card := by
    exact (card_union_le ..).trans (add_le_add (by simp) card_image_le)
  calc
    _ ≤ (C ∪ C.image Prod.swap).card := card_le_card sub
    _ ≤ C.card+(C.image Prod.swap).card := card_union_le ..
    _ ≤ _ := by rw [two_mul]; exact add_le_add bound (card_image_le.trans bound)

/-- Absolute number of candidate pairs, with both choices of the prime where
identity is detected. The full permitted base interval is charged just once. -/
theorem absolute_count (S : Finset (ℕ × ℕ))
    (fits : ∀ v∈S, v.1.Prime ∧ v.2.Prime ∧ 2^1023≤v.1 ∧ v.1<2^1024 ∧ 2^1023≤v.2 ∧ v.2<2^1024)
    (hit : ∀ v∈S, localHit 21 1001 v.1 v.2 ∨ localHit 21 1001 v.2 v.1) :
    S.card < 2^1848 := by
  have total := count (T:=2^403) S (by decide +kernel) fits hit
  have small := prefix_403 (2^1024)
  have large := SmoothOrderTail.large_403
  calc
    _ ≤ 2*((2^821)*(2^1024)+2^1846) := total.trans
      (Nat.mul_le_mul_left _ (add_le_add (Nat.mul_le_mul_right _ small.le) large.le))
    _ < _ := by decide +kernel

/-- All bases from 2 through 2^21 and every product-dependent 1000-smooth
exponent. The population counts eligible products before running the search. -/
theorem full_size (S : Finset (ℕ × ℕ)) {population : ℕ} (den : 2^2021≤population)
    (fits : ∀ v∈S, v.1.Prime ∧ v.2.Prime ∧ 2^1023≤v.1 ∧ v.1<2^1024 ∧ 2^1023≤v.2 ∧ v.2<2^1024)
    (hit : ∀ v∈S, localHit 21 1001 v.1 v.2 ∨ localHit 21 1001 v.2 v.1) :
    2^173*S.card<population := by
  have h := Nat.mul_lt_mul_of_pos_left (absolute_count S fits hit) (by positivity : 0<2^173)
  exact (h.trans_eq (by decide +kernel : 2^173*2^1848=2^2021)).trans_le den

end PrimeFactors.FixedBaseSmoothPopulation
