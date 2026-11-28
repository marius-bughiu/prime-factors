import PrimeFactors.CircleMarkSmallTargets
import PrimeFactors.CyclotomicCoefficientProbePopulation

/-! A finite population bound over products, allowing the target, coordinate
and tested component to be chosen after seeing the product. -/

namespace PrimeFactors.CircleMarkSmallTargetPopulation

open Finset MixedPrefixSample
open private PrimeFactors.MixedPrefixSample.mem_primes from PrimeFactors.MixedPrefixSample
open private PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info
  from PrimeFactors.CyclotomicCoefficientProbePopulation
open private PrimeFactors.CircleMarkSmallTargets.abs_sub_bound from PrimeFactors.CircleMarkSmallTargets
open private PrimeFactors.CircleMarkAutocorrelation.abs_coprime from PrimeFactors.CircleMarkAutocorrelation

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible primes

/-- Maximum positive raw coordinate or lag and maximum positive target. -/
abbrev H : ℕ := 2^900
abbrev A : ℕ := 2015165

/-- Absolute integer tested for a target a, a coordinate h and scale s. -/
def magnitude (a h s : ℕ) := ((h : ℤ)^2-(a : ℤ)*(s : ℤ)^2).natAbs

/-- Allow all targets, positive lags and scales simultaneously. The scale
one tests ordinary marks. The scales d−1 and d+1 are the two factors in the
resultant of the square-related targets a and a*d². -/
noncomputable def successful (S : Finset ℕ) : Finset (ℕ×ℕ) := by
  classical
  exact eligible.filter fun v => ∃ a∈Icc 1 A, ∃ h∈Icc 1 H, ∃ s∈S,
    jacobiSym a (v.1*v.2)= -1 ∧ ¬(v.1*v.2).Coprime (magnitude a h s)

private noncomputable def divisors (z : ℕ) := primes.filter fun p => 0<z ∧ z<X^2 ∧ p∣z

/-- Two distinct primes of at least 1024 bits cannot divide the same positive
integer below 2^2046. -/
private theorem divisor_count (z : ℕ) : (divisors z).card≤1 := by
  apply card_le_one.mpr
  intro p hp q hq
  obtain ⟨pl,zp,small,pd⟩ := mem_filter.mp hp
  obtain ⟨ql,_,_,qd⟩ := mem_filter.mp hq
  obtain ⟨⟨lp,_⟩,pp⟩ := PrimeFactors.MixedPrefixSample.mem_primes.mp pl
  obtain ⟨⟨lq,_⟩,qp⟩ := PrimeFactors.MixedPrefixSample.mem_primes.mp ql
  by_contra ne
  have cop := (Nat.coprime_primes pp qp).mpr ne
  have lower := Nat.mul_le_mul lp lq
  rw [←sq] at lower
  exact (not_lt_of_ge (lower.trans (Nat.le_of_dvd zp (cop.mul_dvd_of_dvd_of_dvd pd qd)))) small

private def values (S : Finset ℕ) : Finset ℕ :=
  ((Icc 1 A) ×ˢ (Icc 1 H)).biUnion (fun u => S.image (magnitude u.1 u.2))

private theorem value_count (S : Finset ℕ) : (values S).card≤A*H*S.card := by
  calc
    _ ≤ ((Icc 1 A) ×ˢ (Icc 1 H)).card*S.card :=
      card_biUnion_le_card_mul _ _ _ (fun _ _ => card_image_le)
    _ = _ := by simp [Nat.card_Icc]

private theorem size {a h s : ℕ} (ap : a≤A) (inside : h≤H) (scale : s≤2*H+1) :
    magnitude a h s<X^2 := by
  apply PrimeFactors.CircleMarkSmallTargets.abs_sub_bound (sq_nonneg _) (by positivity)
  · calc (h:ℤ)^2 ≤ (H:ℤ)^2 := by exact_mod_cast Nat.pow_le_pow_left inside 2
         _ < _ := by decide +kernel
  · calc (a:ℤ)*(s:ℤ)^2 ≤ (A:ℤ)*((2*H+1:ℕ):ℤ)^2 := by
           exact_mod_cast Nat.mul_le_mul ap (Nat.pow_le_pow_left scale 2)
         _ < _ := by decide +kernel

private noncomputable def pool (S : Finset ℕ) := (values S).biUnion divisors

private theorem pool_count (S : Finset ℕ) : (pool S).card≤A*H*S.card := by
  have bound : (pool S).card≤(values S).card*1 :=
    card_biUnion_le_card_mul _ _ _ fun z _ => divisor_count z
  simpa using bound.trans (by simpa using value_count S : (values S).card*1≤_)

attribute [local irreducible] values pool divisors successful magnitude

private theorem subset (S : Finset ℕ) (scales : ∀ s∈S,s≤2*H+1) :
    successful S⊆CyclotomicCoefficientProbePopulation.hits (pool S) := by
  classical
  intro v hv
  rw [successful,mem_filter] at hv
  obtain ⟨pair,a,ha,h,hh,s,hs,neg,hit⟩ := hv
  obtain ⟨p,q,_⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info pair
  have val : magnitude a h s∈values S := by
    simp only [values,mem_biUnion,mem_product,mem_image]
    exact ⟨(a,h),⟨ha,hh⟩,s,hs,rfl⟩
  have positive : 0<h := (mem_Icc.mp hh).1
  have zp : 0<magnitude a h s := by
    unfold magnitude
    apply Int.natAbs_pos.mpr
    exact (CircleMarkSmallTargets.nonzero_component neg (Or.inl (by exact_mod_cast positive.ne')))
  have small := size (mem_Icc.mp ha).2 (mem_Icc.mp hh).2 (scales s hs)
  have into {r : ℕ} (prime : r∈primes) (dv : r∣magnitude a h s) : r∈pool S := by
    simp only [pool,mem_biUnion,divisors,mem_filter]
    exact ⟨magnitude a h s,val,prime,zp,small,dv⟩
  rw [Nat.coprime_mul_iff_left] at hit
  push_neg at hit
  apply (CyclotomicCoefficientProbePopulation.mem_hits (Q:=pool S) (z:=v)).mpr
  refine ⟨pair,?_⟩
  by_cases left : v.1.Coprime (magnitude a h s)
  · have no := hit left
    have div := Classical.not_not.mp (fun nd => no ((PrimeFactors.MixedPrefixSample.mem_primes.mp q).2.coprime_iff_not_dvd.mpr nd))
    exact ⟨v.2,into (r:=v.2) q div,Or.inr (Or.inl rfl)⟩
  · have div := Classical.not_not.mp (fun nd => left ((PrimeFactors.MixedPrefixSample.mem_primes.mp p).2.coprime_iff_not_dvd.mpr nd))
    exact ⟨v.1,into (r:=v.1) p div,Or.inl rfl⟩

/-- General counting inequality for any fixed finite list of scales. Each
target-coordinate-scale triple costs at most one possible full-size prime. -/
theorem population (S : Finset ℕ) (scales : ∀ s∈S,s≤2*H+1) {m : ℕ}
    (capacity : 41056*m*(A*H*S.card)≤X) : m*(successful S).card<eligible.card := by
  exact (Nat.mul_le_mul_left m (card_le_card (subset S scales))).trans_lt
    (CyclotomicCoefficientProbePopulation.fraction ((Nat.mul_le_mul_left _ (pool_count S)).trans capacity))

/-- The raw test is exactly a mark at x in the modular circle. -/
theorem raw_test {n : ℕ} [NeZero n] (a x : ℕ) :
    ¬n.Coprime (magnitude a x 1) ↔ (x:ZMod n)∈CircleBranchCount.marked n a := by
  rw [magnitude]
  simp only [Nat.cast_one,one_pow,mul_one]
  rw [←PrimeFactors.CircleMarkAutocorrelation.abs_coprime]
  simp only [CircleBranchCount.marked,mem_filter,mem_univ,true_and,Int.cast_sub,Int.cast_pow,
    Int.cast_natCast]
  have eq : (x:ZMod n)^2-(a:ZMod n) = -((a:ZMod n)-(x:ZMod n)^2) := by ring
  rw [eq,IsUnit.neg_iff]

/-- A raw hit for any positive target up to 2,015,165 in the whole inclusive
coordinate window through 2^900 occurs on fewer than one in 2^86 products. -/
theorem raw_population : 2^86*(successful {1}).card<eligible.card := by
  apply population _ (by intro s hs; rw [mem_singleton] at hs; subst s; decide +kernel)
  simp only [card_singleton]
  decide +kernel

/-- At d=2L the two-component resultant gcd fails the coprimality
test exactly when one of the two integer components fails it. -/
theorem packed_test (n a h L : ℕ) (pos : 0<L) :
    let d := 2*(L:ℤ)
    CircleMarkResultant.commonGcd n a (a*d^2) h ≠ 1 ↔
    ¬n.Coprime (magnitude a h (2*L-1)) ∨ ¬n.Coprime (magnitude a h (2*L+1)) := by
  dsimp only
  rw [CircleMarkResultant.commonGcd,CircleMarkResultant.scaled_resultant,Int.natAbs_mul]
  change ¬n.Coprime _ ↔ _
  rw [Nat.coprime_mul_iff_right]
  simp only [magnitude,Nat.cast_sub (show 1≤2*L by omega),Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  tauto

/-- Membership in the population counted below, stated using the public raw
mark and the single resultant gcd. A single eligible target suffices. -/
theorem mem_combined {p q : ℕ} [NeZero (p*q)] :
    (p,q)∈successful {1,2*H-1,2*H+1} ↔ (p,q)∈eligible ∧
      ∃ a∈Icc 1 A, ∃ h∈Icc 1 H, jacobiSym a (p*q)= -1 ∧
        ((h:ZMod (p*q))∈CircleBranchCount.marked (p*q) a ∨
         CircleMarkResultant.commonGcd (p*q) a (a*(2*(H:ℤ))^2) h≠1) := by
  classical
  rw [successful,mem_filter]
  apply and_congr_right
  intro _
  apply exists_congr
  intro a
  apply and_congr_right
  intro _
  apply exists_congr
  intro h
  apply and_congr_right
  intro _
  have packed := packed_test (p*q) a h H (by decide : 0<H)
  dsimp only at packed
  rw [←raw_test,packed]
  constructor
  · rintro ⟨s,hs,neg,hit⟩
    refine ⟨neg,?_⟩
    simp only [mem_insert,mem_singleton] at hs
    rcases hs with rfl|rfl|rfl
    · exact Or.inl hit
    · exact Or.inr (Or.inl hit)
    · exact Or.inr (Or.inr hit)
  · rintro ⟨neg,h1|h2|h3⟩
    · exact ⟨1,mem_insert_self ..,neg,h1⟩
    · exact ⟨2*H-1,mem_insert_of_mem (mem_insert_self ..),neg,h2⟩
    · exact ⟨2*H+1,mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)),neg,h3⟩

/-- Fewer than one in 2^85 eligible products permits any raw hit or either
packed component at any allowed target and coordinate. Both target and
coordinate may depend arbitrarily on the product. -/
theorem combined_population :
    2^85*(successful {1,2*H-1,2*H+1}).card<eligible.card := by
  apply population _ (by
    intro s hs
    simp only [mem_insert,mem_singleton] at hs
    rcases hs with rfl|rfl|rfl <;> decide)
  have card : ({1,2*H-1,2*H+1} : Finset ℕ).card=3 := by decide +kernel
  rw [card]
  decide +kernel

end PrimeFactors.CircleMarkSmallTargetPopulation
