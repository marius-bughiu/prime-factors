import PrimeFactors.CircleMarkCofactorBands
import PrimeFactors.CircleMarkSmallTargetPopulation

/-! How many positive coordinates the unreduced cofactor-band test can skip
before reaching a mark. The population is the full set of distinct 1,024-bit
prime pairs with a 2,048-bit product, with the smaller prime first. -/
namespace PrimeFactors.CircleMarkBandSavings

open Finset MixedPrefixSample CircleMarkCofactorBands
open scoped Classical
open private PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info
  PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info from PrimeFactors.CyclotomicCoefficientProbePopulation

set_option exponentiation.threshold 8192
set_option maxRecDepth 8192
attribute [local irreducible] eligible primes

/-- The strict upper endpoint for both factors. -/
abbrev U : ℕ := 2^1024

/-- The publicly available lower endpoint, since both factors are strictly below U. -/
def lower (n : ℕ) := n/U+1

/-- All discarded positive coordinates through stop, including those with no
positive remainder. Counting all such coordinates also covers a partial implementation
that only skips some of the nonmembers. -/
noncomputable def skipped (n a stop : ℕ) : Finset ℕ :=
  (Icc 1 stop).filter fun x => ¬inBands (lower n) (U-1) (x^2-a)

/-- Sufficient conditions for a concrete coordinate threshold R to lie in the
continuous part of the band cover, simultaneously for every target up to A. -/
theorem beyond {n a x A G k R : ℕ} (width : lower n≤U-G) (gap : 0<G)
    (ku : G≤U) (kp : 0<k) (touch : U-G-1≤k*(G-1)) (edge : k*(U-G)+A≤R^2)
    (target : a≤A) (large : R≤x) : inBands (lower n) (U-1) (x^2-a) := by
  apply continuous (by simp [lower]) (by omega) kp
  · have e := Nat.mul_le_mul_left k (show G-1≤U-1-lower n by omega)
    omega
  · have f := Nat.mul_le_mul_left k width
    have s := Nat.pow_le_pow_left large 2
    omega

private theorem lower_le {p q : ℕ} (pv : 0<p) (qu : q<U) : lower (p*q)≤p := by
  have bound : p*q<p*U := Nat.mul_lt_mul_of_pos_left qu pv
  exact (Nat.div_lt_iff_lt_mul (by decide +kernel : 0<U)).mpr bound

private theorem away {v : ℕ×ℕ} (mem : v∈eligible) {G : ℕ} (separated : v.1≤U-G) :
    lower (v.1*v.2)≤U-G := by
  obtain ⟨p,q,_⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info mem
  obtain ⟨pl,_,_,_⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info p
  obtain ⟨_,qu,_,_⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info q
  exact (lower_le ((by decide +kernel : 0<X).trans_le pl) qu).trans separated

private theorem before_count {n a stop G k R : ℕ} (width : lower n≤U-G) (gap : 0<G)
    (ku : G≤U) (kp : 0<k) (touch : U-G-1≤k*(G-1))
    (edge : k*(U-G)+CircleMarkSmallTargetPopulation.A≤R^2) (target : a≤CircleMarkSmallTargetPopulation.A) :
    (skipped n a stop).card≤R-1 := by
  have sub : skipped n a stop⊆Icc 1 (R-1) := by
    intro x hx
    obtain ⟨iv,miss⟩ := mem_filter.mp hx
    exact mem_Icc.mpr ⟨(mem_Icc.mp iv).1,by
      by_contra! out
      exact miss (beyond width gap ku kp touch edge target (by omega))⟩
  exact (card_le_card sub).trans_eq (by simp [Nat.card_Icc])

/-- At the stated distance from the top, no positive coordinate at or beyond
2^524 is removed, regardless of the run's stopping position. -/
theorem far_count {v : ℕ×ℕ} (mem : v∈eligible) (separated : v.1≤U-2^1000)
    {a : ℕ} (target : a≤CircleMarkSmallTargetPopulation.A) (stop : ℕ) :
    (skipped (v.1*v.2) a stop).card≤2^524-1 := by
  exact before_count (k:=2^24) (away mem separated) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) target

/-- A smaller endpoint exception gives the uniform 2^540 coordinate cutoff. -/
theorem broad_count {v : ℕ×ℕ} (mem : v∈eligible) (separated : v.1≤U-2^968)
    {a : ℕ} (target : a≤CircleMarkSmallTargetPopulation.A) (stop : ℕ) :
    (skipped (v.1*v.2) a stop).card≤2^540-1 := by
  exact before_count (k:=2^56) (away mem separated) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) target

/-- The uppermost factor interval and any eligible product with an early raw
mark for any of the allowed targets. Both exceptions are taken over prime pairs. -/
noncomputable def near (G : ℕ) := eligible.filter fun v => U-G<v.1
noncomputable def exceptional (G : ℕ) := near G ∪ CircleMarkSmallTargetPopulation.successful {1}

private theorem near_count {g : ℕ} (gu : 2*g≤U) : (near (2*g)).card≤g^2 := by
  let I := Ico (U/2-g) (U/2)
  let decode (v : ℕ×ℕ) := (2*v.1+1,2*v.2+1)
  have evenU : 2*(U/2)=U := by decide +kernel
  have sub : near (2*g)⊆(I ×ˢ I).image decode := by
    intro v hv
    obtain ⟨pair,close⟩ := mem_filter.mp hv
    obtain ⟨p,q,order⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info pair
    obtain ⟨_,_,_,po⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info p
    obtain ⟨_,qu,_,qo⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.prime_info q
    change v.2<U at qu
    apply mem_image.mpr
    refine ⟨(v.1/2,v.2/2),mem_product.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,
      mem_Ico.mpr ⟨by omega,by omega⟩⟩,?_⟩
    exact Prod.ext (by change 2*(v.1/2)+1=v.1; omega) (by change 2*(v.2/2)+1=v.2; omega)
  have ci : I.card=g := by dsimp [I]; rw [Nat.card_Ico]; omega
  exact ((card_le_card sub).trans card_image_le).trans_eq (by rw [card_product,ci,sq])

private theorem combine_counts {e u raw both g M k j l : ℕ} (den : 2^2046<21000000*e)
    (nearSmall : u≤g^2) (rawSmall : 2^86*raw<e) (union : both≤u+raw)
    (positive : 0<j) (sum : j+l=k)
    (tail : k*M*21000000*g^2≤j*2^2046) (early : k*M≤l*2^86) :
    M*both<e := by
  have left : k*M*u<j*e := by
    apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
    calc
      _ ≤ k*M*21000000*g^2 := by
        simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using
          Nat.mul_le_mul_left (k*M*21000000) nearSmall
      _ ≤ j*2^2046 := tail
      _ < j*(21000000*e) := Nat.mul_lt_mul_of_pos_left den positive
      _ = _ := by ring
  have right : k*M*raw≤l*e :=
    (Nat.mul_le_mul_right _ early).trans (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left l rawSmall.le)
  apply Nat.lt_of_mul_lt_mul_left (a:=k)
  calc
    _ = k*M*both := by ring
    _ ≤ k*M*(u+raw) := Nat.mul_le_mul_left _ union
    _ = _ := Nat.mul_add ..
    _ < j*e+l*e := Nat.add_lt_add_of_lt_of_le left right
    _ = _ := by rw [←Nat.add_mul,sum]

private theorem joint_bound {g M k j l : ℕ} (gu : 2*g≤U) (positive : 0<j) (sum : j+l=k)
    (tail : k*M*21000000*g^2≤j*2^2046) (early : k*M≤l*2^86) :
    M*(exceptional (2*g)).card<eligible.card :=
  combine_counts ChebyshevPrimeSample.eligible_count (near_count gu)
    CircleMarkSmallTargetPopulation.raw_population
    (card_union_le (near (2*g)) (CircleMarkSmallTargetPopulation.successful {1}))
    positive sum tail early

/-- Fewer than one pair in 2^23 is excluded by the sharper pointwise cutoff. -/
theorem far_exceptions : 2^23*(exceptional (2^1000)).card<eligible.card := by
  rw [show (2:ℕ)^1000=2*2^999 by decide +kernel]
  exact joint_bound (g:=2^999) (M:=2^23) (k:=3) (j:=2) (l:=1)
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)

/-- Fewer than one pair in 2^85 is excluded by the wider pointwise cutoff. -/
theorem broad_exceptions : 2^85*(exceptional (2^968)).card<eligible.card := by
  rw [show (2:ℕ)^968=2*2^967 by decide +kernel]
  exact joint_bound (g:=2^967) (M:=2^85) (k:=2) (j:=1) (l:=1)
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)

/-- The absolute count includes the initial prefix that the elementary
magnitude test already removes. No search for a cofactor is needed there. -/
theorem initial_count {p q a stop : ℕ} (full : 2^2047≤p*q) (long : 2^511≤stop) :
    2^511≤(skipped (p*q) a stop).card := by
  have size : 2^1023≤p*q/U :=
    (Nat.le_div_iff_mul_le (by decide +kernel : 0<U)).mpr
      ((by decide +kernel : 2^1023*U≤2^2047).trans full)
  have sub : Icc 1 (2^511)⊆skipped (p*q) a stop := by
    intro x hx
    obtain ⟨positive,short⟩ := mem_Icc.mp hx
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨positive,short.trans long⟩,?_⟩
    rintro ⟨k,kp,lo,_⟩
    have bound := (Nat.pow_le_pow_left short 2).trans (by decide +kernel : ((2:ℕ)^511)^2≤2^1023)
    have low := Nat.le_mul_of_pos_left (lower (p*q)) kp
    unfold lower at low lo
    omega
  simpa only [Nat.card_Icc,Nat.add_sub_cancel] using card_le_card sub

private theorem stop_data {v : ℕ×ℕ} (mem : v∈eligible) {G : ℕ}
    (good : v∉exceptional G) {a stop : ℕ} (target : a∈Icc 1 CircleMarkSmallTargetPopulation.A)
    (neg : jacobiSym a (v.1*v.2)= -1) (start : 0<stop)
    (hit : ¬(v.1*v.2).Coprime (CircleMarkSmallTargetPopulation.magnitude a stop 1)) :
    v.1≤U-G ∧ 2^900<stop := by
  have notNear : v∉near G := fun h => good (mem_union_left _ h)
  have notEarly : v∉CircleMarkSmallTargetPopulation.successful {1} := fun h => good (mem_union_right _ h)
  refine ⟨le_of_not_gt (fun h => notNear (mem_filter.mpr ⟨mem,h⟩)),?_⟩
  by_contra! endPos
  exact notEarly (mem_filter.mpr ⟨mem,a,target,stop,mem_Icc.mpr ⟨start,endPos⟩,1,mem_singleton_self 1,neg,hit⟩)

/-- For every allowed target and every positive marked stop (including the first),
the raw band's discarded coordinates account for less than 2^-376 of 1,…,stop. -/
theorem far_fraction {v : ℕ×ℕ} (mem : v∈eligible) (good : v∉exceptional (2^1000))
    {a stop : ℕ} (target : a∈Icc 1 CircleMarkSmallTargetPopulation.A)
    (neg : jacobiSym a (v.1*v.2)= -1) (start : 0<stop)
    (hit : ¬(v.1*v.2).Coprime (CircleMarkSmallTargetPopulation.magnitude a stop 1)) :
    2^376*(skipped (v.1*v.2) a stop).card<stop := by
  obtain ⟨sep,late⟩ := stop_data mem good target neg start hit
  have cap := Nat.mul_le_mul_left (2^376) (far_count mem sep (mem_Icc.mp target).2 stop)
  exact (cap.trans (by decide +kernel : 2^376*(2^524-1)≤2^900)).trans_lt late

/-- Outside the much smaller 2^-85 population exception, the corresponding
relative saving is less than 2^-360. -/
theorem broad_fraction {v : ℕ×ℕ} (mem : v∈eligible) (good : v∉exceptional (2^968))
    {a stop : ℕ} (target : a∈Icc 1 CircleMarkSmallTargetPopulation.A)
    (neg : jacobiSym a (v.1*v.2)= -1) (start : 0<stop)
    (hit : ¬(v.1*v.2).Coprime (CircleMarkSmallTargetPopulation.magnitude a stop 1)) :
    2^360*(skipped (v.1*v.2) a stop).card<stop := by
  obtain ⟨sep,late⟩ := stop_data mem good target neg start hit
  have cap := Nat.mul_le_mul_left (2^360) (broad_count mem sep (mem_Icc.mp target).2 stop)
  exact (cap.trans (by decide +kernel : 2^360*(2^540-1)≤2^900)).trans_lt late

end PrimeFactors.CircleMarkBandSavings
