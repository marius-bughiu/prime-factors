import PrimeFactors.FractionalMatchedDivisors
import Mathlib.NumberTheory.Primorial

/-! A congruence cover supplies a small prime divisor of every noncentral lift
in the range permitted by the balance tests. A candidate product coprime
to those primes therefore equals the original product. -/

namespace PrimeFactors.FractionalRoughMatchedPairs

private theorem prime_dvd_primorial {p B : ℕ} (hp : p.Prime) (small : p ≤ B) :
    (p : ℤ) ∣ (primorial B : ℤ) := by
  apply Int.natCast_dvd_natCast.mpr
  exact Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le small), hp⟩)

/-- If m agrees with N modulo the primorial of H+1, every term except the
central term and index −2 is covered by a prime through H+1.  The additional
congruence 2m ≡ N modulo the prime r covers −2 as well. -/
theorem progression_cover {n m : ℤ} {H r : ℕ} (pos : 1 ≤ H) (hr : r.Prime)
    (wheel : m ≡ n [ZMOD (primorial (H+1) : ℤ)]) (extra : 2*m ≡ n [ZMOD (r : ℤ)])
    {j : ℤ} (low : -(H : ℤ) ≤ j) (high : j ≤ H) (nonzero : j ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ (p ≤ H+1 ∨ p=r) ∧ (p : ℤ) ∣ n+j*m := by
  by_cases first : j = -1
  · subst j
    have two : 2 ≤ H+1 := by omega
    refine ⟨2, Nat.prime_two, Or.inl two, ?_⟩
    simpa only [neg_one_mul, sub_eq_add_neg] using
      ((prime_dvd_primorial Nat.prime_two two).trans wheel.dvd)
  by_cases second : j = -2
  · subst j
    exact ⟨r, hr, Or.inr rfl, by convert extra.dvd using 1; ring⟩
  let k := (j+1).natAbs
  have ab : (k : ℤ) = |j+1| := Int.natCast_natAbs _
  have gt : 1 < k := by
    have : (1 : ℤ) < |j+1| := by
      rcases le_total 0 (j+1) with h | h
      · rw [abs_of_nonneg h]; omega
      · rw [abs_of_nonpos h]; omega
    omega
  have bound : k ≤ H+1 := by
    have : |j+1| ≤ (H : ℤ)+1 := abs_le.mpr ⟨by omega, by omega⟩
    omega
  let p := k.minFac
  have prime : p.Prime := Nat.minFac_prime (by omega)
  have small : p ≤ H+1 := (Nat.minFac_le (by omega : 0 < k)).trans bound
  have div : (p : ℤ) ∣ j+1 :=
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd k))
  refine ⟨p, prime, Or.inl small, Int.modEq_zero_iff_dvd.mp ?_⟩
  calc
    n+j*m ≡ m+j*m [ZMOD (p : ℤ)] :=
      (wheel.symm.of_dvd (prime_dvd_primorial prime small)).add_right _
    _ = (j+1)*m := by ring
    _ ≡ 0 [ZMOD (p : ℤ)] := Int.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left div _)

/-- At N=1189 and m=67 the auxiliary prime 5 covers 1055 at j=−2. -/
theorem example_1189 {j : ℤ} (low : -3 ≤ j) (high : j ≤ 3) (nonzero : j ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ (p ≤ 4 ∨ p=5) ∧ (p : ℤ) ∣ 1189+j*67 :=
  progression_cover (H := 3) (by decide) (by decide) (by decide) (by decide) low high nonzero

open Finset FractionalBalancedLifts FractionalMatchedDivisors

/-- The size of the chosen modulus puts every admissible lift in the
range of the supplied congruence cover. -/
theorem covered_indices {n m H : ℕ} (hm : 0<m) (scale : n≤8*(H+1)*m)
    {j : ℤ} (range : InIndexRange n m j) : -(H : ℤ)≤j ∧ j≤H := by
  have mp : 0<(m : ℤ) := by exact_mod_cast hm
  have budget : (n : ℤ)≤8*((H : ℤ)+1)*m := by exact_mod_cast scale
  obtain ⟨l,u⟩ := (index_range_iff hm j).mp range
  unfold liftProduct at l u
  constructor
  · by_contra! bad
    have shift : j≤-((H : ℤ)+1) := by omega
    have mul := mul_le_mul_of_nonneg_right shift mp.le
    have size : 0≤((H : ℤ)+1)*m := by positivity
    nlinarith only [l,budget,mul,size]
  · by_contra! bad
    have shift : (H : ℤ)+1≤j := by omega
    have mul := mul_le_mul_of_nonneg_right shift mp.le
    nlinarith only [u,budget,mul]

/-- A matched pair with product coprime to the public wheel belongs to
the central lift. Neither entry is required to be prime. -/
theorem rough_product {n m H r x y : ℕ} (hm : 0<m) (scale : n≤8*(H+1)*m)
    (pos : 1≤H) (hr : r.Prime)
    (wheel : (m : ℤ) ≡ n [ZMOD (primorial (H+1) : ℤ)])
    (extra : 2*(m : ℤ) ≡ n [ZMOD (r : ℤ)])
    (pair : (x,y) ∈ pairs n m) (rough : (x*y).Coprime (primorial (H+1)*r)) : x*y=n := by
  obtain ⟨j,⟨range,prod⟩,_⟩ := unique_lift hm pair
  have central : j=0 := by
    by_contra off
    obtain ⟨lo,hi⟩ := covered_indices hm scale range
    obtain ⟨a,ha,small,dv⟩ := progression_cover
      pos hr wheel extra lo hi off
    have left : a∣x*y := by
      apply Int.natCast_dvd_natCast.mp
      rw [←prod]
      exact dv
    have right : a∣primorial (H+1)*r := by
      rcases small with bound | rfl
      · have part : a∣primorial (H+1) := Finset.dvd_prod_of_mem id
          (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le bound),ha⟩)
        exact dvd_mul_of_dvd_left part _
      · exact dvd_mul_left _ _
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨a,ha,left,right⟩) rough
  subst j
  simpa only [liftProduct,zero_mul,add_zero,Nat.cast_inj] using prod.symm

/-- Filtering the finite set of matched pairs by a single public
coprimality condition leaves exactly the genuinely balanced semiprime pair. -/
theorem singleton {p q m H r : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p≤q)
    (balance : q<2*p) (wide : q<m) (scale : p*q≤8*(H+1)*m)
    (pos : 1≤H) (hr : r.Prime)
    (wheel : (m : ℤ) ≡ (p*q : ℕ) [ZMOD (primorial (H+1) : ℤ)])
    (extra : 2*(m : ℤ) ≡ (p*q : ℕ) [ZMOD (r : ℤ)])
    (rough : (p*q).Coprime (primorial (H+1)*r)) :
    ((pairs (p*q) m).filter fun z => (z.1*z.2).Coprime (primorial (H+1)*r)) = {(p,q)} := by
  ext ⟨x,y⟩
  rw [mem_filter,mem_singleton]
  constructor
  · rintro ⟨pair,ok⟩
    obtain ⟨_,nontriv,ordered,_,_,_⟩ := mem_filter.mp pair
    have prod := rough_product (hq.pos.trans wide) scale pos hr wheel extra pair ok
    obtain ⟨rfl,rfl⟩ := ordered_semiprime_pair_unique hp hq order ordered nontriv prod
    rfl
  · intro eqn
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eqn
    exact ⟨mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (order.trans_lt wide),mem_range.mpr wide⟩,
      hp.one_lt,order,balance,true_window order balance,Nat.ModEq.refl _⟩,rough⟩

/-- The public roughness check modulo 30 singles out (101,127) at modulus 401. -/
theorem example_12827 :
    ((pairs 12827 401).filter fun z => (z.1*z.2).Coprime 30) = {(101,127)} := by
  exact singleton (p := 101) (q := 127) (m := 401) (H := 3) (r := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end PrimeFactors.FractionalRoughMatchedPairs
