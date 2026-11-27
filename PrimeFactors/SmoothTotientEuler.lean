import PrimeFactors.SmoothOrderTail

/-! An outward-rounded Euler-product bound for primes up to 1500.
Each integer root used below is checked by a fourth-power inequality. -/
namespace PrimeFactors.SmoothTotientEuler
open Finset
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Each step tentatively sets one more binary digit of the lower bound. -/
private def narrow (t lo : ℕ) : ℕ → ℕ
  | 0 => lo
  | k+1 =>
    let next := lo+2^k
    narrow t (if next^4≤t then next else lo) k

private theorem narrow_bounds (t lo k : ℕ) (start : lo^4≤t) :
    lo≤narrow t lo k ∧ (narrow t lo k)^4≤t := by
  induction k generalizing lo with
  | zero => exact ⟨le_rfl,start⟩
  | succ k ih =>
    simp only [narrow]
    split
    next h =>
      obtain ⟨a,b⟩ := ih _ h
      exact ⟨(Nat.le_add_right ..).trans a,b⟩
    next => exact ih _ start

private def root (p : ℕ) : ℕ := narrow (64^4*p) 65 9

/-- Blocks of 64 integers keep kernel evaluation of the finite product shallow. -/
private noncomputable def block (i : ℕ) : Finset ℕ :=
  ((range 64).filter fun j => 64*i+j<1501 ∧ SharedSmoothPowers.trialPrime 38 (64*i+j)).image (64*i+·)

private theorem mem_block {p i : ℕ} :
    p∈block i ↔ 64*i≤p ∧ p<64*i+64 ∧ p<1501 ∧ p.Prime := by
  simp only [block,mem_image,mem_filter,mem_range,SharedSmoothPowers.trialPrime_eq,decide_eq_true_eq]
  constructor
  · rintro ⟨j,⟨h,below,prime⟩,rfl⟩
    exact ⟨by omega,by omega,below,prime⟩
  · rintro ⟨lo,hi,below,prime⟩
    have eq : 64*i+(p-64*i)=p := Nat.add_sub_of_le lo
    exact ⟨p-64*i,⟨by omega,by rwa [eq],by rwa [eq]⟩,eq⟩

private noncomputable def primes := (range 24).biUnion block

private theorem primes_eq : primes=(1501:ℕ).primesBelow := by
  ext p
  rw [primes,mem_biUnion,Nat.mem_primesBelow]
  constructor
  · rintro ⟨i,_,hi⟩
    exact (mem_block.mp hi).2.2
  · rintro ⟨below,prime⟩
    exact ⟨p/64,mem_range.mpr (by omega),mem_block.mpr ⟨by omega,by omega,below,prime⟩⟩

private theorem parts (f : ℕ → ℕ) :
    ∏ p∈primes, f p = ∏ i∈range 24, ∏ p∈block i, f p := by
  apply Finset.prod_biUnion
  intro i _ j _ ne
  apply disjoint_left.mpr
  intro p hi hj
  have a := mem_block.mp hi
  have b := mem_block.mp hj
  omega

attribute [local irreducible] primes block

private theorem prime_of_mem {p : ℕ} (hp : p∈primes) : p.Prime := by
  unfold primes at hp
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hp
  exact (mem_block.mp hi).2.2.2

private theorem bounds {p : ℕ} (hp : p∈primes) :
    64<root p ∧ root p^4≤64^4*p := by
  have start : 65^4≤64^4*p := (by decide : 65^4≤64^4*2).trans
    (Nat.mul_le_mul_left _ (prime_of_mem hp).two_le)
  exact narrow_bounds _ _ _ start

private theorem product_check :
    (∏ p∈primes, root p) ≤ 2^94 * (∏ p∈primes, (root p-64)) := by
  calc
    _ = ∏ i∈range 24, ∏ p∈block i, root p := parts root
    _ ≤ 2^94 * (∏ i∈range 24, ∏ p∈block i, (root p-64)) := by decide +kernel
    _ = _ := congrArg (2^94*·) (parts (fun p => root p-64)).symm

private theorem geometric {p a : ℕ} (big : 64<a) (rounded : a^4≤64^4*p) :
    (1-(p:ℝ)^(-(1/4:ℝ)))⁻¹ ≤ (a:ℝ)/(a-64:ℕ) := by
  let x := (p:ℝ)^(1/4:ℝ)
  have px : x^4=p := by
    dsimp only [x]
    rw [←Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    norm_num
  have ax : (a:ℝ)≤64*x := by
    apply le_of_pow_le_pow_left₀ (by decide : 4≠0)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    rw [mul_pow,px]
    exact_mod_cast rounded
  have ar : (64:ℝ)<a := by exact_mod_cast big
  have xp : 1<x := by linarith
  have dp : 0<(a:ℝ)-64 := by linarith
  rw [Nat.cast_sub big.le, Nat.cast_ofNat, Real.rpow_neg (Nat.cast_nonneg p)]
  change (1-x⁻¹)⁻¹ ≤ (a:ℝ)/(a-64)
  rw [show 1-x⁻¹=(x-1)/x by field_simp,inv_div,
    div_le_div_iff₀ (by linarith) dp]
  nlinarith only [ax]

/-- The finite Euler product is less than the rational majorant obtained
by replacing each fourth root by a multiple of 1/64 rounded down. -/
theorem euler_1500 :
    (∏ p∈(1501:ℕ).primesBelow, (1-(p:ℝ)^(-(1/4:ℝ)))⁻¹) ≤ (2:ℝ)^94 := by
  rw [←primes_eq]
  have den : 0 < ∏ p∈primes, ((root p-64:ℕ):ℝ) :=
    prod_pos fun p hp => Nat.cast_pos.mpr (Nat.sub_pos_of_lt (bounds hp).1)
  calc
    _ ≤ ∏ p∈primes, ((root p:ℝ)/(root p-64:ℕ)) := by
      apply prod_le_prod
      · intro p hp
        have pp : (1:ℝ)<p := by exact_mod_cast (prime_of_mem hp).one_lt
        exact inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg pp (by norm_num)).le)
      · exact fun p hp => geometric (bounds hp).1 (bounds hp).2
    _ ≤ _ := by
      rw [prod_div_distrib,div_le_iff₀ den]
      exact_mod_cast product_check

end PrimeFactors.SmoothTotientEuler
