import PrimeFactors.FloorSquareShiftPopulation

/-!
# A restriction on the one-gcd prediction across all lower centers

The searched quantity is the entire power of two in N−s². A single center
may be chosen after seeing the product, or all nonnegative centers through
the floor square root may be granted. The argument includes a zero remainder.
-/

namespace PrimeFactors.FloorShiftDyadicCenters

open Finset FloorSquareShift
open private PrimeFactors.FloorSquareShift.floor_bounds from PrimeFactors.FloorSquareShift

def proposed (N s : ℕ) := 2*s+twoPart (N-s^2)

/-- At zero the gcd convention returns 1, which divides zero. -/
theorem power_divisor (D : ℕ) : ∃ j, twoPart D=2^j ∧ twoPart D∣D := by
  by_cases zero : D=0
  · subst D
    exact ⟨0,by simp [twoPart],dvd_zero _⟩
  obtain ⟨j,m,odd,eqn⟩ := Nat.exists_eq_two_pow_mul_odd zero
  rw [eqn,mul_comm (2^j) m,twoPart_odd_mul _ odd]
  exact ⟨j,rfl,dvd_mul_left ..⟩

/-- This necessary bound even permits proposing a smaller dyadic divisor of the remainder. -/
theorem odd_gap_bound {p q s j v g H : ℕ} (ord : p<q) (hi : q≤H)
    (center : s≤(p*q).sqrt) (sum : p+q=2*s+2^j) (dv : 2^j∣p*q-s^2)
    (gap : q-p=2^v*g) (odd : Odd g) : g^2≤4*H := by
  have sq : s^2≤p*q := (Nat.pow_le_pow_left center 2).trans (Nat.sqrt_le' _)
  have eqn : (q-p)^2+4*(p*q-s^2)=2^j*(p+q+2*s) := by
    zify [ord.le,sq]
    have eqZ : (p:ℤ)+q=2*s+2^j := by exact_mod_cast sum
    linear_combination ((p:ℤ)+q+2*s)*eqZ
  have dvd : 2^j∣(q-p)^2 := by
    apply (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right dv 4)).mpr
    rw [eqn]
    exact dvd_mul_right ..
  rw [gap,mul_pow] at dvd
  have dPow : 2^j∣(2^v)^2 := ((odd.coprime_two_left.pow_left j).pow_right 2).dvd_of_dvd_mul_right dvd
  have pos : 0<(2^v)^2 := by positivity
  have small := Nat.le_of_dvd pos dPow
  have sh := (center.trans (PrimeFactors.FloorSquareShift.floor_bounds ord).2.1).trans hi
  have size : p+q+2*s≤4*H := by omega
  have bound : (2^v)^2*g^2≤(2^v)^2*(4*H) := calc
    _ = (q-p)^2 := by rw [gap,mul_pow]
    _ ≤ 2^j*(p+q+2*s) := by omega
    _ ≤ _ := Nat.mul_le_mul small size
  exact Nat.le_of_mul_le_mul_left bound pos

theorem proposed_bound {p q s v g H : ℕ} (ord : p<q) (hi : q≤H)
    (center : s≤(p*q).sqrt) (hit : proposed (p*q) s=p+q)
    (gap : q-p=2^v*g) (odd : Odd g) : g^2≤4*H := by
  obtain ⟨j,hj,dv⟩ := power_divisor (p*q-s^2)
  rw [proposed,hj] at hit
  rw [hj] at dv
  exact odd_gap_bound ord hi center hit.symm dv gap odd

private noncomputable def cover (H b : ℕ) : Finset (ℕ×ℕ) :=
  ((Icc 1 H) ×ˢ ((range b) ×ˢ (Icc 1 (4*H).sqrt))).image fun w =>
    (w.1,w.1+2^w.2.1*w.2.2)

/-- An arbitrary choice of a power of two dividing the remainder, at any
center in the full interval. Only pairs with the correct predicted sum are counted. -/
theorem finite_count (P : Finset (ℕ×ℕ)) {H b : ℕ} (bits : H≤2^b)
    (valid : ∀ z∈P, 0<z.1 ∧ z.1<z.2 ∧ z.2≤H ∧
      ∃ s j, s≤(z.1*z.2).sqrt ∧ z.1+z.2=2*s+2^j ∧ 2^j∣z.1*z.2-s^2) :
    P.card≤H*b*(4*H).sqrt := by
  have sub : P⊆cover H b := by
    rintro ⟨p,q⟩ hv
    obtain ⟨pp,ord,hi,s,j,hs,sum,dv⟩ := valid _ hv
    obtain ⟨v,g,odd,gap⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.sub_pos_of_lt ord).ne'
    have gpos : 0<g := by obtain ⟨k,hk⟩ := odd; omega
    have gbound := Nat.le_sqrt'.mpr (odd_gap_bound ord hi hs sum dv gap odd)
    have vbound : v<b := by
      apply (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
      have powle := Nat.le_mul_of_pos_right (2^v) gpos
      omega
    exact mem_image.mpr ⟨(p,v,g),mem_product.mpr ⟨mem_Icc.mpr ⟨pp,ord.le.trans hi⟩,
      mem_product.mpr ⟨mem_range.mpr vbound,mem_Icc.mpr ⟨gpos,gbound⟩⟩⟩,
      Prod.ext rfl (by dsimp; omega)⟩
  exact (card_le_card sub).trans (card_image_le.trans_eq (by
    simp only [card_product,Nat.card_Icc,Nat.add_sub_cancel,card_range,Nat.mul_assoc]))

open MixedPrefixSample
open private PrimeFactors.MonotoneSumPopulation.data from PrimeFactors.MonotoneSumPopulation
open private PrimeFactors.MixedPrefixSample.mem_sample PrimeFactors.MixedPrefixSample.mem_primes
  from PrimeFactors.MixedPrefixSample

attribute [local irreducible] eligible MixedPrefixSample.primes
set_option exponentiation.threshold 4096

noncomputable def successes : Finset (ℕ×ℕ) := by
  classical
  exact eligible.filter fun z => ∃ s j, s≤(z.1*z.2).sqrt ∧
    z.1+z.2=2*s+2^j ∧ 2^j∣z.1*z.2-s^2

theorem mem_of_reading {p q s : ℕ} (ok : (p,q)∈eligible) (hs : s≤(p*q).sqrt)
    (hit : proposed (p*q) s=p+q) : (p,q)∈successes := by
  classical
  obtain ⟨j,eqn,dv⟩ := power_divisor (p*q-s^2)
  rw [proposed,eqn] at hit
  exact mem_filter.mpr ⟨ok,s,j,hs,hit.symm,eqn ▸ dv⟩

theorem full_width : 2^474*successes.card<eligible.card := by
  classical
  have count := finite_count successes (H:=2^1024) (b:=1024) le_rfl (by
    rintro ⟨p,q⟩ hv
    obtain ⟨mem,data⟩ := mem_filter.mp hv
    obtain ⟨ord,hi⟩ := PrimeFactors.MonotoneSumPopulation.data mem
    rw [eligible] at mem
    have pm := (mem_ordered.mp (PrimeFactors.MixedPrefixSample.mem_sample.mp mem).1).1
    have pp := (PrimeFactors.MixedPrefixSample.mem_primes.mp pm).2.pos
    exact ⟨pp,ord,hi.le,data⟩)
  have rt : (4*2^1024:ℕ).sqrt=2^513 := by
    rw [show (4*2^1024:ℕ)=2^513*2^513 by decide +kernel,Nat.sqrt_eq]
  rw [rt] at count
  have room : 21000000*(2^474*(2^1024*1024*2^513))≤(2:ℕ)^2046 := by decide +kernel
  exact Nat.lt_of_mul_lt_mul_left ((Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left _ count)).trans_lt
    (room.trans_lt ChebyshevPrimeSample.eligible_count))

end PrimeFactors.FloorShiftDyadicCenters
