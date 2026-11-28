import PrimeFactors.SquareRootPhasePopulation
import PrimeFactors.BinaryRotationProduct

/-! Product information about the parity of a cyclic shift and unconditional
coverage of all binary shifts on the full-width prime-pair population. -/

namespace PrimeFactors.BinaryRotationPopulation

open Finset MixedPrefixSample BinaryRotationProduct
open scoped Classical
open private PrimeFactors.MixedPrefixSample.mem_sample PrimeFactors.MixedPrefixSample.mem_primes
  from PrimeFactors.MixedPrefixSample

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible primes ordered sample

private theorem even_power (j : ℕ) : (2:ℕ)^(2*j) ≡ 1 [MOD 3] := by
  simpa only [pow_mul, one_pow] using
    (show (2:ℕ)^2 ≡ 1 [MOD 3] by decide).pow j

private theorem power_three (j : ℕ) : (2:ℕ)^j%3 = 1+j%2 := by
  rcases Nat.mod_two_eq_zero_or_one j with h|h
  · have eq : j=2*(j/2) := by omega
    exact (show (2:ℕ)^j%3=1 by simpa only [← eq] using even_power (j/2)).trans (by omega)
  · have eq : j=2*(j/2)+1 := by omega
    have hpow := (even_power (j/2)).mul_right 2
    rw [← pow_succ, ← eq, one_mul] at hpow
    exact (show (2:ℕ)^j%3=2 from hpow).trans (by omega)

private theorem three_dvd {w : ℕ} (width : Even w) : 3∣modulus w := by
  obtain ⟨k,hk⟩ := width
  have we : w=2*k := by omega
  apply (Nat.modEq_iff_dvd' (Nat.one_le_pow w 2 (by decide))).mp
  simpa only [we] using (even_power k).symm

/-- At even width, the wrong one of the two root sets is empty before any
integer-word representatives are tested. -/
theorem wrong_roots {w N r : ℕ} (width : Even w) (unit : ¬3∣N)
    (wrong : N%3 ≠ 1+r%2) : roots w N r=∅ := by
  apply eq_empty_of_forall_not_mem
  intro x member
  have eq := (mem_roots.mp member).2.of_dvd (three_dvd width)
  change x^2%3 = (2^r*N)%3 at eq
  rw [Nat.pow_mod, Nat.mul_mod, power_three] at eq
  have n0 : N%3≠0 := fun h => unit (Nat.dvd_of_mod_eq_zero h)
  rcases (show N%3=1 ∨ N%3=2 by omega) with n|n <;>
    rcases Nat.mod_two_eq_zero_or_one r with e|e <;>
    rcases (show x%3=0 ∨ x%3=1 ∨ x%3=2 by omega) with a|a|a <;>
    norm_num [n,e,a] at eq wrong

/-- For even-width words, the public product modulo three specifies the
parity of every compatible rotation when the first word is coprime to three. -/
theorem product_mod_three {w p q j : ℕ} (hw : 0<w) (width : Even w)
    (unit : ¬3∣p) (turn : q=rotate w j p) : (p*q)%3 = 1+j%2 := by
  have zn : p%3≠0 := fun h => unit (Nat.dvd_of_mod_eq_zero h)
  have square : p*p ≡ 1 [MOD 3] := by
    change (p*p)%3=1
    rw [Nat.mul_mod]
    rcases (show p%3=1 ∨ p%3=2 by omega) with h|h <;> norm_num [h]
  have step : p*q ≡ 2^j [MOD 3] := calc
    p*q ≡ p*(2^j*p) [MOD 3] := by
      rw [turn]
      exact ((rotate_modEq (p:=p) hw j).of_dvd (three_dvd width)).mul_left p
    _ = 2^j*(p*p) := by ring
    _ ≡ 2^j*1 [MOD 3] := square.mul_left _
    _ = 2^j := mul_one _
  exact Eq.trans step (power_three j)

noncomputable def parityShifts (half n : ℕ) : Finset ℕ :=
  if n%3=1 then (Ico 1 half).image (fun j => 2*j)
  else if n%3=2 then (range half).image (fun j => 2*j+1) else ∅

theorem parity_card (half n : ℕ) : (parityShifts half n).card=
    if n%3=1 then half-1 else if n%3=2 then half else 0 := by
  unfold parityShifts
  split
  · rw [card_image_of_injective _ (by intro i j h; dsimp at h; omega), Nat.card_Ico]
  · split
    · rw [card_image_of_injective _ (by intro i j h; dsimp at h; omega), card_range]
    · exact card_empty

private theorem mem_parity {half n j : ℕ} (positive : 0<j) (below : j<2*half)
    (eq : n%3=1+j%2) : j∈parityShifts half n := by
  unfold parityShifts
  split
  · exact mem_image.mpr ⟨j/2, mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
  · split
    · exact mem_image.mpr ⟨j/2, mem_range.mpr (by omega),by omega⟩
    · omega

theorem admissible_shift {half p q j : ℕ} (positive : 0<j) (below : j<2*half)
    (unit : ¬3∣p) (turn : q=rotate (2*half) j p) : j∈parityShifts half (p*q) :=
  mem_parity positive below (product_mod_three (by omega) ⟨half,by omega⟩ unit turn)

theorem full_width_list (n : ℕ) : (parityShifts 512 n).card=
    if n%3=1 then 511 else if n%3=2 then 512 else 0 := parity_card 512 n

/-- Each undirected pair has two different orientations. Both must occur
among the images of the prime-and-shift choices admitted by the row. -/
private theorem incidence (S : Finset (ℕ×ℕ)) (P I : Finset ℕ) (f : ℕ→ℕ→ℕ)
    (row : ∀ z∈S, z.1∈P ∧ z.2∈P ∧ z.1<z.2 ∧
      (∃ i∈I, f i z.1=z.2) ∧ (∃ j∈I, f j z.2=z.1)) :
    2*S.card ≤ P.card*I.card := by
  let V := (P ×ˢ I).image (fun u => (u.1, f u.2 u.1))
  have dis : Disjoint S (S.image Prod.swap) := by
    apply disjoint_left.mpr
    intro x hx hsw
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hsw
    have a := (row y hy).2.2.1
    have b := (row y.swap hx).2.2.1
    exact (Nat.lt_asymm a b)
  have sub : S ∪ S.image Prod.swap ⊆ V := by
    intro x hx
    rcases mem_union.mp hx with forward|reverse
    · obtain ⟨p,_,_,⟨i,hi,eq⟩,_⟩ := row x forward
      exact mem_image.mpr ⟨(x.1,i), mem_product.mpr ⟨p,hi⟩, Prod.ext rfl eq⟩
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp reverse
      obtain ⟨_,q,_,_,j,hj,eq⟩ := row y hy
      exact mem_image.mpr ⟨(y.2,j), mem_product.mpr ⟨q,hj⟩, Prod.ext rfl eq⟩
  have total := (card_le_card sub).trans (show V.card≤(P ×ˢ I).card from card_image_le)
  simpa only [card_union_of_disjoint dis, card_image_of_injective _ Prod.swap_injective,
    card_product, two_mul] using total

noncomputable def family := eligible.filter (fun z =>
  ∃ j∈Ico 1 1024, z.2=rotate 1024 j z.1)

theorem mem_family {z : ℕ×ℕ} : z∈family ↔ z∈eligible ∧
    ∃ j∈Ico 1 1024, z.2=rotate 1024 j z.1 := by simp only [family,mem_filter]

attribute [local irreducible] family rotate

private theorem endpoints {z : ℕ×ℕ} (hz : z∈eligible) :
    z.1∈primes ∧ z.2∈primes ∧ z.1<z.2 := by
  rw [eligible] at hz
  obtain ⟨base,order⟩ := PrimeFactors.MixedPrefixSample.mem_sample.mp hz
  exact ⟨(mem_ordered.mp base).1,(mem_ordered.mp base).2.1,order⟩

private theorem prime_data {p : ℕ} (hp : p∈primes) : p≤modulus 1024 ∧ ¬3∣p := by
  obtain ⟨⟨lo,hi⟩,prime⟩ := PrimeFactors.MixedPrefixSample.mem_primes.mp hp
  have top : 2*X=(2:ℕ)^1024 := by decide +kernel
  have far : 3<X := by decide +kernel
  rw [top] at hi
  refine ⟨by unfold modulus; omega,?_⟩
  intro dvd
  rcases (Nat.dvd_prime prime).mp dvd with h|h <;> omega

private theorem rotations {z : ℕ×ℕ} (hz : z∈family) :
    z.1∈primes ∧ z.2∈primes ∧ z.1<z.2 ∧
    (∃ j∈Ico 1 1024, z.2=rotate 1024 j z.1) ∧
    (∃ j∈Ico 1 1024, z.1=rotate 1024 j z.2) := by
  obtain ⟨member,j,hj,eq⟩ := mem_family.mp hz
  obtain ⟨p,q,lt⟩ := endpoints member
  obtain ⟨low,high⟩ := mem_Ico.mp hj
  refine ⟨p,q,lt,⟨j,hj,eq⟩,1024-j, mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩
  rw [eq, rotate_inverse (by decide) high.le (prime_data p).1]

private theorem incidence_full (S : Finset (ℕ×ℕ)) (P : Finset ℕ) (f : ℕ→ℕ→ℕ)
    (row : ∀ z∈S, z.1∈P ∧ z.2∈P ∧ z.1<z.2 ∧
      (∃ i∈Ico 1 1024, z.2=f i z.1) ∧ (∃ j∈Ico 1 1024, z.1=f j z.2)) :
    2*S.card ≤ 1023*P.card := by
  calc
    _ ≤ P.card*(Ico 1 1024).card := by
      apply incidence _ _ _ f
      intro z hz
      obtain ⟨p,q,lt,⟨i,hi,eq⟩,j,hj,rev⟩ := row z hz
      exact ⟨p,q,lt,⟨i,hi,eq.symm⟩,j,hj,rev.symm⟩
    _ = _ := by rw [Nat.card_Ico, Nat.mul_comm]

theorem count : 2*family.card≤1023*primes.card :=
  incidence_full family primes (rotate 1024) fun _ hz => rotations hz

/-- A sharper count in the numerator when the product's residue modulo
three is fixed. The denominator for the fraction below remains all pairs. -/
theorem residue_count (r : ℕ) :
    2*(family.filter (fun z => (z.1*z.2)%3=r%3)).card ≤
      primes.card*(parityShifts 512 r).card := by
  apply incidence _ _ _ (rotate 1024)
  intro z hz
  obtain ⟨member,suffix⟩ := mem_filter.mp hz
  obtain ⟨p,q,lt,⟨i,hi,eq⟩,j,hj,rev⟩ := rotations member
  obtain ⟨il,iu⟩ := mem_Ico.mp hi
  obtain ⟨jl,ju⟩ := mem_Ico.mp hj
  have iok := admissible_shift (half:=512) il iu (prime_data p).2 eq
  have jok := admissible_shift (half:=512) jl ju (prime_data q).2 rev
  have idem : parityShifts 512 (z.1*z.2) = parityShifts 512 r := by
    unfold parityShifts
    simp only [suffix]
  refine ⟨p,q,lt,⟨i,idem ▸ iok,eq.symm⟩,j,?_,rev.symm⟩
  rw [Nat.mul_comm z.2 z.1, idem] at jok
  exact jok

/-- Coverage of every nontrivial cyclic rotation, over all equally weighted
unordered full-width prime pairs, with no analytic hypothesis. -/
theorem fraction : 2^998*family.card<eligible.card := by
  apply Nat.lt_of_mul_lt_mul_left (a:=41056*1023)
  calc
    _ = (41056*1023*2^998)*family.card := by ring
    _ ≤ (2*X)*family.card := Nat.mul_le_mul_right _ (by decide +kernel)
    _ = X*(2*family.card) := by ring
    _ ≤ X*(1023*primes.card) := Nat.mul_le_mul_left _ count
    _ = 1023*(X*primes.card) := by ring
    _ < 1023*(41056*eligible.card) := Nat.mul_lt_mul_of_pos_left
      SquareRootPhasePopulation.marginal (by decide)
    _ = _ := by ring

end PrimeFactors.BinaryRotationPopulation
