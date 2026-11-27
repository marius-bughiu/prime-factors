import PrimeFactors.RectangularFullWidth

/-! A lower bound for the number of DISTINCT integers actually yielded
by the coprime weight-product scanner on a complete traversal. -/
namespace PrimeFactors.RectangularSearchFloor

open Finset RectangularFullWidth

set_option exponentiation.threshold 4096

/-- Python's range(first,last+1,2), with the gcd gate, at fixed a and
multiplier t. Taking the image discards any repetition. -/
private noncomputable def lane (K scale e t a first : ℕ) : Finset ℕ :=
  let last := min (K/(t*a)) ((scale+e)*a/scale)
  ((Icc first last).filter (fun b => (b-first)%2=0 ∧ a.Coprime b)).image (fun b => t*a*b)

/-- The distinct elements of the merged odd and even scanner streams.
Both the product cutoff and the rounded ratio are applied in each lane. -/
noncomputable def emitted (K scale e : ℕ) : Finset ℕ :=
  (((Icc 1 K.sqrt).filter (fun a => a%2=1)).biUnion (fun a => lane K scale e 1 a a)) ∪
    ((Icc 1 (K/4).sqrt).biUnion (fun a => lane K scale e 4 a (a+1)))

/-- Two unequal possible factors bounded by U have product strictly
below U². Positive sqrt(N) makes the unrounded ratio strictly above 1. -/
theorem positive_excess {p q : ℕ} (lt : p<q) (qu : q<2^1024)
    (lo : 2^2047≤p*q) (hi : p*q<2^2048) : 1≤excess (p*q) := by
  let N := p*q
  obtain ⟨_,_,_,_,_,_,ss⟩ := dimensions lo hi
  have sp : 0<N.sqrt := by dsimp [N]; omega
  have cap : q≤upperPrime := by dsimp [upperPrime]; omega
  have smaller : N<upperPrime^2 := calc
    N < q*q := Nat.mul_lt_mul_of_pos_right lt (by omega)
    _ = q^2 := by ring
    _ ≤ upperPrime^2 := Nat.pow_le_pow_left cap 2
  have strict : N*(N.sqrt-H N)<upperPrime^2*(N.sqrt+H N) := calc
    _ ≤ N*N.sqrt := Nat.mul_le_mul_left _ (Nat.sub_le ..)
    _ < upperPrime^2*N.sqrt := Nat.mul_lt_mul_of_pos_right smaller sp
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have ratio := (excess_bound lo hi).2
  change 1024*(upperPrime^2*(N.sqrt+H N))≤(1024+excess N)*(N*(N.sqrt-H N)) at ratio
  by_contra! bad
  have zero : excess N=0 := by change excess N<1 at bad; omega
  rw [zero,Nat.add_zero] at ratio
  exact (not_le_of_gt strict) (Nat.le_of_mul_le_mul_left ratio (by decide))

/-- Consecutive odd weights have gcd one. The second weight appears
precisely one step beyond the first in its odd scanner lane. -/
theorem odd_pair_emitted {a K e : ℕ} (odd : Odd a) (low : 2048≤a)
    (large : (a+2)^2≤K) (positive : 1≤e) : a*(a+2)∈emitted K 1024 e := by
  have ap : 0<a := by omega
  have fit : a*(a+2)≤K := (Nat.mul_le_mul_right (a+2) (show a≤a+2 by omega)).trans
    (by simpa only [pow_two] using large)
  have den : a+2≤K/a := (Nat.le_div_iff_mul_le ap).mpr (by simpa only [mul_comm] using fit)
  have bound : a+2≤(1024+e)*a/1024 := by
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    have ea : a≤e*a := by simpa only [one_mul] using Nat.mul_le_mul_right a positive
    nlinarith only [low,ea]
  have sa : a≤K.sqrt := (show a≤a+2 by omega).trans (Nat.le_sqrt.mpr
    (by simpa only [pow_two] using large))
  have cop : a.Coprime (a+2) := Nat.coprime_self_add_right.mpr (Nat.coprime_two_right.mpr odd)
  apply mem_union_left
  apply mem_biUnion.mpr
  refine ⟨a,mem_filter.mpr ⟨mem_Icc.mpr ⟨ap,sa⟩,Nat.odd_iff.mp odd⟩,?_⟩
  apply mem_image.mpr
  refine ⟨a+2,mem_filter.mpr ⟨?_,by simpa using cop⟩,by simp⟩
  exact mem_Icc.mpr ⟨by omega,le_min (by simpa using den) bound⟩

def weight (i : ℕ) := 2049+2*i
def entry (i : ℕ) := weight i*(weight i+2)
def familySize : ℕ := 2^339-1025

theorem increasing : StrictMono entry := by
  intro i j lt
  have inc : weight i<weight j := by dsimp [weight]; omega
  exact (Nat.mul_lt_mul_of_pos_right inc (by omega : 0<weight i+2)).trans_le
    (Nat.mul_le_mul_left (weight j) (by omega))

theorem accepted {N : ℕ} (kl : 2^680≤K N) (ep : 1≤excess N) (i : Fin familySize) :
    entry i ∈ emitted (K N) 1024 (excess N) := by
  have small : weight i+2≤2^340 := by
    have h := i.isLt
    dsimp [weight,familySize] at *
    omega
  apply odd_pair_emitted (Nat.odd_iff.mpr (by dsimp [weight]; omega))
    (by dsimp [weight]; omega) _ ep
  exact (Nat.pow_le_pow_left small 2).trans (by omega)

/-- A closed, injective map into actual yielded products; collisions
between other representations do not remove any of these values. -/
noncomputable def embedding {N : ℕ} (kl : 2^680≤K N) (ep : 1≤excess N) :
    Fin familySize ↪ ↥(emitted (K N) 1024 (excess N)) where
  toFun i := ⟨entry i,accepted kl ep i⟩
  inj' := fun _ _ h => Fin.ext (increasing.injective (congrArg Subtype.val h))

/-- The bound holds even without primality; every product of two distinct
1024-bit primes with a 2048-bit product satisfies these hypotheses. -/
theorem full_width {p q : ℕ} (lt : p<q) (qu : q<2^1024)
    (lo : 2^2047≤p*q) (hi : p*q<2^2048) :
    2^339-1025 ≤ (emitted (K (p*q)) 1024 (excess (p*q))).card := by
  have kl := (dimensions lo hi).2.2.2.2.2.1
  have inject := embedding kl (positive_excess lt qu lo hi)
  simpa only [Fintype.card_fin,Fintype.card_coe,familySize] using Fintype.card_le_of_embedding inject

end PrimeFactors.RectangularSearchFloor
