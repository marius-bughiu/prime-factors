import PrimeFactors.PublicPrimeSquareCounts

/-! An auxiliary set of factor-sum residues at six odd prime squares,
coprime to the existing period 100. -/
namespace PrimeFactors.SixSquareAuxiliarySieve

open Finset LocalSumMenu
open private PrimeFactors.PublicPrimeSquareCounts.second_count from PrimeFactors.PublicPrimeSquareCounts

def L : ℕ := 3^2*7^2*11^2*13^2*17^2*19^2

theorem value : L=940839860961 := by decide
instance : NeZero L := ⟨by decide⟩
theorem coprime : Nat.Coprime 100 L := by decide

/-- Attained sum residues modulo L for the supplied product. -/
noncomputable def A (n : ℕ) : Finset (ZMod L) := by
  classical exact univ.filter (AdmissibleSum (n:ZMod L))

theorem mem_A {n : ℕ} {s : ZMod L} : s∈A n ↔ AdmissibleSum (n:ZMod L) s := by
  classical simp only [A,mem_filter,mem_univ,true_and]

/-- The true sum passes for any integer factors represented by naturals. -/
theorem true_sum (p q : ℕ) : ((p+q:ℕ):ZMod L)∈A (p*q) :=
  mem_A.mpr ⟨p,q,(Nat.cast_mul ..).symm,(Nat.cast_add ..).symm⟩

private theorem size (n : ℕ) : (A n).card=count n L := by
  classical
  rw [count,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rfl

private theorem components (n : ℕ) : count n L =
    count n (3^2)*count n (7^2)*count n (11^2)*count n (13^2)*count n (17^2)*count n (19^2) := by
  have crt {a b : ℕ} (c : a.Coprime b) : count n (a*b)=count n a*count n b := card_admissibleSum_crt c n
  simp (disch := decide) only [L,crt]

/-- At most this many of the L sum residues pass, for every unit product. -/
theorem card_bound {n : ℕ} (cop : n.Coprime L) : (A n).card≤6285399120 := by
  have cap {p k : ℕ} (pp : p.Prime) (odd : p≠2) (d : p∣L) (law : ∀ z : Bool,primePowerSumCount p z 2≤k) :
      count n (p^2)≤k := by
    rw [PrimeFactors.PublicPrimeSquareCounts.second_count pp odd
      (pp.coprime_iff_not_dvd.mp (cop.of_dvd_right d).symm)]
    exact law _
  rw [size,components]
  change _ ≤ 3*21*55*78*136*171
  gcongr <;> exact cap (by decide) (by decide) (by decide) (by decide +kernel)

/-- The upper bound is attained. The unit 41 is a quadratic nonresidue
at each of the six primes. -/
theorem sharp : Nat.Coprime 41 L ∧ (A 41).card=6285399120 := by
  refine ⟨by decide,?_⟩
  have at_prime {p k : ℕ} [NeZero p] (pp : p.Prime) (odd : p≠2) (nd : ¬p∣41)
      (law : primePowerSumCount p (decide (∃ x : ZMod p,x*x=(41:ZMod p))) 2=k) :
      count 41 (p^2)=k := (PrimeFactors.PublicPrimeSquareCounts.second_count pp odd nd).trans law
  rw [size,components,
    at_prime (p:=3) (k:=3) (by decide) (by decide) (by decide) (by decide +kernel),
    at_prime (p:=7) (k:=21) (by decide) (by decide) (by decide) (by decide +kernel),
    at_prime (p:=11) (k:=55) (by decide) (by decide) (by decide) (by decide +kernel),
    at_prime (p:=13) (k:=78) (by decide) (by decide) (by decide) (by decide +kernel),
    at_prime (p:=17) (k:=136) (by decide) (by decide) (by decide) (by decide +kernel),
    at_prime (p:=19) (k:=171) (by decide) (by decide) (by decide) (by decide +kernel)]

end PrimeFactors.SixSquareAuxiliarySieve
