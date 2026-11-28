import PrimeFactors.BinaryRotationModulus
import PrimeFactors.BinaryRotationPopulation
import PrimeFactors.RotationSquareRootCount
import PrimeFactors.FullWidthTransposedFixture

/-! The size of a modular square-root class at the public 1,024-bit word
width. The counts are cardinalities of residue classes. They make no
assumption about the distribution of products of actual primes. -/
namespace PrimeFactors.FullWidthRotationRoots

open BinaryRotationModulus BinaryRotationProduct RotationSquareRootCount

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

theorem factors_odd (p : ℕ) (hp : p∈factors) : p.Prime ∧ p≠2 := by
  exact ⟨exactFactors.2 p hp, fun h => (by decide +kernel : 2∉factors) (h ▸ hp)⟩

theorem factors_coprime : factors.Pairwise Nat.Coprime := by decide +kernel

private theorem below (p : ℕ) (hp : p∈factors) : p<2^1023 := by
  have all : factors.all (fun q => decide (q<2^1023))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all p hp)

/-- Every prime as large as a 1,024-bit prime is a unit at this public modulus. -/
theorem prime_unit {p : ℕ} (prime : p.Prime) (lo : 2^1023≤p) : p.Coprime M := by
  apply prime.coprime_iff_not_dvd.mpr
  intro dvd
  exact (Nat.not_lt_of_ge lo) (below _ ((prime_divisors p).mp ⟨prime,dvd⟩))

theorem phase_unit {N : ℕ} (unit : N.Coprime M) (r : ℕ) : (2^r*N).Coprime M :=
  Nat.coprime_mul_iff_left.mpr ⟨(by decide +kernel : Nat.Coprime 2 M).pow_left r,unit⟩

private theorem word_modulus : modulus 1024=M := rfl

private theorem word_roots (N r : ℕ) : roots 1024 N r=residues M (2^r*N) := rfl

attribute [local irreducible] M factors

theorem roots_card {N r : ℕ} (unit : N.Coprime M) (hit : (roots 1024 N r).Nonempty) :
    (roots 1024 N r).card=65536 := by
  obtain ⟨y,hy⟩ := hit
  have eqn := (mem_roots.mp hy).2
  rw [word_modulus] at eqn
  have u := phase_unit unit r
  rw [←exactFactors.1] at u eqn
  have cnt := list_count factors_odd factors_coprime u eqn
  rw [exactFactors.1,size] at cnt
  rw [word_roots]
  exact cnt

theorem zero_or_full {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (r : ℕ) :
    (roots 1024 (p*q) r).card=0 ∨ (roots 1024 (p*q) r).card=65536 := by
  rcases (roots 1024 (p*q) r).eq_empty_or_nonempty with h|h
  · exact Or.inl (Finset.card_eq_zero.mpr h)
  · exact Or.inr (roots_card (Nat.coprime_mul_iff_left.mpr ⟨prime_unit pp pl,prime_unit qp ql⟩) h)

/-- A true rotation supplies a member of the appropriate residue class. -/
theorem actual {p q j : ℕ} (unit : (p*q).Coprime M) (turn : q=rotate 1024 j p) :
    (roots 1024 (p*q) (j%2)).card=65536 := by
  apply roots_card unit
  let x := 2^(half j)*p
  refine ⟨x%(modulus 1024), mem_roots.mpr ⟨Nat.mod_lt _ (by decide +kernel),?_⟩⟩
  exact ((Nat.mod_modEq ..).pow 2).trans (target (by decide) turn)

open FullWidthTransposedFixture in
/-- For the planted two-block fixture the 65,536 residues occur in the even
phase. Modulo three rules out every residue in the other phase. -/
theorem planted : (roots 1024 N 0).card=65536 ∧ roots 1024 N 1=∅ := by
  have turn : q=rotate 1024 512 p := by decide +kernel
  have lo := data.2
  have u := Nat.coprime_mul_iff_left.mpr
    ⟨prime_unit p_prime lo.1,prime_unit q_prime (lo.1.trans lo.2.1.le)⟩
  refine ⟨?_,BinaryRotationPopulation.wrong_roots (by decide) (by decide +kernel) (by decide +kernel)⟩
  simpa only [product] using actual u turn

/-- A six-bit prime pair passes the modular test even though no rotation can
produce its factors. This distinguishes square residuosity from rotation. -/
theorem false_positive : Nat.Prime 41 ∧ Nat.Prime 59 ∧ 41*59=2419 ∧
    roots 6 2419 0={5,23,40,58} ∧ allPairs 6 2419=∅ := by decide +kernel

end PrimeFactors.FullWidthRotationRoots
