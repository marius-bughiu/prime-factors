import PrimeFactors.SquarePrimeDecoys
import PrimeFactors.ChebyshevQuarticScale

/-! Count distinct composite candidates in the full factor interval that
survive an arbitrary fixed list of affine Jacobi tests. The prime-counting
estimate is the explicitly named Dusart hypothesis. -/

namespace PrimeFactors.FullSizeSquareDecoys
open Finset
open WeightedCrowdingEstimates (Dusart)
set_option exponentiation.threshold 8192

/-- Only nonprime squares of primes coprime to the wheel are counted. The
Jacobi numerator uses signed subtraction, including at draw zero. -/
noncomputable def survivingSquares (N lo hi : ℕ) (draws : List ℕ) : Finset ℕ := by
  classical
  exact (Icc lo hi).filter fun x => (∃ p : ℕ, p.Prime ∧ p^2 = x) ∧ ¬ x.Prime ∧
    x.Coprime 60 ∧ ∀ r ∈ draws, jacobiSym (1-4*(N : ℤ)*r) x = 1

theorem mem_survivingSquares {N lo hi x : ℕ} {draws : List ℕ} :
    x ∈ survivingSquares N lo hi draws ↔ (lo ≤ x ∧ x ≤ hi) ∧
      (∃ p : ℕ, p.Prime ∧ p^2 = x) ∧ ¬ x.Prime ∧ x.Coprime 60 ∧
      ∀ r ∈ draws, jacobiSym (1-4*(N : ℤ)*r) x = 1 := by
  classical
  simp only [survivingSquares, mem_filter, mem_Icc]

/-- Every bounded list, including repeated draws, leaves more than 2^498
distinct nonprime candidates if the physical interval contains the indicated
prime squares. The upper estimate of eight exceptional bases per draw counts
even overlaps repeatedly. -/
theorem count {N a b lo hi : ℕ} (draws : List ℕ) (len : draws.length = 1100)
    (draw : ∀ r ∈ draws, r < N) (size : N < 2^2048) (low : 2^511 ≤ a)
    (ab : a ≤ b) (high : b ≤ 2^512) (placeLo : lo ≤ (a+1)^2) (placeHi : b^2 ≤ hi)
    (room : 355*a+355*353*(2^498+8800) < 353*b) (du : Dusart) :
    2^498 < (survivingSquares N lo hi draws).card := by
  classical
  let P := (Ioc a b).filter Nat.Prime
  let z (i : Fin draws.length) : ℤ := 1-4*(N : ℤ)*(draws.get i)
  have bases (p : ℕ) (hp : p ∈ P) : p.Prime ∧ 2^511 ≤ p := by
    obtain ⟨w,prime⟩ := mem_filter.mp hp
    exact ⟨prime,low.trans (mem_Ioc.mp w).1.le⟩
  have available : 2^498+8800 < P.card := SquarePrimeDecoys.base_count low ab high room du
  have remain := SquarePrimeDecoys.square_survivors z P
    (fun i => SquarePrimeDecoys.affine_size size (draw _ (List.get_mem draws i))) bases
  have incl : ((P.filter fun p => ∀ i, jacobiSym (z i) (p^2) = 1).image (fun p => p^2)) ⊆
      survivingSquares N lo hi draws := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
    obtain ⟨hp,pass⟩ := mem_filter.mp hp
    obtain ⟨prime,pbig⟩ := bases p hp
    have bounds := mem_Ioc.mp (mem_filter.mp hp).1
    have wunit : p.Coprime 60 := prime.coprime_iff_not_dvd.mpr (by
      intro hd
      have small := Nat.le_of_dvd (by decide : 0 < 60) hd
      have huge : 60 < 2^511 := by decide +kernel
      omega)
    apply mem_survivingSquares.mpr
    refine ⟨⟨placeLo.trans (Nat.pow_le_pow_left bounds.1 2),
      (Nat.pow_le_pow_left bounds.2 2).trans placeHi⟩,⟨p,prime,rfl⟩,
      Nat.Prime.not_prime_pow (by decide),wunit.pow_left 2,?_⟩
    intro r hr
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
    exact pass i
  have actual := card_le_card incl
  have loss : 8*draws.length = 8800 := by omega
  rw [loss] at remain
  omega

/-- The complete feasible interval for the smaller factor when both factors
are below 2^1024. -/
def physicalLower (N : ℕ) : ℕ := (N-1)/(2^1024-1)+1

/-- Check an entire band of squares by integer endpoint inequalities. The
upper endpoint is the exact square root bound in the search definition. -/
private theorem control {N a b : ℕ} (draws : List ℕ) (len : draws.length = 1100)
    (draw : ∀ r ∈ draws, r < N) (size : N < 2^2048) (low : 2^511 ≤ a)
    (ab : a ≤ b) (high : b ≤ 2^512) (placeLo : physicalLower N ≤ (a+1)^2)
    (placeHi : (b^2)*(b^2) ≤ N) (room : 355*a+355*353*(2^498+8800) < 353*b)
    (du : Dusart) : 2^498 < (survivingSquares N (physicalLower N) N.sqrt draws).card :=
  count draws len draw size low ab high placeLo (Nat.le_sqrt.mpr placeHi) room du

/-- Every 1100-draw list on the fresh input leaves these composite candidates
inside the exact search interval. -/
theorem fresh (draws : List ℕ) (len : draws.length = 1100)
    (draw : ∀ r ∈ draws, r < ChebyshevQuarticScale.fresh) (du : Dusart) :
    2^498 < (survivingSquares ChebyshevQuarticScale.fresh
      (physicalLower ChebyshevQuarticScale.fresh) ChebyshevQuarticScale.fresh.sqrt draws).card :=
  control (a := 57*2^506) (b := 59*2^506) draws len draw
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) du

/-- The crossed input uses a different verified band in the same physical interval. -/
theorem crossed (draws : List ℕ) (len : draws.length = 1100)
    (draw : ∀ r ∈ draws, r < ChebyshevQuarticScale.crossed) (du : Dusart) :
    2^498 < (survivingSquares ChebyshevQuarticScale.crossed
      (physicalLower ChebyshevQuarticScale.crossed) ChebyshevQuarticScale.crossed.sqrt draws).card :=
  control (a := 49*2^506) (b := 51*2^506) draws len draw
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) du

end PrimeFactors.FullSizeSquareDecoys
