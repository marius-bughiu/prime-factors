import PrimeFactors.PrimitiveIntervalCandidateBand
import PrimeFactors.SquareDivisorClueWindow

/-! A supplied synthetic integer reading on a previously certified 39-bit
product. The five candidates follow from four endpoint comparisons. -/
namespace PrimeFactors.PrimitiveIntervalSuppliedExample

open Finset PrimitiveIntervalMoment PrimitiveIntervalCandidateBand

private abbrev N : ℕ := 419636024497
private abbrev B : ℕ := 458058
private abbrev v : ℤ := -112538867588
private abbrev E : ℕ := 16000000
private abbrev V (s : ℕ) : ℤ := value N B s

/-- Reuse the published factor certificate to identify the exact character
aggregate. The synthetic observation adds exactly five million. -/
theorem supplied_reading :
    cutoff N = B ∧ aggregate 556559 753983 B = (-112543867588:ℂ) ∧
    v - V 1310542 = 5000000 ∧ |v - V 1310542| ≤ E := by
  have factor := SquareDivisorClueWindow.seeded_control.1
  letI : Fact (Nat.Prime 556559) := ⟨factor.2 _ (by simp)⟩
  letI : Fact (Nat.Prime 753983) := ⟨factor.2 _ (by simp)⟩
  have cut : cutoff N = B := (Nat.eq_sqrt'.mpr (by decide +kernel)).symm
  refine ⟨cut,?_,by decide +kernel,by decide +kernel⟩
  have agg := aggregate_value (p:=556559) (q:=753983) (by decide) (by decide)
  change aggregate 556559 753983 (cutoff N) = ((value N (cutoff N) 1310542 : ℤ):ℂ) at agg
  rw [cut] at agg
  exact agg.trans (by norm_num [V,value,B,N])

private theorem monotone {s t : ℕ} (lo : B+1 ≤ s) (ord : s ≤ t) : V s ≤ V t := by
  have h := value_difference N B s t
  change V t - V s = _ at h
  have pos := mul_nonneg (show (0:ℤ)≤(t:ℤ)-s by omega)
    (show (0:ℤ)≤(s:ℤ)+t-2*B-2 by omega)
  omega

/-- Within the public interval, the reading cuts out exactly nineteen
consecutive integers before the mod-four condition is imposed. -/
theorem raw_interval {s : ℕ} (lo : 2*B+2 ≤ s) :
    |V s-v| ≤ E ↔ 1310536 ≤ s ∧ s ≤ 1310554 := by
  have lowerMiss : V 1310535 < v-E := by decide +kernel
  have lowerHit : v-E ≤ V 1310536 := by decide +kernel
  have upperHit : V 1310554 ≤ v+E := by decide +kernel
  have upperMiss : v+E < V 1310555 := by decide +kernel
  rw [abs_le]
  constructor
  · intro h
    constructor
    · by_contra! small
      have := monotone (by omega : B+1 ≤ s) (show s ≤ 1310535 by omega)
      omega
    · by_contra! big
      have := monotone (by decide : B+1 ≤ 1310555) (show 1310555 ≤ s by omega)
      omega
  · rintro ⟨l,u⟩
    have a := monotone (by decide : B+1 ≤ 1310536) l
    have b := monotone (by omega : B+1 ≤ s) u
    omega

/-- The candidate filter receives only N, B, the supplied reading and E. -/
theorem five_candidates :
    candidates N B v E = {1310538,1310542,1310546,1310550,1310554} := by
  ext s
  simp only [mem_candidates,mem_insert,mem_singleton]
  change ((2*B+2 ≤ s ∧ s ≤ 4*B+2) ∧ s%4=2 ∧ |V s-v| ≤ E) ↔ _
  constructor
  · rintro ⟨⟨lo,_⟩,r,h⟩
    obtain ⟨l,u⟩ := (raw_interval lo).mp h
    omega
  · intro h
    have low : 2*B+2 ≤ s := by change 916118 ≤ s; omega
    exact ⟨⟨low,by change s ≤ 1832234; omega⟩,by omega,(raw_interval low).mpr (by omega)⟩

private theorem sqrt_square_iff (d : ℕ) : IsSquare d ↔ d.sqrt*d.sqrt=d := by
  rw [← Nat.exists_mul_self]
  exact ⟨fun ⟨r,h⟩ => ⟨r,h.symm⟩,fun ⟨r,h⟩ => ⟨r,h.symm⟩⟩

private theorem true_gap : Nat.sqrt (1310542^2-4*N) = 197424 :=
  (Nat.eq_sqrt'.mpr (by decide +kernel)).symm

/-- Taking the integer square root of each of the five discriminants
leaves just the true sum. Its square root is the factor gap 197424. -/
theorem square_discriminant {s : ℕ} (hs : s ∈ candidates N B v E) :
    IsSquare (s^2-4*N) ↔ s=1310542 := by
  rw [five_candidates] at hs
  simp only [mem_insert,mem_singleton] at hs
  rw [sqrt_square_iff]
  rcases hs with rfl|rfl|rfl|rfl|rfl
  · rw [show Nat.sqrt (1310538^2-4*N)=197397 from (Nat.eq_sqrt'.mpr (by decide +kernel)).symm]
    decide +kernel
  · rw [true_gap]
    decide +kernel
  · rw [show Nat.sqrt (1310546^2-4*N)=197450 from (Nat.eq_sqrt'.mpr (by decide +kernel)).symm]
    decide +kernel
  · rw [show Nat.sqrt (1310550^2-4*N)=197477 from (Nat.eq_sqrt'.mpr (by decide +kernel)).symm]
    decide +kernel
  · rw [show Nat.sqrt (1310554^2-4*N)=197503 from (Nat.eq_sqrt'.mpr (by decide +kernel)).symm]
    decide +kernel

theorem recovered_factors :
    (1310542-Nat.sqrt (1310542^2-4*N))/2=556559 ∧
    (1310542+Nat.sqrt (1310542^2-4*N))/2=753983 ∧
    ExactFactorization N [556559,753983] := by
  rw [true_gap]
  exact ⟨by decide +kernel,by decide +kernel,SquareDivisorClueWindow.seeded_control.1⟩

end PrimeFactors.PrimitiveIntervalSuppliedExample
