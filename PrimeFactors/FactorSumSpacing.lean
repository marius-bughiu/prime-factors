import PrimeFactors.TraceGapCycle
import PrimeFactors.TraceGapMoments
import PrimeFactors.SquareTraceGapLift

/-! Every displacement is attained between two local factor sums modulo a
prime at least eleven and at all positive powers of that prime. The two sums may have different factor-pair witnesses. -/
namespace PrimeFactors.FactorSumSpacing

open Finset

/-- Two admissible sums for the same product differ by the prescribed shift. -/
def Gap (m : ℕ) (n t : ZMod m) : Prop :=
  ∃ s : ZMod m, AdmissibleSum n s ∧ AdmissibleSum n (s+t)

private theorem nonsquare {ℓ : ℕ} [Fact ℓ.Prime] (large : 11≤ℓ) (n t : ZMod ℓ)
    (ns : ¬ IsSquare n) : Gap ℓ n t := by
  have nonzero : n≠0 := fun h => ns (h ▸ IsSquare.zero)
  let A := factorSumResidues ℓ n
  by_contra no
  have sep : ∀ s∈A, s+t∉A := fun s hs ht =>
    no ⟨s,(mem_factorSumResidues_iff ℓ nonzero).mp hs,(mem_factorSumResidues_iff ℓ nonzero).mp ht⟩
  obtain ⟨k,hk⟩ := (Fact.out : ℓ.Prime).odd_of_ne_two (by omega)
  have cnt : A.card=k := (card_factorSumResidues_of_nonsquare ℓ n nonzero ns).trans (by omega)
  obtain ⟨one,two,three,four⟩ := TraceGapMoments.moments (by omega) n ns
  have collapse := TraceGapCycle.prime_moment_identity (by omega) A t (by omega : ℓ=2*k+1)
    cnt sep one three
  change (∑ x∈factorSumResidues ℓ n,x^4) = -10*(∑ x∈factorSumResidues ℓ n,x^2)^2 at collapse
  rw [four,two] at collapse
  have seven : (7 : ZMod ℓ)≠0 := by
    intro h
    have dvd := (ZMod.natCast_zmod_eq_zero_iff_dvd 7 ℓ).mp h
    have bound := Nat.le_of_dvd (by decide : 0<7) dvd
    omega
  apply (mul_ne_zero seven (pow_ne_zero 2 nonzero))
  linear_combination collapse

/-- Over all primes at least eleven, every product residue allows every gap. -/
theorem prime {ℓ : ℕ} [Fact ℓ.Prime] (large : 11≤ℓ) (n t : ZMod ℓ) : Gap ℓ n t := by
  by_cases zero : n=0
  · subst n
    exact ⟨0,⟨0,0,zero_mul _,zero_add _⟩,⟨0,t,zero_mul _,rfl⟩⟩
  by_cases sq : IsSquare n
  · obtain ⟨s,h,j,_⟩ := SquareTraceGapLift.regular_gap (by omega) n t zero sq
    exact ⟨s,h,j⟩
  exact nonsquare large n t sq

/-- Nonsquare products have no singular trace at an odd prime. -/
theorem regular {ℓ : ℕ} [Fact ℓ.Prime] (odd : ℓ≠2) {n : ZMod ℓ}
    (ns : ¬IsSquare n) (s : ZMod ℓ) : s^2-4*n ≠ 0 := by
  have two : (2 : ZMod ℓ)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  intro zero
  apply ns
  refine ⟨s/2,?_⟩
  rw [div_mul_div_comm,eq_div_iff (mul_ne_zero two two)]
  linear_combination -zero

/-- For a product coprime to a prime at least eleven, each displacement is
realized modulo every positive power, including displacements divisible by the prime. -/
theorem prime_power {ℓ : ℕ} [Fact ℓ.Prime] (large : 11≤ℓ) (n t : ℤ)
    (unit : (n : ZMod ℓ)≠0) (k : ℕ) : Gap (ℓ^(k+1)) n t := by
  by_cases sq : IsSquare (n : ZMod ℓ)
  · exact SquareTraceGapLift.power (by omega) n t unit sq k
  obtain ⟨s,first,next⟩ := nonsquare large (n : ZMod ℓ) (t : ZMod ℓ) sq
  obtain ⟨S,rfl⟩ := ZMod.intCast_surjective s
  have lift (u : ℤ) (h : AdmissibleSum (n : ZMod ℓ) (u : ZMod ℓ)) :
      AdmissibleSum (n : ZMod (ℓ^(k+1))) (u : ZMod (ℓ^(k+1))) := by
    apply (admissibleSum_primePow_iff_of_regular (by omega : ℓ≠2) n u _ k).mpr h
    simpa only [Int.cast_sub,Int.cast_pow,Int.cast_mul,Int.cast_ofNat] using
      (regular (by omega : ℓ≠2) sq (u : ZMod ℓ))
  exact ⟨S,lift _ first,by simpa only [Int.cast_add] using lift (S+t) (by
    simpa only [Int.cast_add] using next)⟩

/-- If the product vanishes at the base prime, choose both traces nonzero
there. Their discriminants are nonzero squares, even when the product at the
prime power is nonzero. This argument also covers the odd primes 3, 5 and 7. -/
theorem prime_power_of_zero {ℓ : ℕ} [Fact ℓ.Prime] (large : 3≤ℓ) (n t : ℤ)
    (zero : (n : ZMod ℓ)=0) (k : ℕ) : Gap (ℓ^(k+1)) n t := by
  have odd : ℓ≠2 := by omega
  have two : (2 : ZMod ℓ)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have select : ∃ u : ℤ, (u : ZMod ℓ)≠0 ∧ ((u+t : ℤ) : ZMod ℓ)≠0 := by
    by_cases hit : 1 + (t:ZMod ℓ) = 0
    · refine ⟨2,by simpa only [Int.cast_ofNat] using two,?_⟩
      push_cast
      intro h
      apply (one_ne_zero : (1:ZMod ℓ)≠0)
      linear_combination h-hit
    · exact ⟨1,by simp,by simpa only [Int.cast_add,Int.cast_one] using hit⟩
  have lift (u : ℤ) (nz : (u:ZMod ℓ)≠0) :
      AdmissibleSum (n : ZMod (ℓ^(k+1))) (u : ZMod (ℓ^(k+1))) := by
    have reg : ((u^2-4*n : ℤ) : ZMod ℓ)≠0 := by simpa [zero] using (pow_ne_zero 2 nz)
    apply (admissibleSum_primePow_iff_of_regular odd n u reg k).mpr
    rw [zero]
    exact ⟨0,u,zero_mul _,zero_add _⟩
  obtain ⟨u,first,next⟩ := select
  exact ⟨u,lift u first,by simpa only [Int.cast_add] using lift (u+t) next⟩

/-- Every prescribed displacement between local sums is possible over each
positive power of a prime at least eleven, for every integer product. -/
theorem prime_power_all {ℓ : ℕ} [Fact ℓ.Prime] (large : 11≤ℓ) (n t : ℤ) (k : ℕ) :
    Gap (ℓ^(k+1)) n t := by
  by_cases zero : (n : ZMod ℓ)=0
  · exact prime_power_of_zero (by omega) n t zero k
  · exact prime_power large n t zero k

end PrimeFactors.FactorSumSpacing
