import PrimeFactors.MonotoneSumPopulation
import PrimeFactors.SquareRootPhasePopulation

/-! A nonincreasing prediction can track only a short run of partners
at each fixed smaller prime, even with an additive error allowance. -/
namespace PrimeFactors.AntitoneSumPopulation

open Finset MixedPrefixSample MonotoneSumPopulation
open private PrimeFactors.MixedPrefixSample.mem_sample from PrimeFactors.MixedPrefixSample
open scoped Classical

attribute [local irreducible] eligible primes
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

private theorem smaller {z : ℕ×ℕ} (ok : z∈eligible) : z.1∈primes := by
  rw [eligible] at ok
  exact (mem_ordered.mp (PrimeFactors.MixedPrefixSample.mem_sample.mp ok).1).1

/-- For a fixed smaller coordinate p, increasing the partner by more
than twice the tolerance makes joint agreement impossible. -/
theorem partners {g : ℕ→ℕ} (down : Antitone g) {p q r E : ℕ} (qr : q≤r)
    (first : g (p*q)≤p+q+E) (last : p+r≤g (p*r)+E) : r≤q+2*E := by
  have := down (Nat.mul_le_mul_left p qr)
  omega

private theorem count_on (A : Finset (ℕ×ℕ)) (P : Finset ℕ) (g : ℕ→ℕ) (down : Antitone g) (E : ℕ)
    (inside : ∀ z∈A, z.1∈P)
    (fit : ∀ z∈A, g (z.1*z.2)≤z.1+z.2+E ∧ z.1+z.2≤g (z.1*z.2)+E) :
    A.card≤(2*E+1)*P.card := by
  classical
  apply card_le_mul_card_image_of_maps_to (f:=Prod.fst) inside
  intro p _
  let row := A.filter (fun z => z.1=p)
  let Q := row.image Prod.snd
  have inject : row.card=Q.card :=
    (card_image_of_injOn (s:=row) (f:=Prod.snd) (by
      intro x hx y hy eq
      exact Prod.ext ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) eq)).symm
  change row.card≤2*E+1
  rw [inject]
  obtain empty|nonempty := Q.eq_empty_or_nonempty
  · simp [empty]
  let m := Q.min' nonempty
  have on {q : ℕ} (hq : q∈Q) : (p,q)∈A := by
    obtain ⟨⟨x,y⟩,hy,rfl⟩ := mem_image.mp hq
    obtain ⟨mem,eq⟩ := mem_filter.mp hy
    change x=p at eq
    simpa only [eq] using mem
  have low := (fit _ (on (Q.min'_mem nonempty))).1
  have sub : Q⊆Icc m (m+2*E) := by
    intro q hq
    have le := Q.min'_le q hq
    exact mem_Icc.mpr ⟨le,partners down le low (fit _ (on hq)).2⟩
  exact (card_le_card sub).trans (by rw [Nat.card_Icc]; omega)

private theorem mem_agree {g : ℕ→ℕ} {E : ℕ} {z : ℕ×ℕ} (hz : z∈agreement g E) :
    z∈eligible ∧ g (z.1*z.2)≤z.1+z.2+E ∧ z.1+z.2≤g (z.1*z.2)+E := Finset.mem_filter.mp hz

attribute [local irreducible] agreement

theorem count (g : ℕ→ℕ) (down : Antitone g) (E : ℕ) :
    (agreement g E).card≤(2*E+1)*primes.card :=
  count_on (agreement g E) primes g down E
    (fun z hz => smaller (z:=z) (mem_agree (z:=z) (g:=g) (E:=E) hz).1)
    (fun z hz => (mem_agree (z:=z) (g:=g) (E:=E) hz).2)

/-- No regularity or cost assumption beyond the direction of the prediction. -/
theorem fraction (g : ℕ→ℕ) (down : Antitone g) (E : ℕ) :
    2^1007*(agreement g E).card<(2*E+1)*eligible.card := by
  have cap : 41056*2^1007≤X := by decide +kernel
  have pos : 0<2*E+1 := by omega
  have per := count g down E
  have norm := Nat.mul_lt_mul_of_pos_left SquareRootPhasePopulation.marginal pos
  apply Nat.lt_of_mul_lt_mul_left (a:=41056)
  calc
    41056*(2^1007*(agreement g E).card) ≤ X*((2*E+1)*primes.card) := by
      rw [←Nat.mul_assoc]
      exact Nat.mul_le_mul cap per
    _ = (2*E+1)*(X*primes.card) := by ac_rfl
    _ < (2*E+1)*(41056*eligible.card) := norm
    _ = _ := by ac_rfl

end PrimeFactors.AntitoneSumPopulation
