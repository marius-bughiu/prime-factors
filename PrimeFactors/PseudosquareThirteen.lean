import PrimeFactors.PseudosquareNormalization
import PrimeFactors.LevelMaskCertificate

/-! Lehmer, Lehmer and Shanks, *Integer sequences having prescribed quadratic
character* (1970), Table I, lists 8089 as the least 13-pseudosquare
(https://doi.org/10.1090/S0025-5718-1970-0271006-X). The
finite proof here independently checks all 1011 smaller candidates congruent
to one modulo eight, along with the endpoint and a masked example. -/

namespace PrimeFactors.PseudosquareThirteen

open PseudosquareNormalization
open private PrimeFactors.PseudosquareNormalization.clean_id from PrimeFactors.PseudosquareNormalization

def tests : List ℕ := [3,5,7,11,13]

theorem primes : ∀ p ∈ tests, Nat.Prime p := by decide +kernel

private theorem mask_iff (p m u : ℕ) (hp : 0<p)
    (cert : ∀ a : Fin p, m.testBit a.val = true ↔ UnitSquare p a.val) :
    m.testBit (u%p) = true ↔ UnitSquare p u := by
  simpa only [UnitSquare,Nat.mod_mod] using cert ⟨u%p,Nat.mod_lt _ hp⟩

private def oddRows : List (ℕ × ℕ) := [(3,2),(5,18),(7,22),(11,570),(13,5658)]

private theorem certificate : ∀ r∈oddRows, r.1 ∈ tests ∧ 0<r.1 ∧
    ∀ i : Fin r.1, r.2.testBit i.val=true ↔ UnitSquare r.1 i.val := by decide +kernel

/-- Each set bit occurs at the square of one of the listed roots. -/
private def squareMask : List ℕ → ℕ
  | [] => 0
  | x::xs => 2^(x^2) ||| squareMask xs

private theorem squareMask_sound (xs : List ℕ) (u : ℕ) (hit : (squareMask xs).testBit u=true) :
    IsSquare u := by
  induction xs with
  | nil => simp [squareMask] at hit
  | cons x xs ih =>
    simp only [squareMask,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,decide_eq_true_eq] at hit
    rcases hit with eq | tail
    · exact (isSquare_iff_exists_sq _).mpr ⟨x,by omega⟩
    · exact ih tail

private def allRows : List (ℕ × ℕ) := (8,2)::oddRows

private def belowMask : ℕ := LevelMaskCertificate.block 0 8089 (fun _ => 12) allRows

private theorem mask_subset :
    belowMask &&& squareMask (List.range 90) = belowMask := by decide +kernel

/-- Both the threshold and its first failing endpoint are kernel-checked.
The bit at u in the 8089-position block is set exactly when it meets all rows.
A bitwise inclusion certificate places every such bit at a square. -/
theorem cutoff : Cutoff tests 8089 where
  below := by
    intro u _ size pass
    have room : ∀ r∈allRows, 0<r.1 ∧ (0%(r.1:ℤ)).toNat+8089 ≤ r.1*2^12 := by decide
    have hits (r : ℕ × ℕ) (mem : r∈allRows) : r.2.testBit (u%r.1)=true := by
      rcases List.mem_cons.mp mem with rfl | mem
      · change (2:ℕ).testBit (u%8)=true
        rw [pass.1]
        decide
      · obtain ⟨listed,positive,cert⟩ := certificate r mem
        exact (mask_iff r.1 r.2 u positive cert).mpr (pass.2 _ listed)
    have bit : belowMask.testBit u = true := LevelMaskCertificate.block_bit _ _ _ _ _ size room (by
      intro r m
      simpa only [zero_add,←Int.natCast_emod,Int.toNat_natCast] using hits r m)
    have both := bit
    rw [←mask_subset,Nat.testBit_and,Bool.and_eq_true] at both
    exact squareMask_sound _ u both.2
  positive := by decide
  nonsquare := by
    intro sq
    obtain ⟨x,eq⟩ := sq.exists_sq
    by_cases small : x≤89
    · have := Nat.pow_le_pow_left small 2
      omega
    · have := Nat.pow_le_pow_left (show 90≤x by omega) 2
      omega
  endpoint := by decide +kernel

theorem test {D : ℕ} (pos : 0<D) (size : residual (2::tests) D < 8089) :
    IsSquare D ↔ evenExponents (2::tests) D ∧ Passes tests (residual (2::tests) D) :=
  normalized_iff cutoff pos primes size

/-- Both candidate sums meet the public balance and parity conditions. -/
theorem control_data : Nat.Prime 353 ∧ Nat.Prime 359 ∧ 353*359=(126727:ℕ) ∧
    353+359=(712:ℕ) ∧
    (∀ s ∈ ([712,728] : List ℕ), 4*126727≤s^2 ∧ 2*s^2≤9*126727 ∧ s%4=(126727+1)%4) ∧
    356^2-126727=(9:ℕ) ∧ 364^2-126727=(5769:ℕ) ∧ 5769=3^2*(641:ℕ) ∧
    5769<8089 ∧ 5769%8=(1:ℕ) := by decide +kernel

/-- All five ordinary square tests pass the false midpoint discriminant,
including zero at three. -/
theorem masked_passes : ∀ p ∈ tests, IsSquare ((5769:ℕ):ZMod p) := by
  have table : ∀ p ∈ tests, ∃ x : Fin p, x.val^2%p=5769%p := by decide +kernel
  intro p hp
  obtain ⟨x,ex⟩ := table p hp
  apply (isSquare_iff_exists_sq _).mpr
  refine ⟨(x.val:ZMod p),?_⟩
  simpa only [Nat.cast_pow] using ((ZMod.natCast_eq_natCast_iff' ..).mpr ex).symm

private theorem strip_three {D u : ℕ} (pos : D ≠ 0) (odd : ¬2∣D)
    (low : 3^2∣D) (high : ¬3^3∣D) (div : D/9=u)
    (clean : ∀p∈([5,7,11,13]:List ℕ), ¬ p∣u) :
    residual (2::tests) D = u ∧ evenExponents (2::tests) D := by
  have v2 := Nat.factorization_eq_zero_of_not_dvd odd
  have lo := (Nat.prime_three.pow_dvd_iff_le_factorization pos).mp low
  have hi := mt (Nat.prime_three.pow_dvd_iff_le_factorization pos).mpr high
  have v3 : D.factorization 3=2 := by omega
  have first : away 2 D=D := by simp [away,v2]
  have next : away 3 D=u := by simpa [away,v3] using div
  obtain ⟨same,even⟩ := PrimeFactors.PseudosquareNormalization.clean_id _ u clean
  change residual [5,7,11,13] (away 3 (away 2 D))=u ∧ Even (D.factorization 2) ∧
    Even ((away 2 D).factorization 3) ∧ evenExponents [5,7,11,13] (away 3 (away 2 D))
  rw [first,next,v2,v3]
  exact ⟨same,⟨0,rfl⟩,⟨1,rfl⟩,even⟩

/-- Stripping removes the masking square from both the true and false
candidates. The strict unit test then accepts one and rejects 641 at three. -/
theorem control_residuals : residual (2::tests) 9 = 1 ∧ residual (2::tests) 5769 = 641 ∧
    evenExponents (2::tests) 9 ∧ evenExponents (2::tests) 5769 ∧
    Passes tests 1 ∧ ¬ UnitSquare 3 641 ∧ ¬ Passes tests 9 ∧ ¬ Passes tests 5769 := by
  obtain ⟨r₁,e₁⟩ := strip_three (D:=9) (u:=1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨r₂,e₂⟩ := strip_three (D:=5769) (u:=641) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨r₁,r₂,e₁,e₂,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

/-- The normalized test recognizes the true midpoint discriminant and excludes the false one. -/
theorem classified_control : IsSquare (9:ℕ) ∧ ¬ IsSquare (5769:ℕ) := by
  obtain ⟨r₁,r₂,e₁,_,pass,fail,_⟩ := control_residuals
  constructor
  · exact (test (by decide) (by rw [r₁]; decide)).mpr ⟨e₁,r₁.symm ▸ pass⟩
  · intro square
    have checked := ((test (by decide) (by rw [r₂]; decide)).mp square).2
    rw [r₂] at checked
    exact fail (checked.2 3 (by decide))

end PrimeFactors.PseudosquareThirteen
