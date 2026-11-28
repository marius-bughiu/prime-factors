import PrimeFactors.FullWidthRotationRoots
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! Group prime factors by their local square classes at the sixteen primes of
the fixed rotation modulus. The Chinese remainder theorem joins the local
roots of a product when the two signatures agree. -/

namespace PrimeFactors.RotationPrimeSignature

open Finset BinaryRotationModulus BinaryRotationProduct RotationSquareRootCount
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

private theorem word_roots (N r : ℕ) : roots 1024 N r=residues M (2^r*N) := rfl

private theorem three_factor : 3∈factors := by decide +kernel

attribute [local irreducible] M factors

/-- Record the prime divisors of M at which n is a square. -/
noncomputable def signature (n : ℕ) := factors.toFinset.filter fun ℓ => IsSquare (n : ZMod ℓ)

noncomputable def bins := factors.toFinset.powerset

theorem card_bins : bins.card=65536 := by
  rw [bins,card_powerset,List.toFinset_card_of_nodup distinct,size]
  decide

theorem signature_mem (n : ℕ) : signature n∈bins :=
  mem_powerset.mpr (filter_subset _ _)

theorem mem_signature {n ℓ : ℕ} : ℓ∈signature n ↔ ℓ∈factors ∧ IsSquare (n : ZMod ℓ) := by
  simp only [signature,mem_filter,List.mem_toFinset]

private theorem matched {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {x y : F} (same : IsSquare x ↔ IsSquare y) : IsSquare (x*y) := by
  by_cases sx : IsSquare x
  · exact sx.mul (same.mp sx)
  · have sy : ¬IsSquare y := fun h => sx (same.mpr h)
    have nx : x≠0 := fun h => sx (h ▸ IsSquare.zero)
    have ny : y≠0 := fun h => sy (h ▸ IsSquare.zero)
    apply (quadraticChar_one_iff_isSquare (mul_ne_zero nx ny)).mp
    rw [map_mul,quadraticChar_neg_one_iff_not_isSquare.mpr sx,
      quadraticChar_neg_one_iff_not_isSquare.mpr sy]
    norm_num

private theorem field_root {ℓ N : ℕ} (prime : ℓ.Prime) (sq : IsSquare (N : ZMod ℓ)) :
    (residues ℓ N).Nonempty := by
  letI : Fact ℓ.Prime := ⟨prime⟩
  obtain ⟨r,eq⟩ := sq
  refine ⟨r.val,mem_residues.mpr ⟨ZMod.val_lt _,?_⟩⟩
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  simpa only [Nat.cast_pow,Nat.cast_mul,ZMod.natCast_zmod_val,pow_two] using eq.symm

private theorem join_roots {L : List ℕ} {N : ℕ} (positive : ∀ ℓ∈L,0<ℓ)
    (co : L.Pairwise Nat.Coprime) (localRoots : ∀ ℓ∈L,(residues ℓ N).Nonempty) :
    (residues L.prod N).Nonempty := by
  induction L with
  | nil => exact ⟨0,mem_residues.mpr ⟨by decide,(Nat.mod_one N).symm⟩⟩
  | cons ℓ L ih =>
    have tail (q : ℕ) (hq : q∈L) := positive q (List.mem_cons_of_mem _ hq)
    have pos : 0<L.prod := Nat.pos_of_ne_zero (List.prod_ne_zero fun h => (tail 0 h).ne' rfl)
    have cop := Nat.coprime_list_prod_right_iff.mpr (List.pairwise_cons.mp co).1
    have left := localRoots ℓ (List.mem_cons_self ..)
    have right := ih tail co.of_cons (fun q h => localRoots q (List.mem_cons_of_mem _ h))
    rw [←card_pos,List.prod_cons,product_count cop (positive ℓ (by simp)) pos]
    exact Nat.mul_pos (card_pos.mpr left) (card_pos.mpr right)

/-- Matching local square signatures suffice for every pair of ordinary numbers. -/
theorem square_of_same {p q : ℕ} (same : signature p=signature q) :
    (roots 1024 (p*q) 0).Nonempty := by
  rw [word_roots,pow_zero,one_mul,←exactFactors.1]
  apply join_roots (fun ℓ h => (exactFactors.2 ℓ h).pos) FullWidthRotationRoots.factors_coprime
  intro ℓ h
  have prime := exactFactors.2 ℓ h
  letI : Fact ℓ.Prime := ⟨prime⟩
  apply field_root prime
  rw [Nat.cast_mul]
  apply matched
  have agree : ℓ∈signature p ↔ ℓ∈signature q := by rw [same]
  simpa only [mem_signature,h,true_and] using agree

/-- On primes at least 2^1023, matching signs put the product in the even
rotation phase. There are exactly 65,536 roots in that phase. -/
theorem same_square_count {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (pl : 2^1023≤p)
    (ql : 2^1023≤q) (same : signature p=signature q) :
    (roots 1024 (p*q) 0).Nonempty ∧ (roots 1024 (p*q) 0).card=65536 := by
  have hit := square_of_same same
  exact ⟨hit,FullWidthRotationRoots.roots_card (Nat.coprime_mul_iff_left.mpr
    ⟨FullWidthRotationRoots.prime_unit pp pl,FullWidthRotationRoots.prime_unit qp ql⟩) hit⟩

theorem same_square {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (pl : 2^1023≤p)
    (ql : 2^1023≤q) (same : signature p=signature q) : (roots 1024 (p*q) 0).Nonempty :=
  (same_square_count pp qp pl ql same).1

/-- Multiplying by two when n is two modulo three puts the result in a square
class at three. The other fifteen square classes encode both possible phases. -/
def normalized (n : ℕ) := if n%3=2 then 2*n else n

private theorem normalized_three (n : ℕ) : 3∈signature (normalized n) := by
  apply mem_signature.mpr ⟨three_factor,?_⟩
  have eq := (ZMod.natCast_mod n 3).symm
  rcases (show n%3=0 ∨ n%3=1 ∨ n%3=2 by omega) with h|h|h
  · simp [normalized,h,eq]
  · simp [normalized,h,eq]
  · rw [normalized,if_pos h,Nat.cast_mul,eq,h]
    exact ⟨2,by decide⟩

noncomputable def shortSignature (n : ℕ) := (signature (normalized n)).erase 3

noncomputable def shortBins := (factors.toFinset.erase 3).powerset

theorem card_shortBins : shortBins.card=32768 := by
  rw [shortBins,card_powerset,card_erase_of_mem (List.mem_toFinset.mpr three_factor),
    List.toFinset_card_of_nodup distinct,size]
  decide

theorem shortSignature_mem (n : ℕ) : shortSignature n∈shortBins :=
  mem_powerset.mpr (erase_subset_erase 3 (mem_powerset.mp (signature_mem (normalized n))))

private theorem undouble {N : ℕ} (hit : (roots 1024 (4*N) 0).Nonempty) :
    (roots 1024 N 0).Nonempty := by
  let inv : ℕ := 2^1023
  have den : 2*inv ≡ 1 [MOD modulus 1024] := by decide +kernel
  have nz : 0<modulus 1024 := by decide +kernel
  obtain ⟨r,hr⟩ := hit
  have eq := (mem_roots.mp hr).2
  rw [pow_zero,one_mul] at eq
  refine ⟨(r*inv)%modulus 1024,mem_roots.mpr ⟨Nat.mod_lt _ nz,?_⟩⟩
  rw [pow_zero,one_mul]
  apply ((Nat.mod_modEq ..).pow 2).trans
  rw [mul_pow]
  apply (eq.mul_right (inv^2)).trans
  rw [show 4*N*inv^2=N*(2*inv)^2 by ring]
  simpa only [one_pow,mul_one] using (den.pow 2).mul_left N

private theorem odd_scaled (N : ℕ) : roots 1024 (2*N) 0=roots 1024 N 1 := by
  simp only [roots,pow_zero,pow_one,one_mul]

/-- Equal fifteen-bit signatures guarantee that at least one phase is occupied.
The signature compares the two factors and does not require a rotation between them. -/
theorem same_phase {p q : ℕ} (same : shortSignature p=shortSignature q) :
    (roots 1024 (p*q) 0).Nonempty ∨ (roots 1024 (p*q) 1).Nonempty := by
  have equal : signature (normalized p)=signature (normalized q) :=
    (insert_erase (normalized_three p)).symm.trans
      ((congrArg (insert 3) same).trans (insert_erase (normalized_three q)))
  have hit := square_of_same equal
  by_cases hp : p%3=2 <;> by_cases hq : q%3=2
  · apply Or.inl
    apply undouble
    simpa only [normalized,if_pos hp,if_pos hq,show 2*p*(2*q)=4*(p*q) by ring] using hit
  · apply Or.inr
    rw [←odd_scaled]
    simpa only [normalized,if_pos hp,if_neg hq,mul_assoc] using hit
  · apply Or.inr
    rw [←odd_scaled]
    simpa only [normalized,if_neg hp,if_pos hq,show p*(2*q)=2*(p*q) by ring] using hit
  · exact Or.inl (by simpa only [normalized,if_neg hp,if_neg hq] using hit)

end PrimeFactors.RotationPrimeSignature
