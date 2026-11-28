import PrimeFactors.CoprimeGuessTables
import PrimeFactors.LocalSumMenu
import PrimeFactors.PrimePowerSumFilter

/-! Minimum mass of each attainable sum for a uniform ordered pair with
fixed odd product modulo a power of two. -/
namespace PrimeFactors.TwoPowerGuessShare

open Finset CoprimeGuessTables PrimeSquareSumWeights
open scoped Classical
open private PrimeFactors.CombinedSumWeights.weight_first from PrimeFactors.CombinedSumWeights

/-- A half-modulus shift gives a different pair with the same product and sum. -/
theorem two_le_weight {k n : ℕ} (odd : Odd n) {s : ZMod (2^(k+2))}
    (ok : AdmissibleSum (n : ZMod _) s) : 2 ≤ weight n s := by
  classical
  let M := 2^(k+2)
  let H := 2^(k+1)
  have mod_eq : M = H*2 := pow_succ _ _
  obtain ⟨x, y, prod, rfl⟩ := ok
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective x
  obtain ⟨b, rfl⟩ := ZMod.natCast_zmod_surjective y
  have red : a*b ≡ n [MOD 2] := ((ZMod.natCast_eq_natCast_iff (a*b) n M).mp
    (by simpa only [Nat.cast_mul] using prod)).of_dvd (mod_eq ▸ dvd_mul_left _ _)
  have ab : a%2 = b%2 := by
    change (a*b)%2=n%2 at red
    rw [Nat.mul_mod] at red
    obtain ⟨j,hj⟩ := odd
    rcases (show a%2=0 ∨ a%2=1 by omega) with ha|ha <;>
      rcases (show b%2=0 ∨ b%2=1 by omega) with hb|hb <;>
      simp only [ha,hb] at red ⊢ <;> omega
  let h : ZMod M := H
  have h2 : 2*h=0 := by
    change (2 : ZMod M)*(H : ZMod M)=0
    have z : ((2*H:ℕ):ZMod M)=0 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr
      (by rw [mod_eq,Nat.mul_comm 2 H])
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using z
  have hn : h≠0 := by
    intro zero
    have dvd := (ZMod.natCast_zmod_eq_zero_iff_dvd H M).mp zero
    have pos : 0<H := by dsimp [H]; positivity
    have := Nat.le_of_dvd pos dvd
    omega
  have scaled (v : ℕ) : h*(v:ZMod M)=h*(v%2:ℕ) := by
    have decomp := Nat.mod_add_div v 2
    conv_lhs => rw [←decomp]
    push_cast
    linear_combination h2 * (v/2 : ℕ)
  have hsq : h*h=0 := by
    change h*(H:ZMod M)=0
    rw [scaled, show H%2=0 by dsimp [H]; rw [pow_succ]; omega]
    simp
  have diff : h*(a:ZMod M)=h*(b:ZMod M) := by
    rw [scaled a,scaled b,ab]
  let F := {z : ZMod M // z*((a:ZMod M)+b-z)=n}
  let u : F := ⟨a,by simpa using prod⟩
  let v : F := ⟨a+h,by linear_combination prod - diff - hsq⟩
  have ne : u≠v := by
    intro eq
    have val : (a:ZMod M)=a+h := congrArg Subtype.val eq
    exact hn (by linear_combination -val)
  haveI : Nontrivial F := ⟨⟨u,v,ne⟩⟩
  rw [PrimeFactors.CombinedSumWeights.weight_first, Nat.card_eq_fintype_card]
  exact (Fintype.one_lt_card (α:=F))

/-- Each attained label carries at least one sixteenth of its mass in the
uniform distribution on attained labels, for every dyadic precision. -/
theorem uniform_bound {e n : ℕ} (odd : Odd n) (s : Labels (2^e) n) :
    (2^e).totient ≤ 16 * Fintype.card (Labels (2^e) n) * weight n s.val := by
  classical
  have mass := (positive_iff (n:=n) s.val).mpr s.property
  have labels := Fintype.card_pos (α:=Labels (2^e) n)
  have one : 1 ≤ Fintype.card (Labels (2^e) n) * weight n s.val := Nat.mul_pos labels mass
  rcases e with _|(_|k)
  · simpa only [pow_zero, Nat.totient_one, Nat.mul_assoc] using one.trans
      (Nat.le_mul_of_pos_left _ (by decide : 0<16))
  · simpa only [pow_one, Nat.totient_prime Nat.prime_two, Nat.reduceSub, Nat.mul_assoc] using one.trans
      (Nat.le_mul_of_pos_left _ (by decide : 0<16))
  · have density := LocalSumMenu.dyadic_density (n:=n) (fun h => by obtain ⟨k,hk⟩ := odd; omega) (k+2)
    change 2^(k+2) ≤ 64 * Nat.card (Labels (2^(k+2)) n) at density
    rw [Nat.card_eq_fintype_card] at density
    conv_lhs at density => rw [pow_succ]
    have enough := two_le_weight odd s.property
    rw [Nat.totient_prime_pow_succ Nat.prime_two, show (2:ℕ)-1=1 by decide, mul_one]
    change 2^(k+1) ≤ 16 * Fintype.card (Labels (2^(k+2)) n) * weight n s.val
    exact (show 2^(k+1) ≤ 16 * Fintype.card (Labels (2^(k+2)) n) * 2 by omega).trans
      (Nat.mul_le_mul_left _ enough)

/-- A depth-eleven example has a label with mass only 23/32 of a uniform
label. It rules out a general three-quarters bound. -/
theorem depth_eleven : Fintype.card (Labels 2048 1)=46 ∧ weight 1 (46 : ZMod 2048)=16 := by
  classical
  constructor
  · have h := PrimePowerSumFilter.square_product_count (N:=1) (by decide) 7
    have c : Nat.card {v : ZMod 128 // IsSquare v}=23 := by
      let sq := (univ : Finset (ZMod 128)).image (fun x => x*x)
      have eq : {v : ZMod 128 // IsSquare v} ≃ ↥sq := Equiv.subtypeEquivRight (fun z => by
        simp only [sq, mem_image, mem_univ, true_and, IsSquare]
        exact exists_congr (fun _ => eq_comm))
      rw [Nat.card_congr eq,Nat.card_eq_finsetCard]
      decide +kernel
    change Nat.card (Labels 2048 1) = 2*Nat.card {v : ZMod 128 // IsSquare v} at h
    rw [Nat.card_eq_fintype_card,c] at h
    exact h
  · rw [PrimeFactors.CombinedSumWeights.weight_first,Nat.card_eq_fintype_card,Fintype.card_subtype]
    decide +kernel

/-- The exact local masses give a strict counterexample to three quarters. -/
theorem fails_three_quarters : ∃ s : Labels 2048 1,
    4 * Fintype.card (Labels 2048 1) * weight 1 s.val < 3 * (2048:ℕ).totient := by
  obtain ⟨count, mass⟩ := depth_eleven
  have positive : 0 < weight 1 (46 : ZMod 2048) := by rw [mass]; decide
  refine ⟨⟨46, (positive_iff _).mp positive⟩, ?_⟩
  change 4 * Fintype.card (Labels 2048 1) * weight 1 (46 : ZMod 2048) < _
  rw [count, mass]
  rw [show (2048:ℕ) = 2^(10+1) by decide, Nat.totient_prime_pow_succ Nat.prime_two 10]
  decide

end PrimeFactors.TwoPowerGuessShare
