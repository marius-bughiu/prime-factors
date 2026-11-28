import PrimeFactors.FiveSquareSignPopulation

/-! Lossless fixed-width encoding of an attained sum when its product modulo
the five prime squares is already known to the encoder and the decoder. -/
namespace PrimeFactors.FiveSquareSumCodeWidth

open Finset FiveSquareSignRanks
open FiveSquareSignPopulation (m)
open FiveSquareGuessRanks (primes)
open scoped Classical
open private PrimeFactors.FiveSquareSignPopulation.size_from_sum PrimeFactors.FiveSquareSignPopulation.flag
  PrimeFactors.FiveSquareSignPopulation.flag_true from PrimeFactors.FiveSquareSignPopulation
set_option maxRecDepth 4096
attribute [local irreducible] CoprimeGuessTables.modulus Fintype.card

/-- The decoder is allowed to use the same known product n as the encoder. -/
def Fits (n bits : ℕ) : Prop :=
  ∃ encode : Labels n → Fin (2^bits), ∃ decode : Fin (2^bits) → Labels n, Function.LeftInverse decode encode

/-- Finite cardinality is the exact criterion, including existence of a
total decoder on unused bit strings. -/
theorem fits_iff (n bits : ℕ) : Fits n bits ↔ Fintype.card (Labels n)≤2^bits := by
  constructor
  · rintro ⟨encode,_,inv⟩
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective encode inv.injective
  · intro count
    let encode := (Fintype.equivFin (Labels n)).toEmbedding.trans (Fin.castLEEmb count)
    exact ⟨encode,Function.invFun encode,Function.leftInverse_invFun encode.injective⟩

private theorem receipt :
    (∀ b : Pattern,41767264≤labels b ∧ labels b≤122522400) ∧
    labels (fun _ => true)=41767264 ∧ labels (fun _ => false)=122522400 ∧
    (∑ b : Pattern, if labels b≤2^26 then 1 else 0 : ℕ)=14 := by
  decide +kernel

private theorem size (u : (ZMod m)ˣ) : Fintype.card (Labels u.val.val)=labels (sign u.val.val) := by
  have unit : IsUnit (u.val.val:ZMod m) := by rw [ZMod.natCast_zmod_val]; exact u.isUnit
  exact (optimum u.val.val (local_units unit)).1

/-- At a known unit product its five square/nonsquare signs completely
determine whether a proposed fixed width suffices. -/
theorem for_product (u : (ZMod m)ˣ) (bits : ℕ) :
    Fits u.val.val bits ↔ labels (sign u.val.val)≤2^bits := by rw [fits_iff,size]

/-- Every known unit product requires at least 26 bits. -/
theorem necessary (u : (ZMod m)ˣ) {b : ℕ} (h : Fits u.val.val b) : 26≤b := by
  by_contra! small
  have bound := ((receipt.1 _).1.trans ((for_product u b).mp h)).trans
    (Nat.pow_le_pow_right (by decide : 0<2) (show b≤25 by omega))
  exact (by decide : ¬41767264≤2^25) bound

/-- The unit product one attains the smaller width of 26 bits. -/
theorem one_iff (b : ℕ) : Fits 1 b ↔ 26≤b := by
  have sign1 : sign 1=(fun _ => true) := by funext i; simp [sign]
  have sz := (optimum 1 (fun i => (Fact.out : (primes i).Prime).not_dvd_one)).1
  rw [sign1,receipt.2.1] at sz
  rw [fits_iff,sz]
  constructor
  · intro h
    by_contra! small
    exact (by decide : ¬41767264≤2^25) (h.trans (Nat.pow_le_pow_right (by decide) (show b≤25 by omega)))
  · intro h
    exact (by decide : 41767264≤2^26).trans (Nat.pow_le_pow_right (by decide) h)

/-- The small unit product residue 73 attains the worst case. -/
theorem seventy_three_iff (b : ℕ) : Fits 73 b ↔ 27≤b := by
  have flags : ∀ i : Fin 5,PrimeFactors.FiveSquareSignPopulation.flag (primes i) 73=false := by decide +kernel
  have sign73 : sign 73=(fun _ => false) := by
    funext i
    apply decide_eq_false
    intro h
    exact Bool.false_ne_true ((flags i).symm.trans ((PrimeFactors.FiveSquareSignPopulation.flag_true 73).mpr h))
  have unit : ∀ i,¬primes i∣73 := by decide +kernel
  have sz := (optimum 73 unit).1
  rw [sign73,receipt.2.2.1] at sz
  rw [fits_iff,sz]
  constructor
  · intro h
    by_contra! small
    exact (by decide : ¬122522400≤2^26) (h.trans (Nat.pow_le_pow_right (by decide) (show b≤26 by omega)))
  · intro h
    exact (by decide : 122522400≤2^27).trans (Nat.pow_le_pow_right (by decide) h)

/-- Exactly 27 bits are necessary and sufficient for every *unit* product.
A product in the all-nonsquare pattern witnesses the lower bound. -/
theorem all_units_iff (bits : ℕ) : (∀ u : (ZMod m)ˣ,Fits u.val.val bits) ↔ 27≤bits := by
  classical
  constructor
  · intro all
    have count := FiveSquareSignPopulation.pattern_count (fun _ => false)
    have pos := count.symm ▸ (by decide : 0<122522400)
    obtain ⟨u,hu⟩ := card_pos.mp pos
    have cond := (for_product u bits).mp (all u)
    rw [(mem_filter.mp hu).2,receipt.2.2.1] at cond
    by_contra! small
    exact (by decide : ¬122522400≤2^26) (cond.trans (Nat.pow_le_pow_right (by decide) (show bits≤26 by omega)))
  · intro h u
    exact (for_product u bits).mpr (((receipt.1 _).2.trans (by decide : 122522400≤2^27)).trans
      (Nat.pow_le_pow_right (by decide) h))

private theorem counts_of_test {α : Type*} [Fintype α] (P Q : α→Prop)
    [DecidablePred P] [DecidablePred Q] (equivalent : ∀ x,P x ↔ Q x)
    (mass : (∑ a : α, if Q a then 1 else 0 : ℕ)=1715313600)
    (total : Fintype.card α=3920716800) :
    (univ.filter P).card=1715313600 ∧ (univ.filter (fun x => ¬P x)).card=2205403200 := by
  have eq : univ.filter P=univ.filter Q := filter_congr (fun x _ => equivalent x)
  have yes : (univ.filter P).card=1715313600 := eq ▸ (by simpa only [sum_boole] using mass)
  have both := filter_card_add_filter_neg_card_eq_card (s:=univ) P
  rw [card_univ,total,yes] at both
  exact ⟨yes,by omega⟩

/-- The lower width is exact at 14 of 32 equally populated patterns and
fails at the other 18. These counts are of unit residue products. -/
theorem twenty_six_counts :
    ((univ : Finset (ZMod m)ˣ).filter (fun u => Fits u.val.val 26)).card=1715313600 ∧
    ((univ : Finset (ZMod m)ˣ).filter (fun u => ¬Fits u.val.val 26)).card=2205403200 := by
  classical
  let f (b : Pattern) : ℕ := if labels b≤2^26 then 1 else 0
  have sums := FiveSquareSignPopulation.sum_by_pattern f
  rw [show (∑ b : Pattern,f b)=14 from receipt.2.2.2] at sums
  apply counts_of_test _ (fun u => labels (sign u.val.val)≤2^26) (fun u => for_product u 26)
  · exact sums.trans (by decide : (122522400 • (14:ℕ))=1715313600)
  · exact PrimeFactors.FiveSquareSignPopulation.size_from_sum
      (FiveSquareSignPopulation.sum_by_pattern (fun _ => (1:ℕ))) (by simp [Pattern,Fintype.card_pi])

/-- If the product can be a nonunit, the zero product admits every sum
via the pair (0,s). The corresponding uniform width is 33 bits. -/
theorem all_residues_iff (bits : ℕ) : (∀ n : ℕ,Fits n bits) ↔ 33≤bits := by
  let zeroEquiv : Labels 0 ≃ ZMod m := {
    toFun := Subtype.val
    invFun := fun s => ⟨s,0,s,by simp,by simp⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have modValue : m=7239457225 := FiveSquareGuessRanks.modulus_value
  have zeroSize := (Fintype.card_congr zeroEquiv).trans (ZMod.card m)
  constructor
  · intro h
    have fits := (fits_iff 0 bits).mp (h 0)
    rw [zeroSize,modValue] at fits
    by_contra! small
    exact (by decide : ¬7239457225≤2^32) (fits.trans (Nat.pow_le_pow_right (by decide) (show bits≤32 by omega)))
  · intro h n
    have cap := Fintype.card_le_of_injective (fun x : Labels n => x.val) Subtype.val_injective
    rw [ZMod.card] at cap
    change Fintype.card (Labels n)≤m at cap
    rw [modValue] at cap
    exact (fits_iff n bits).mpr ((cap.trans (by decide : 7239457225≤2^33)).trans (Nat.pow_le_pow_right (by decide) h))

end PrimeFactors.FiveSquareSumCodeWidth
