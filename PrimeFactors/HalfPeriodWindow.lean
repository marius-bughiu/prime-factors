import PrimeFactors.CharacterInterval

/-! Compare nested residue tests on the very same finite progression. The
complete periods force some positions to pass the old test and fail the new
one, regardless of the arrangement of residues in the incomplete period. -/

namespace PrimeFactors.HalfPeriodWindow

open Finset CharacterInterval

variable {d : ℕ} [NeZero d]

/-- A surviving position corresponds bijectively to its block number and
its residue. The inverse first undoes the affine permutation modulo d. -/
theorem full_periods (A : Finset (ZMod d)) (first step B : ℕ)
    (unit : IsUnit (step : ZMod d)) :
    (surviving A first step (B*d)).card = B*A.card := by
  classical
  obtain ⟨u,hu⟩ := unit
  let e := (Units.mulLeft u).trans (Equiv.addLeft (first : ZMod d))
  have eval (r : ZMod d) : e r = first + (step : ZMod d)*r := by
    change (first : ZMod d) + (u : ZMod d)*r = _
    rw [hu]
  let pack (i : ℕ) : ℕ × ZMod d := (i/d,e i)
  let unpack (t : ℕ × ZMod d) := t.1*d + (e.symm t.2).val
  have read (t : ℕ × ZMod d) : pack (unpack t) = t := by
    apply Prod.ext
    · change (t.1*d+(e.symm t.2).val)/d=t.1
      rw [Nat.mul_comm t.1 d,Nat.mul_add_div (NeZero.pos d),Nat.div_eq_of_lt (ZMod.val_lt _),Nat.add_zero]
    · change e ((↑(t.1*d+(e.symm t.2).val) : ZMod d)) = t.2
      simp
  have write (i : ℕ) : unpack (pack i) = i := by
    change (i/d)*d + (e.symm (e (i:ZMod d))).val = i
    rw [e.symm_apply_apply,ZMod.val_natCast,Nat.mul_comm (i/d) d,Nat.div_add_mod]
  calc
    _ = (range B ×ˢ A).card := by
      refine card_bij' (fun i _ => pack i) (fun t _ => unpack t) ?_ ?_
        (fun i _ => write i) (fun t _ => read t)
      · intro i hi
        obtain ⟨bound,member⟩ := mem_filter.mp hi
        exact mem_product.mpr ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul (NeZero.pos d)).mpr
          (mem_range.mp bound)), by simpa only [pack, eval] using member⟩
      · intro t ht
        obtain ⟨bound,member⟩ := mem_product.mp ht
        apply mem_filter.mpr
        constructor
        · apply mem_range.mpr
          calc
            unpack t < t.1*d+d := Nat.add_lt_add_left (ZMod.val_lt _) _
            _ = (t.1+1)*d := (Nat.succ_mul ..).symm
            _ ≤ B*d := Nat.mul_le_mul_right _ (mem_range.mp bound)
        · have h := congrArg Prod.snd (read t)
          change e ((unpack t:ℕ):ZMod d) = t.2 at h
          rwa [← eval,h]
    _ = _ := by simp

/-- If the new test P retains exactly half of the old residue classes O,
its fraction of the actual old survivors in this interval is at most
(B+1)/(2B+1). The cross-multiplied statement includes empty intervals. -/
theorem compare {P O : Finset (ZMod d)} (sub : P ⊆ O) (half : 2*P.card = O.card)
    (first step len B : ℕ) (unit : IsUnit (step : ZMod d))
    (lower : B*d ≤ len) (upper : len ≤ (B+1)*d) :
    (2*B+1)*(surviving P first step len).card ≤ (B+1)*(surviving O first step len).card := by
  classical
  let hits (A : Finset (ZMod d)) := surviving A first step len
  have inside : hits P ⊆ hits O := by
    intro i hi
    obtain ⟨hi,hp⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hi,sub hp⟩
  have diff : hits (O \ P) = hits O \ hits P := by
    ext i
    simp only [hits,surviving,mem_sdiff,mem_filter]
    tauto
  have size := card_sdiff_add_card_eq_card sub
  have balance : (O \ P).card = P.card := by omega
  have guaranteed : B*P.card ≤ (hits O \ hits P).card := by
    rw [← diff,← balance,← full_periods (O \ P) first step B unit]
    exact card_le_card (filter_subset_filter _ (range_mono lower))
  have cap := capacity P first step len (B+1) unit upper
  change (hits P).card ≤ (B+1)*P.card at cap
  have weighted : B*(hits P).card ≤ (B+1)*(hits O \ hits P).card := calc
    _ ≤ B*((B+1)*P.card) := Nat.mul_le_mul_left _ cap
    _ = (B+1)*(B*P.card) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ guaranteed
  change (2*B+1)*(hits P).card ≤ (B+1)*(hits O).card
  calc
    _ = B*(hits P).card + (B+1)*(hits P).card := by ring
    _ ≤ (B+1)*(hits O \ hits P).card + (B+1)*(hits P).card := Nat.add_le_add_right weighted _
    _ = _ := by rw [← Nat.mul_add,card_sdiff_add_card_eq_card inside]

end PrimeFactors.HalfPeriodWindow
