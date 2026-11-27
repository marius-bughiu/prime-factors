import PrimeFactors.ReciprocalAdaptiveCharacter

/-! Select one orientation of each pair of opposite nonzero residues by
evaluating a tag only on the smaller ordinary representative. If the tag
recovers the factor's Jacobi sign at ordinary traces, the selected
ordinary traces are exactly the positive factor sums. -/
namespace PrimeFactors.OrientedTraceClasses

open Finset TraceFoldedRight ReciprocalSumCharacter ReciprocalDivisorSums ReciprocalTraceHalving

variable {d : ℕ} [NeZero d]

/-- Only the tag of the smaller of s and −s is queried. The positive tag
selects that smaller residue; every other value selects its negative. -/
def accepts (tag : ZMod d → ℤ) (s : ZMod d) : Bool :=
  if s = 0 then false
  else if s.val < (-s).val then decide (tag s = 1) else decide (tag (-s) ≠ 1)

/-- The full residue set for the pointwise selector. Evaluating membership
requires no table and no enumeration of units. -/
noncomputable def selected (tag : ZMod d → ℤ) : Finset (ZMod d) :=
  (univ.erase 0).filter (fun s => accepts tag s)

theorem mem_selected (tag : ZMod d → ℤ) (s : ZMod d) :
    s ∈ selected tag ↔ accepts tag s = true := by
  by_cases zero : s = 0
  · simp [zero, selected, accepts]
  · simp [selected, zero]

/-- There is no nonzero fixed point of negation at an odd modulus. -/
private theorem different (odd : Odd d) {s : ZMod d} (nz : s ≠ 0) : s.val ≠ (-s).val := by
  letI : NeZero s := ⟨nz⟩
  rw [ZMod.val_neg_of_ne_zero]
  have h := Nat.odd_iff.mp odd
  have v := ZMod.val_lt s
  omega

private theorem flip (odd : Odd d) (tag : ZMod d → ℤ) {s : ZMod d} (nz : s ≠ 0) :
    accepts tag (-s) = !(accepts tag s) := by
  simp only [accepts, if_neg nz, if_neg (neg_ne_zero.mpr nz), neg_neg]
  obtain lt | gt := lt_or_gt_of_ne (different odd nz)
  · simp [lt, not_lt_of_ge lt.le]
  · simp [gt, not_lt_of_ge gt.le]

/-- Exactly (d−1)/2 of all residues pass, regardless of the values of the
tag on residues for which no factor pair with the given sum exists. -/
theorem selected_card (odd : Odd d) (tag : ZMod d → ℤ) :
    (selected tag).card = (d-1)/2 := by
  classical
  let U := (univ : Finset (ZMod d)).erase 0
  have eq : (selected tag).card = (U.filter (fun s => ¬ accepts tag s = true)).card := by
    refine card_bij' (fun s _ => -s) (fun s _ => -s) ?_ ?_ ?_ ?_
    · intro s hs
      obtain ⟨hs,h⟩ := mem_filter.mp hs
      have nz := (mem_erase.mp hs).1
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨neg_ne_zero.mpr nz,mem_univ _⟩,
        by simp [flip odd tag nz,h]⟩
    · intro s hs
      obtain ⟨hs,h⟩ := mem_filter.mp hs
      have nz := (mem_erase.mp hs).1
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨neg_ne_zero.mpr nz,mem_univ _⟩,
        by simp [flip odd tag nz,h]⟩
    · simp
    · simp
  have total := filter_card_add_filter_neg_card_eq_card (s := U) (fun s => accepts tag s = true)
  change (selected tag).card + _ = _ at total
  rw [← eq] at total
  have card : U.card = d-1 := by simp [U,ZMod.card]
  omega

/-- Emit one residue, using just one call of the tag on the small index. -/
def residueAt (tag : ZMod d → ℤ) (j : ZMod d) : ZMod d :=
  if tag j = 1 then j else -j

/-- Traversing precisely the integers 1 through (d−1)/2 emits every selected
residue once, with no search for representatives and no final deduplication. -/
theorem generate (odd : Odd d) (tag : ZMod d → ℤ) :
    Set.InjOn (fun j : ℕ => residueAt tag j) (Icc 1 ((d-1)/2) : Finset ℕ) ∧
    (Icc 1 ((d-1)/2)).image (fun j : ℕ => residueAt tag j) = selected tag := by
  have data (i : ℕ) (hi : i ∈ Icc 1 ((d-1)/2)) :
      (i : ZMod d) ≠ 0 ∧ (i : ZMod d).val = i ∧ (i : ZMod d).val < (-(i : ZMod d)).val := by
    obtain ⟨lo,hi⟩ := mem_Icc.mp hi
    have positive := NeZero.pos d
    have v : (i : ZMod d).val = i := ZMod.val_natCast_of_lt (by omega)
    have nz : (i : ZMod d) ≠ 0 := by
      intro zero
      rw [zero,ZMod.val_zero] at v
      omega
    letI : NeZero (i : ZMod d) := ⟨nz⟩
    refine ⟨nz,v,?_⟩
    rw [ZMod.val_neg_of_ne_zero,v]
    omega
  let index (s : ZMod d) := min s.val (-s).val
  have read (j : ℕ) (hj : j ∈ Icc 1 ((d-1)/2)) : index (residueAt tag j) = j := by
    obtain ⟨_,v,small⟩ := data j hj
    unfold residueAt
    split
    · exact (min_eq_left small.le).trans v
    · simpa only [index,neg_neg,min_eq_right small.le] using v
  have inj : Set.InjOn (fun j : ℕ => residueAt tag j) (Icc 1 ((d-1)/2) : Finset ℕ) := by
    intro i hi j hj eq
    exact (read i hi).symm.trans ((congrArg index eq).trans (read j hj))
  refine ⟨inj,eq_of_subset_of_card_le ?_ ?_⟩
  · intro s hs
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hs
    obtain ⟨nz,_,small⟩ := data i hi
    rw [mem_selected]
    by_cases yes : tag (i : ZMod d) = 1
    · rw [residueAt,if_pos yes,accepts,if_neg nz,if_pos small,decide_eq_true_eq]
      exact yes
    · rw [residueAt,if_neg yes,accepts,if_neg (neg_ne_zero.mpr nz),neg_neg,
        if_neg (not_lt_of_ge small.le),decide_eq_true_eq]
      exact yes
  · rw [selected_card odd,card_image_of_injOn inj,Nat.card_Icc,Nat.add_sub_cancel]

/-- With a square unit product, zero fails the ordinary discriminant test
at every modulus congruent to 3 modulo 4. -/
theorem zero_not_ordinary (hd : d % 4 = 3) (n : (ZMod d)ˣ) (square : IsSquare (n : ZMod d)) :
    0 ∉ ordinary n := by
  intro member
  obtain ⟨x,hx⟩ := (mem_ordinary (Nat.odd_iff.mpr (by omega))).mp member
  have same := same_sign n x (-x) square (by rw [neg_local_sum,hx,neg_zero])
  change sign (x : ZMod d) = sign (-(x : ZMod d)) at same
  rw [sign_neg hd] at same
  rcases ReciprocalDivisorClasses.unit_sign x with h|h <;> omega

/-- The pointwise test recovers a trace's factor sign. Agreement is only
needed on traces that actually arise from units. -/
theorem trace_selected_iff (hd : d % 4 = 3) (n : (ZMod d)ˣ) (square : IsSquare (n : ZMod d))
    (tag : ZMod d → ℤ) (agrees : ∀ x : (ZMod d)ˣ, tag (trace n x) = sign (x : ZMod d))
    (x : (ZMod d)ˣ) : trace n x ∈ selected tag ↔ sign (x : ZMod d) = 1 := by
  have odd : Odd d := Nat.odd_iff.mpr (by omega)
  have nz : trace n x ≠ 0 := fun h => zero_not_ordinary hd n square
    ((mem_ordinary odd).mpr ⟨x,h⟩)
  have neg := agrees (-x)
  change tag (trace n (-x)) = sign (-(x : ZMod d)) at neg
  rw [neg_local_sum,sign_neg hd] at neg
  rw [mem_selected,accepts,if_neg nz]
  split
  · simp only [decide_eq_true_eq,agrees]
  · simp only [decide_eq_true_eq,neg]
    rcases ReciprocalDivisorClasses.unit_sign x with h|h <;> omega

/-- Among the ordinary square-admissible residues this pointwise test agrees
exactly with the image obtained by traversing all positive unit pairs. -/
theorem selected_inter_ordinary (hd : d % 4 = 3) (n : (ZMod d)ˣ) (square : IsSquare (n : ZMod d))
    (tag : ZMod d → ℤ) (agrees : ∀ x : (ZMod d)ˣ, tag (trace n x) = sign (x : ZMod d)) :
    selected tag ∩ ordinary n = sums n := by
  have odd : Odd d := Nat.odd_iff.mpr (by omega)
  ext s
  constructor
  · intro h
    obtain ⟨keep,old⟩ := mem_inter.mp h
    obtain ⟨x,rfl⟩ := (mem_ordinary odd).mp old
    exact mem_image.mpr ⟨x,(pos_mem x).mpr ((trace_selected_iff hd n square tag agrees x).mp keep),rfl⟩
  · intro h
    obtain ⟨x,hx,rfl⟩ := mem_image.mp h
    exact mem_inter.mpr ⟨(trace_selected_iff hd n square tag agrees x).mpr ((pos_mem x).mp hx),
      (mem_ordinary odd).mpr ⟨x,rfl⟩⟩

/-- A true odd factor sum always passes when both public square witnesses
and the ordinary-trace tag identity are available. -/
theorem preserves {p q : ℕ} {a : ℤ} (hd : d % 4 = 3) (hp : Odd p) (hq : Odd q)
    (cop : (p*q).Coprime d) (root : ((p*q : ℕ) : ℤ) ∣ a^2+d)
    (square : IsSquare ((p*q : ℕ) : ZMod d)) (tag : ZMod d → ℤ)
    (agrees : ∀ x : (ZMod d)ˣ, tag (trace (ZMod.unitOfCoprime (p*q) cop) x) = sign (x : ZMod d)) :
    ((p+q : ℕ) : ZMod d) ∈ selected tag := by
  have mem := (ReciprocalDivisorSums.covers hd hp hq cop root).2
  rw [← selected_inter_ordinary hd _ square tag agrees] at mem
  exact (mem_inter.mp mem).1

/-- The explicit tag from saturated gcd and two Jacobi evaluations satisfies
the ordinary-class specification without knowing either factor. -/
theorem adaptive_exact (hd : d % 4 = 3) (n : (ZMod d)ˣ) (e : ZMod d)
    (square : e^2 = (n : ZMod d)) :
    selected (ReciprocalAdaptiveCharacter.tag e) ∩ ordinary n = sums n := by
  exact selected_inter_ordinary hd n ⟨e,by simpa only [pow_two] using square.symm⟩ _
    (ReciprocalAdaptiveCharacter.tag_trace (Nat.odd_iff.mpr (by omega)) n e square)

/-- End-to-end preservation from the two public certificates. -/
theorem adaptive_preserves {p q : ℕ} {a : ℤ} (hd : d % 4 = 3) (hp : Odd p) (hq : Odd q)
    (cop : (p*q).Coprime d) (root : ((p*q : ℕ) : ℤ) ∣ a^2+d) (e : ZMod d)
    (square : e^2 = ((p*q : ℕ) : ZMod d)) :
    accepts (ReciprocalAdaptiveCharacter.tag e) ((p+q : ℕ) : ZMod d) = true := by
  rw [← mem_selected]
  have mem := (ReciprocalDivisorSums.covers hd hp hq cop root).2
  rw [← adaptive_exact hd _ e square] at mem
  exact (mem_inter.mp mem).1

/-- On the composite control D=15, the seven unconditionally generated
classes include exactly the three attainable positive traces. -/
theorem composite_example :
    let C := selected (ReciprocalAdaptiveCharacter.tag (1 : ZMod 15))
    C.card = 7 ∧ C ∩ ordinary (1 : (ZMod 15)ˣ) = {2,8,10} := by
  constructor
  · exact selected_card (by decide +kernel : Odd 15) _
  · rw [adaptive_exact (by decide) 1 1 (by simp)]
    exact ReciprocalDivisorSums.composite_example.2.2.2.1

end PrimeFactors.OrientedTraceClasses
