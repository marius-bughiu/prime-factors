import PrimeFactors.PrimePower
import PrimeFactors.ResidueCount

namespace PrimeFactors

open scoped Classical

/-- Reduction to the first base-prime digit. -/
noncomputable def firstPrimeDigit (p k : ℕ) : ZMod (p^(k+1)) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) _

variable {p : ℕ} [Fact p.Prime]

private theorem firstPrimeDigit_isUnit {k : ℕ} {x : ZMod (p^(k+1))}
    (h : firstPrimeDigit p k x ≠ 0) : IsUnit x := by
  obtain ⟨v,rfl⟩ := ZMod.natCast_zmod_surjective x
  rw [map_natCast] at h
  exact (ZMod.isUnit_iff_coprime _ _).mpr <| Nat.Coprime.pow_right _ <|
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun hd => h <|
      (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hd)).symm

private theorem digit_val (k : ℕ) (s : ZMod (p^(k+1))) :
    (firstPrimeDigit p k s).val = s.val % p := by
  conv_lhs => rw [← ZMod.natCast_zmod_val s, map_natCast, ZMod.val_natCast]

private noncomputable def digitFiber (k : ℕ) (r : ZMod p) :
    Fin (p^k) ≃ {s : ZMod (p^(k+1)) // firstPrimeDigit p k s = r} where
  toFun i := ⟨((r.val + p*i.val : ℕ) : ZMod (p^(k+1))), by simp⟩
  invFun s := ⟨s.val.val / p, (Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos).mpr
    (by simpa [pow_succ] using s.val.val_lt)⟩
  left_inv i := by
    apply Fin.ext
    have bound : r.val+p*i.val < p^(k+1) := calc
      _ < p*(i.val+1) := by rw [Nat.mul_add_one]; have := r.val_lt; omega
      _ ≤ p*(p^k) := Nat.mul_le_mul_left p i.isLt
      _ = _ := by rw [pow_succ]; ring
    simp only [ZMod.val_natCast_of_lt bound, Nat.add_mul_div_left _ _ (Fact.out : p.Prime).pos,
      Nat.div_eq_of_lt r.val_lt, Nat.zero_add]
  right_inv s := by
    apply Subtype.ext
    have digit : s.val.val % p = r.val := (digit_val k s.val).symm.trans (congrArg ZMod.val s.property)
    change ((r.val+p*(s.val.val/p) : ℕ) : ZMod (p^(k+1))) = s.val
    rw [← digit, Nat.mod_add_div, ZMod.natCast_zmod_val]

private theorem digit_card (k : ℕ) (r : ZMod p) :
    Nat.card {s : ZMod (p^(k+1)) // firstPrimeDigit p k s = r} = p^k := by
  rw [← Nat.card_congr (digitFiber k r)]
  simp

private theorem square_unit_lift (hodd : p ≠ 2) {k : ℕ} (D : ZMod (p^(k+1)))
    (regular : firstPrimeDigit p k D ≠ 0) :
    IsSquare D ↔ IsSquare (firstPrimeDigit p k D) := by
  obtain ⟨d,rfl⟩ := ZMod.intCast_surjective D
  rw [map_intCast] at regular ⊢
  exact isSquare_primePow_iff_of_unit hodd d regular k

/-- On one nonzero first-digit class the discriminant gives a bijection onto
its own first-digit class, including when the discriminant vanishes there. -/
noncomputable def discriminantDigitEquiv (hodd : p ≠ 2) (k : ℕ)
    (n : ZMod (p^(k+1))) {r : ZMod p} (hr : r ≠ 0) :
    {s : ZMod (p^(k+1)) // firstPrimeDigit p k s = r} ≃
    {D : ZMod (p^(k+1)) // firstPrimeDigit p k D = r^2-4*firstPrimeDigit p k n} := by
  classical
  let f (s : {s : ZMod (p^(k+1)) // firstPrimeDigit p k s = r}) :
      {D : ZMod (p^(k+1)) // firstPrimeDigit p k D = r^2-4*firstPrimeDigit p k n} :=
    ⟨s.val^2-4*n, by simp [s.property, map_ofNat]⟩
  refine Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩)
  · intro x y h
    have hs : x.val^2-4*n = y.val^2-4*n := congrArg Subtype.val h
    have hu : IsUnit (x.val+y.val) := by
      apply firstPrimeDigit_isUnit
      rw [map_add,x.property,y.property,← two_mul]
      exact mul_ne_zero (Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])) hr
    apply Subtype.ext
    apply eq_of_sub_eq_zero
    apply hu.mul_right_cancel
    linear_combination hs
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, digit_card,digit_card]

private theorem two_unit (hodd : p ≠ 2) (e : ℕ) : IsUnit (2 : ZMod (p^e)) :=
  (ZMod.isUnit_iff_coprime 2 _).mpr
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two Fact.out).mpr hodd.symm))

private theorem double_ne_zero (hodd : p ≠ 2) : (2 : ZMod p) ≠ 0 :=
  Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])

/-- A singular first-digit class contributes exactly the number of squares
reducing to zero, counted as distinct residues. -/
theorem card_admissible_singular_digit (hodd : p ≠ 2) (k : ℕ)
    (n : ZMod (p^(k+1))) (unitN : firstPrimeDigit p k n ≠ 0) {r : ZMod p}
    (sing : r^2-4*firstPrimeDigit p k n = 0) :
    Nat.card {s : ZMod (p^(k+1)) // firstPrimeDigit p k s = r ∧ AdmissibleSum n s} =
      Nat.card {D : ZMod (p^(k+1)) // firstPrimeDigit p k D = 0 ∧ IsSquare D} := by
  have hr : r ≠ 0 := by
    intro z
    rw [z, zero_pow (by decide),zero_sub,neg_eq_zero] at sing
    exact (mul_ne_zero (by convert mul_ne_zero (double_ne_zero hodd) (double_ne_zero hodd) using 1
                           norm_num) unitN) sing
  let e := discriminantDigitEquiv hodd k n hr
  have sub := e.subtypeEquiv (p := fun s => AdmissibleSum n s.val) (q := fun D => IsSquare D.val)
    (fun s => admissibleSum_iff_isSquare_of_two_unit (two_unit hodd _) n s.val)
  have cert := Nat.card_congr (((Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans sub).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _))
  simpa [sing] using cert

/-- Each regular first digit contributes either all its lifts or none. -/
theorem card_admissible_regular_digit (hodd : p ≠ 2) (k : ℕ)
    (n : ZMod (p^(k+1))) {r : ZMod p} (reg : r^2-4*firstPrimeDigit p k n ≠ 0) :
    Nat.card {s : ZMod (p^(k+1)) // firstPrimeDigit p k s = r ∧ AdmissibleSum n s} =
      if _ : AdmissibleSum (firstPrimeDigit p k n) r then p^k else 0 := by
  classical
  have iffAt (s : ZMod (p^(k+1))) (hs : firstPrimeDigit p k s = r) :
      AdmissibleSum n s ↔ AdmissibleSum (firstPrimeDigit p k n) r := by
    have digit : firstPrimeDigit p k (s^2-4*n) = r^2-4*firstPrimeDigit p k n := by simp [hs, map_ofNat]
    rw [admissibleSum_iff_isSquare_of_two_unit (two_unit hodd _) n s,
      admissibleSum_iff_isSquare hodd, ← digit]
    exact square_unit_lift hodd _ (digit ▸ reg)
  split_ifs with yes
  · exact (Nat.card_congr (Equiv.subtypeEquivRight (fun s =>
      and_iff_left_of_imp (fun hs => (iffAt s hs).mpr yes)))).trans (digit_card _ _)
  · apply Nat.card_eq_zero.mpr
    exact Or.inl ⟨fun s => yes ((iffAt _ s.property.1).mp s.property.2)⟩


private noncomputable def scaleByPrimeSquare (p k : ℕ) (z : ZMod (p^k)) : ZMod (p^(k+2)) :=
  ((p^2*z.val : ℕ) : ZMod (p^(k+2)))

omit [Fact p.Prime] in
private theorem scale_natCast (k v : ℕ) :
    scaleByPrimeSquare p k (v : ZMod (p^k)) = ((p^2*v : ℕ) : ZMod (p^(k+2))) := by
  unfold scaleByPrimeSquare
  rw [ZMod.val_natCast, ZMod.natCast_eq_natCast_iff, pow_add, mul_comm (p^k)]
  exact (Nat.mod_modEq v (p^k)).mul_left' _

private theorem scale_injective (k : ℕ) : Function.Injective (scaleByPrimeSquare p k) := by
  intro x y h
  obtain ⟨a,rfl⟩ := ZMod.natCast_zmod_surjective x
  obtain ⟨b,rfl⟩ := ZMod.natCast_zmod_surjective y
  rw [scale_natCast,scale_natCast,ZMod.natCast_eq_natCast_iff,pow_add,mul_comm (p^k)] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr <|
    Nat.ModEq.mul_left_cancel' (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero) h

/-- Removing the two factors of the base prime identifies all singular squares
with the distinct squares two levels lower. The zero square is included. -/
theorem card_squares_zero_digit (k : ℕ) :
    Nat.card {D : ZMod (p^(k+2)) // firstPrimeDigit p (k+1) D = 0 ∧ IsSquare D} =
      Nat.card {d : ZMod (p^k) // IsSquare d} := by
  let f (d : {d : ZMod (p^k) // IsSquare d}) :
      {D : ZMod (p^(k+2)) // firstPrimeDigit p (k+1) D = 0 ∧ IsSquare D} :=
    ⟨scaleByPrimeSquare p k d.val, by
      obtain ⟨z,hz⟩ := d.property
      obtain ⟨t,rfl⟩ := ZMod.natCast_zmod_surjective z
      rw [hz, ← Nat.cast_mul, scale_natCast]
      constructor
      · simp
      · exact ⟨((p*t : ℕ) : ZMod (p^(k+2))), by push_cast; ring⟩⟩
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_,?_⟩)).symm
  · exact fun _ _ h => Subtype.ext (scale_injective k (congrArg Subtype.val h))
  · rintro ⟨D, hd, z,hz⟩
    obtain ⟨v,rfl⟩ := ZMod.natCast_zmod_surjective z
    rw [hz, map_mul,map_natCast,mul_self_eq_zero] at hd
    obtain ⟨t,rfl⟩ := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp hd
    refine ⟨⟨((t*t : ℕ) : ZMod (p^k)), ⟨(t : ZMod (p^k)), Nat.cast_mul _ _⟩⟩,?_⟩
    apply Subtype.ext
    change scaleByPrimeSquare p k ((t*t : ℕ) : ZMod (p^k)) = D
    rw [scale_natCast, hz]
    push_cast
    ring

/-- For any predicate, split a residue count by first digit. -/
private theorem count_digits (k : ℕ) (P : ZMod (p^(k+1)) → Prop) :
    Nat.card {s // P s} = ∑ r : ZMod p, Nat.card {s // firstPrimeDigit p k s = r ∧ P s} := by
  classical
  let f (s : {s // P s}) := firstPrimeDigit p k s.val
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  exact Nat.card_congr <| (Equiv.subtypeSubtypeEquivSubtypeInter P (fun s => firstPrimeDigit p k s = r)).trans <|
    Equiv.subtypeEquivRight (fun _ => and_comm)

private theorem count_if (P : ZMod p → Prop) [DecidablePred P] (a : ℕ) :
    (∑ r : ZMod p, if P r then a else 0) = Nat.card {r // P r} * a := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [← Finset.sum_filter]

private theorem unit_square_count (hodd : p ≠ 2) :
    Nat.card {r : ZMod p // r ≠ 0 ∧ IsSquare r} = (p-1)/2 := by
  classical
  let D := Finset.univ.erase (0 : ZMod p)
  let S := Finset.univ.filter (fun r : ZMod p => r ≠ 0 ∧ IsSquare r)
  have maps : Set.MapsTo (fun r : ZMod p => r^2) D S := by
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      pow_ne_zero _ (Finset.mem_erase.mp hr).1, ⟨r,pow_two _⟩⟩
  have card := Finset.card_eq_sum_card_fiberwise maps
  have per (r : ZMod p) (hr : r ∈ S) : (D.filter (fun z => z^2=r)).card = 2 := by
    obtain ⟨_,hn,hs⟩ := Finset.mem_filter.mp hr
    exact card_squareRootsMod_of_square p hodd r hn hs
  rw [Finset.sum_congr rfl per] at card
  have total : D.card = p-1 := by simp [D,Finset.card_erase_of_mem]
  rw [total] at card
  simp only [Finset.sum_const, smul_eq_mul] at card
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  change S.card = _
  omega

private theorem count_digit_units (hodd : p ≠ 2) (k : ℕ) {r : ZMod p} (hr : r ≠ 0) :
    Nat.card {s : ZMod (p^(k+1)) // firstPrimeDigit p k s = r ∧ IsSquare s} =
      if IsSquare r then p^k else 0 := by
  have iffAt (s : ZMod (p^(k+1))) (hs : firstPrimeDigit p k s = r) : IsSquare s ↔ IsSquare r := by
    rw [← hs]
    exact square_unit_lift hodd s (hs ▸ hr)
  split_ifs with yes
  · exact (Nat.card_congr (Equiv.subtypeEquivRight (fun s =>
      and_iff_left_of_imp (fun hs => (iffAt s hs).mpr yes)))).trans (digit_card _ _)
  · exact Nat.card_eq_zero.mpr (Or.inl ⟨fun s => yes ((iffAt _ s.property.1).mp s.property.2)⟩)

private theorem count_squares_succ (hodd : p ≠ 2) (k : ℕ) :
    Nat.card {s : ZMod (p^(k+1)) // IsSquare s} =
      ((p-1)/2)*p^k + Nat.card {s : ZMod (p^(k+1)) // firstPrimeDigit p k s = 0 ∧ IsSquare s} := by
  rw [count_digits]
  calc
    _ = ∑ r : ZMod p, ((if r ≠ 0 ∧ IsSquare r then p^k else 0) +
      (if r = 0 then Nat.card {s : ZMod (p^(k+1)) // firstPrimeDigit p k s = 0 ∧ IsSquare s} else 0)) := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases z : r=0
        · simp [z]
        · rw [count_digit_units hodd k z]
          by_cases hs : IsSquare r <;> simp [hs,z]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      · exact (count_if (fun r : ZMod p => r ≠ 0 ∧ IsSquare r) _).trans
          (congrArg (fun v => v*p^k) (unit_square_count hodd))
      · simp

/-- Number of distinct square residues. Every singular square at level `e+2`
comes from one square at level `e`. -/
def primePowerSquareCount (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => (p-1)/2+1
  | k+2 => ((p-1)/2)*p^(k+1)+primePowerSquareCount p k

theorem card_primePower_squares (hodd : p ≠ 2) (e : ℕ) :
    Nat.card {s : ZMod (p^e) // IsSquare s} = primePowerSquareCount p e := by
  match e with
  | 0 =>
    rw [pow_zero,primePowerSquareCount]
    exact Nat.card_eq_one_iff_exists.mpr
      ⟨⟨0,⟨0,by simp⟩⟩, fun _ => Subsingleton.elim _ _⟩
  | 1 =>
    rw [show 1=0+1 by rfl,count_squares_succ hodd,primePowerSquareCount]
    simp only [pow_zero,mul_one,Nat.add_right_inj]
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨0,by simp⟩,fun s => Subtype.ext ?_⟩
    obtain ⟨a,ha⟩ := ZMod.natCast_zmod_surjective s.val
    have h := s.property.1
    rw [← ha,map_natCast] at h
    rw [← ha]
    apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr
    simpa using (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h
  | k+2 =>
    rw [count_squares_succ hodd (k+1),card_squares_zero_digit,card_primePower_squares hodd k]
    rfl


/-- Number contributed by each colliding first-digit class at precision `k+1`. -/
def collidingDigitCount (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => primePowerSquareCount p k

private theorem zero_digit_count (hodd : p ≠ 2) (k : ℕ) :
    Nat.card {s : ZMod (p^(k+1)) // firstPrimeDigit p k s = 0 ∧ IsSquare s} =
      collidingDigitCount p k := by
  cases k with
  | zero =>
    have h := count_squares_succ (p := p) hodd 0
    rw [card_primePower_squares hodd] at h
    simp only [primePowerSquareCount,pow_zero,mul_one,Nat.add_left_cancel_iff] at h
    exact h.symm
  | succ k => exact (card_squares_zero_digit k).trans (card_primePower_squares hodd k)

private theorem base_singular_count (hodd : p ≠ 2) {n : ZMod p} (hn : n ≠ 0) :
    Nat.card {r : ZMod p // r^2-4*n = 0} = if IsSquare n then 2 else 0 := by
  have four : (4 : ZMod p) ≠ 0 := by
    convert mul_ne_zero (double_ne_zero hodd) (double_ne_zero hodd) using 1
    norm_num
  have nonzero := mul_ne_zero four hn
  have card : Nat.card {r : ZMod p // r^2-4*n = 0} = (squareRootsMod p (4*n)).card := by
    rw [← Fintype.card_coe,← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    simp only [sub_eq_zero,squareRootsMod,Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,and_true]
    constructor
    · intro h
      exact ⟨fun z => nonzero (by rw [← h,z]; simp),h⟩
    · exact And.right
  rw [card]
  split_ifs with sq
  · exact card_squareRootsMod_of_square p hodd _ nonzero ((show IsSquare (4 : ZMod p) from ⟨2,by norm_num⟩).mul sq)
  · apply card_squareRootsMod_of_nonsquare
    rintro ⟨u,hu⟩
    apply sq
    exact ⟨u/2, by field_simp [double_ne_zero hodd]; linear_combination hu⟩

private theorem count_first_digit_sums (hodd : p ≠ 2) {n : ZMod p} (hn : n ≠ 0) :
    Nat.card {r : ZMod p // AdmissibleSum n r} =
      if IsSquare n then (p+1)/2 else (p-1)/2 := by
  rw [card_admissibleSum_eq p n hn]
  split_ifs with h
  · exact card_factorSumResidues_of_square p hodd n hn h
  · exact card_factorSumResidues_of_nonsquare p n hn h

/-- Exact count for a product that is a unit at an odd prime. The Boolean
is its quadratic-residue status modulo the prime. -/
def primePowerSumCount (p : ℕ) (square : Bool) : ℕ → ℕ
  | 0 => 1
  | k+1 => if square then (p-3)/2*p^k+2*collidingDigitCount p k else (p-1)/2*p^k

/-- Computing the count uses one base-prime quadratic character and the
square recurrence. This includes arbitrary collisions and zero discriminants. -/
theorem card_primePower_admissibleSum (hodd : p ≠ 2) (k : ℕ) (n : ZMod (p^(k+1)))
    (unitN : firstPrimeDigit p k n ≠ 0) :
    Nat.card {s // AdmissibleSum n s} =
      primePowerSumCount p (decide (IsSquare (firstPrimeDigit p k n))) (k+1) := by
  let m := firstPrimeDigit p k n
  let F := fun r : ZMod p => Nat.card {s // firstPrimeDigit p k s = r ∧ AdmissibleSum n s}
  let S := fun r : ZMod p => r^2-4*m = 0
  let c := collidingDigitCount p k
  have balance (r : ZMod p) :
      F r + (if S r then p^k else 0) =
        (if AdmissibleSum m r then p^k else 0) + (if S r then c else 0) := by
    by_cases h : S r
    · have accept : AdmissibleSum m r := (admissibleSum_iff_isSquare hodd m r).mpr (by
        change r^2-4*m = 0 at h
        rw [h]; exact ⟨0,by simp⟩)
      have count := (card_admissible_singular_digit hodd k n unitN h).trans (zero_digit_count hodd k)
      simp only [F, count, h,accept,if_true]
      exact Nat.add_comm _ _
    · have count := card_admissible_regular_digit hodd k n h
      simp only [h,if_false,add_zero]
      exact count
  have all := Finset.sum_congr (show (Finset.univ : Finset (ZMod p)) = Finset.univ from rfl) (fun r _ => balance r)
  simp only [Finset.sum_add_distrib] at all
  rw [count_if S, count_if (AdmissibleSum m),count_if S,
    base_singular_count hodd unitN,count_first_digit_sums hodd unitN] at all
  rw [count_digits]
  change ∑ r, F r = _
  by_cases sq : IsSquare m
  · change IsSquare (firstPrimeDigit p k n) at sq
    simp only [sq,if_true] at all
    simp only [sq,decide_true, primePowerSumCount,if_true,Bool.true_eq]
    have base : (p+1)/2 = (p-3)/2+2 := by
      have hp := (Fact.out : p.Prime).two_le
      omega
    rw [base,Nat.add_mul] at all
    dsimp [c] at all
    omega
  · change ¬ IsSquare (firstPrimeDigit p k n) at sq
    simp only [sq,if_false,zero_mul,add_zero] at all
    simpa only [sq,decide_false,primePowerSumCount,Bool.false_eq_true,if_false] using all


private theorem colliding_step (p k : ℕ) :
    collidingDigitCount p (k+2) = ((p-1)/2)*p^k+collidingDigitCount p k := by
  cases k with
  | zero => simp [collidingDigitCount,primePowerSquareCount]
  | succ k => rfl

/-- Closed form for a colliding class, with the parity correction intact. -/
theorem collidingDigitCount_closed (hodd : p ≠ 2) (k : ℕ) :
    2*(p+1)*collidingDigitCount p k = p^k + (if Even k then 2*p+1 else p+2) := by
  match k with
  | 0 => simp [collidingDigitCount]; omega
  | 1 => simp [collidingDigitCount,primePowerSquareCount]; omega
  | k+2 =>
    have ih := collidingDigitCount_closed hodd k
    have even : Even (k+2) ↔ Even k := by simp [Nat.even_add]
    rw [colliding_step, if_congr even rfl rfl, pow_add]
    have half : 2*((p-1)/2)+1=p := by
      obtain ⟨i,hi⟩ := (Fact.out : p.Prime).odd_of_ne_two hodd
      omega
    nlinarith only [ih,congrArg (fun v : ℕ => (p+1)*p^k*v) half]

/-- Division-free form of the closed count for a square product. At precision
`k+1` the bounded correction depends only on the parity of `k`. -/
theorem primePowerSumCount_closed_square (hodd : p ≠ 2) (k : ℕ) :
    2*(p+1)*primePowerSumCount p true (k+1) + (2*p+1)*p^k =
      p^2*p^k + 2*(if Even k then 2*p+1 else p+2) := by
  have half : 2*((p-3)/2)+3=p := by
    obtain ⟨i,hi⟩ := (Fact.out : p.Prime).odd_of_ne_two hodd
    have := (Fact.out : p.Prime).two_le
    omega
  simp only [primePowerSumCount,Bool.true_eq,if_true]
  nlinarith only [collidingDigitCount_closed hodd k, congrArg (fun v : ℕ => (p+1)*p^k*v) half]

/-- Uniform local density at every odd prime power is at least one twelfth.
The closed form shows that `p=3` with square product approaches this bound. -/
theorem primePowerSumCount_density (hodd : p ≠ 2) (k : ℕ) (square : Bool) :
    p^(k+1) ≤ 12 * primePowerSumCount p square (k+1) := by
  have hp := (Fact.out : p.Prime).two_le
  obtain ⟨i,hi⟩ := (Fact.out : p.Prime).odd_of_ne_two hodd
  rw [pow_succ]
  cases square with
  | false =>
    simpa [primePowerSumCount,mul_comm,mul_left_comm,mul_assoc] using
      Nat.mul_le_mul_left (p^k) (show p ≤ 12*((p-1)/2) by omega)
  | true =>
    by_cases three : p=3
    · rw [three]
      letI : Fact (Nat.Prime 3) := ⟨by decide⟩
      have closed := collidingDigitCount_closed (p := 3) (by decide) k
      simp only [primePowerSumCount,Bool.true_eq,if_true]
      norm_num at closed ⊢
      omega
    · have base : p ≤ 12*((p-3)/2) := by omega
      have lower := Nat.mul_le_mul_left (p^k) base
      simp only [primePowerSumCount,Bool.true_eq,if_true]
      nlinarith only [lower]

/-- Counts of distinct admissible sums at the first six powers of three for
a unit product in the square class. -/
theorem ternary_square_sum_counts :
    [1, 2, 3, 4, 5, 6].map (primePowerSumCount 3 true) = [2, 2, 4, 8, 22, 62] := by decide

end PrimeFactors
