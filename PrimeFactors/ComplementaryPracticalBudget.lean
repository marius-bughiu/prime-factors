import PrimeFactors.ComplementaryBatch
import PrimeFactors.TwelvePracticalBudget

namespace PrimeFactors.ComplementaryPracticalBudget
open Finset hiding fold
open TwelveResidueCollision TwelveImageSize ComplementaryKeys TwelvePracticalBudget

set_option exponentiation.threshold 2050
set_option maxHeartbeats 900000

private noncomputable def bad (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (univ.filter fun x => mask x=0) ∪ ((regulars p).filter fun x => value x=1-value x)

private theorem bad_card {p : ℕ} [Fact p.Prime] (big : 864<p) : (bad p).card≤25 := by
  exact (card_union_le _ _).trans (Nat.add_le_add (exceptions (p:=p)) (middle_bound big))

private theorem good {p : ℕ} [Fact p.Prime] {x : ZMod p} (h : x∉bad p) :
    x∈regulars p ∧ value x≠1-value x := by
  simp [bad,regulars] at h ⊢
  tauto

noncomputable def capacity (p : ℕ) [Fact p.Prime] : ℕ := by
  classical exact 12 + (if IsSquare (3:ZMod p) then 12 else 0)

private noncomputable def row {p : ℕ} [Fact p.Prime] (x : ZMod p) : Finset (ZMod p) :=
  if x∈bad p then ∅ else (regulars p).filter fun y => fold (value x)=fold (value y)

private theorem row_card {p : ℕ} [Fact p.Prime] (big : 864<p) (x : ZMod p) :
    (row x).card≤capacity p := by
  unfold row
  split_ifs with h
  · simp
  · exact (fold_count big (good h).1 (good h).2).le

private noncomputable def single (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :=
  (bad p ×ˢ (univ : Finset (ZMod q))) ∪ ((univ : Finset (ZMod p)) ×ˢ bad q)

private noncomputable def pair {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (z : ZMod p × ZMod q) :=
  (row z.1 ×ˢ (univ : Finset (ZMod q))) ∪ ((univ : Finset (ZMod p)) ×ˢ row z.2)

/-- Unrestricted draws are charged for every setup exception, every local
middle, and every folded nonunit difference. A global tie counts even when
neither of its orientations splits. -/
def SearchEvent {n m : ℕ} (w : Fin m → ZMod n) : Prop :=
  (∃ i, ¬IsUnit (mask (w i))) ∨
  (∃ i a, a*den (w i)=num (w i) ∧ ¬IsUnit (2*a-1)) ∨
  ∃ i j, i<j ∧ ∃ a b, a*den (w i)=num (w i) ∧ b*den (w j)=num (w j) ∧
    ¬IsUnit (fold a-fold b)

/-- Both original-label and complementary-label comparisons are included
in the folded test, over the public ring itself. -/
theorem folded_covers {R : Type*} [CommRing R] {a b : R}
    (hit : ¬IsUnit (a-b) ∨ ¬IsUnit (a+b-1)) : ¬IsUnit (fold a-fold b) := by
  have eq : fold a-fold b = -(a-b)*(a+b-1) := by unfold fold; ring
  intro unit
  rw [eq,IsUnit.mul_iff] at unit
  exact hit.elim (fun no => no (by simpa only [neg_neg] using unit.1.neg)) (fun no => no unit.2)

/-- The targeted all-ordered-pair product, including self pairs, is also
covered on every regular word. A raw word with a discarded seed already
satisfies the first clause of SearchEvent. -/
theorem directed_covered {n m : ℕ} [NeZero n] (two : IsUnit (2:ZMod n))
    (x : Fin m → TwelveSeedBirthday.Input n) (hit : ¬IsUnit (ComplementaryBatch.directedProduct x)) :
    SearchEvent (fun i => (x i).val) := by
  classical
  let a i := TwelveSeedBirthday.publicKey (x i)
  have readAt (i) : a i*den (x i).val=num (x i).val := by
    have u : IsUnit (mask (x i).val) := (mem_filter.mp (x i).property).2
    simp [mask] at u
    have d : IsUnit ((x i).val^2+3) := by tauto
    have hd : IsUnit (den (x i).val) := d.pow 6
    change (_*_)*_ = _
    rw [mul_assoc,ZMod.inv_mul_of_unit _ hd,mul_one]
  simp only [ComplementaryBatch.directedProduct,IsUnit.prod_univ_iff,not_forall] at hit
  obtain ⟨i,j,hit⟩ := hit
  have bad : ¬IsUnit (a i+a j-1) := by
    intro u
    apply hit
    change IsUnit (-(2*a i-1)-(2*a j-1))
    rw [show -(2*a i-1)-(2*a j-1)= -(2:ZMod n)*(a i+a j-1) by ring]
    exact two.neg.mul u
  rcases lt_trichotomy i j with lt|eq|gt
  · exact .inr (.inr ⟨i,j,lt,a i,a j,readAt i,readAt j,folded_covers (.inr bad)⟩)
  · subst j
    exact .inr (.inl ⟨i,a i,readAt i,by simpa [two_mul] using bad⟩)
  · exact .inr (.inr ⟨j,i,gt,a j,a i,readAt j,readAt i,folded_covers (.inr (by rwa [add_comm]))⟩)

private theorem zero_coord {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    {z : ZMod (p*q)} (h : ¬IsUnit z) :
    (ZMod.chineseRemainder cop z).1=0 ∨ (ZMod.chineseRemainder cop z).2=0 := by
  by_contra! hh
  have u : IsUnit (ZMod.chineseRemainder cop z) := Prod.isUnit_iff.mpr
    ⟨isUnit_iff_ne_zero.mpr hh.1,isUnit_iff_ne_zero.mpr hh.2⟩
  exact h (by simpa using u.map (ZMod.chineseRemainder cop).symm.toRingHom)

private theorem read_label {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] (big : 864<p)
    (f : R →+* ZMod p) {a x : R} (hx : f x∉bad p) (eq : a*den x=num x) : f a=value (f x) := by
  have ch : (108:ZMod p)≠0 := by
    exact_mod_cast (show ((108:ℕ):ZMod p)≠0 by
      rw [Ne,ZMod.natCast_zmod_eq_zero_iff_dvd]
      exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  apply (eq_div_iff ((regular_iff ch _).mp (mem_filter.mp (good hx).1).2).1).mpr
  simpa [num,den,sextic,map_ofNat] using congrArg f eq

theorem covers_search {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 864<p) (hq : 864<q) (w : Fin m → ZMod (p*q)) (h : SearchEvent w) :
    Opportunity (single p q) pair (fun i => ZMod.chineseRemainder cop (w i)) := by
  let e := ZMod.chineseRemainder cop
  let f := (RingHom.fst (ZMod p) (ZMod q)).comp e.toRingHom
  let g := (RingHom.snd (ZMod p) (ZMod q)).comp e.toRingHom
  by_cases ex : ∃ i, e (w i)∈single p q
  · exact Or.inl ex
  have safe (i) : f (w i)∉bad p ∧ g (w i)∉bad q := by
    have hh := not_exists.mp ex i
    simpa [single,f,g] using hh
  rcases h with ⟨i,hit⟩ | ⟨i,a,eq,hit⟩ | ⟨i,j,lt,a,b,ha,hb,hit⟩
  · rcases zero_coord cop hit with l|r
    · change f (mask (w i))=0 at l
      exact False.elim ((mem_filter.mp (good (safe i).1).1).2 (by simpa [mask,map_ofNat] using l))
    · change g (mask (w i))=0 at r
      exact False.elim ((mem_filter.mp (good (safe i).2).1).2 (by simpa [mask,map_ofNat] using r))
  · rcases zero_coord cop hit with l|r
    · change f (2*a-1)=0 at l
      simp only [map_sub,map_mul,map_ofNat,map_one,read_label hp f (safe i).1 eq] at l
      exact False.elim ((good (safe i).1).2 (by linear_combination l))
    · change g (2*a-1)=0 at r
      simp only [map_sub,map_mul,map_ofNat,map_one,read_label hq g (safe i).2 eq] at r
      exact False.elim ((good (safe i).2).2 (by linear_combination r))
  · refine Or.inr ⟨i,j,lt,?_⟩
    rcases zero_coord cop hit with l|r
    · change f (fold a-fold b)=0 at l
      rw [map_sub,sub_eq_zero] at l
      have eq : fold (value (f (w j)))=fold (value (f (w i))) := by
        simpa [fold,read_label hp f (safe i).1 ha,read_label hp f (safe j).1 hb] using l.symm
      apply mem_union_left
      apply mem_product.mpr
      refine ⟨?_,mem_univ _⟩
      change f (w i)∈row (f (w j))
      simpa [row,(safe j).1] using And.intro (good (safe i).1).1 eq
    · change g (fold a-fold b)=0 at r
      rw [map_sub,sub_eq_zero] at r
      have eq : fold (value (g (w j)))=fold (value (g (w i))) := by
        simpa [fold,read_label hq g (safe i).2 ha,read_label hq g (safe j).2 hb] using r.symm
      apply mem_union_right
      apply mem_product.mpr
      refine ⟨mem_univ _,?_⟩
      change g (w i)∈row (g (w j))
      simpa [row,(safe j).2] using And.intro (good (safe i).2).1 eq

noncomputable def words (n m : ℕ) [NeZero n] : Finset (Fin m → ZMod n) := by
  classical exact univ.filter SearchEvent

noncomputable def chance (n m : ℕ) [NeZero n] : ℝ := ((words n m).card:ℝ)/(n:ℝ)^m

/-- General bound preserving the local 12/24 split. -/
theorem chance_bound {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 864<p) (hq : 864<q) (m : ℕ) : chance (p*q) m ≤
      ((25*m + capacity p*m.choose 2:ℕ):ℝ)/p + ((25*m + capacity q*m.choose 2:ℕ):ℝ)/q := by
  classical
  let e := Equiv.arrowCongr (Equiv.refl (Fin m)) (ZMod.chineseRemainder cop).toEquiv
  have cover : (words (p*q) m).card ≤ (opportunityWords (single p q) pair m).card := by
    apply card_le_card_of_injOn e _ (fun _ _ _ _ eq => e.injective eq)
    intro w hw
    exact mem_filter.mpr ⟨mem_univ _,covers_search cop hp hq w (mem_filter.mp hw).2⟩
  have ex : (single p q).card ≤ 25*q+25*p := by
    apply (card_union_le _ _).trans
    simpa [mul_comm] using Nat.add_le_add (Nat.mul_le_mul_right q (bad_card hp))
      (Nat.mul_le_mul_right p (bad_card hq))
  have fiber (x : ZMod p × ZMod q) : (pair x).card ≤ capacity p*q+capacity q*p := by
    apply (card_union_le _ _).trans
    simpa [mul_comm] using Nat.add_le_add (Nat.mul_le_mul_right q (row_card hp x.1))
      (Nat.mul_le_mul_right p (row_card hq x.2))
  have h := word_bound (single p q) pair ex fiber m
  simp only [Fintype.card_prod,ZMod.card] at h
  have cnt := (Nat.mul_le_mul_right (p*q) cover).trans h
  have pc : 0<(p:ℝ) := by exact_mod_cast (show 0<p by omega)
  have qc : 0<(q:ℝ) := by exact_mod_cast (show 0<q by omega)
  have cast : ((words (p*q) m).card : ℝ)*((p:ℝ)*q) ≤
      ((m:ℝ)*(25*q+25*p)+(m.choose 2:ℝ)*(capacity p*q+capacity q*p))*((p:ℝ)*q)^m := by
    exact_mod_cast cnt
  unfold chance
  push_cast
  rw [div_le_iff₀ (by positivity)]
  apply (le_div_iff₀ (mul_pos pc qc)).mpr cast |>.trans_eq
  field_simp
  ring

private theorem trillion_bound {p q m C : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (budget : m≤10^12) (cap : capacity p+capacity q≤C) :
    chance (p*q) m ≤ ((50*(10^12)+C*(10^12).choose 2:ℕ):ℝ)/(2:ℝ)^1023 := by
  have hp := (by norm_num : 864<2^1023).trans_le pl
  have hq := (by norm_num : 864<2^1023).trans_le ql
  have a := div_le_div_of_nonneg_left (by positivity : (0:ℝ)≤((25*m+capacity p*m.choose 2:ℕ):ℝ))
    (by positivity : 0<(2:ℝ)^1023) (show (2:ℝ)^1023≤p by exact_mod_cast pl)
  have b := div_le_div_of_nonneg_left (by positivity : (0:ℝ)≤((25*m+capacity q*m.choose 2:ℕ):ℝ))
    (by positivity : 0<(2:ℝ)^1023) (show (2:ℝ)^1023≤q by exact_mod_cast ql)
  apply ((chance_bound cop hp hq m).trans (add_le_add a b)).trans
  rw [←add_div,←Nat.cast_add]
  apply div_le_div_of_nonneg_right (Nat.cast_le.mpr ?_) (by positivity)
  have hh := Nat.mul_le_mul cap (Nat.choose_le_choose 2 budget)
  nlinarith only [Nat.mul_le_mul_left 50 budget,hh]

/-- Any two distinct 1024-bit primes, including the case where both fields
admit complementary labels. -/
theorem trillion {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (budget : m≤10^12) :
    chance (p*q) m < 1/(2:ℝ)^938 := by
  have cap (r : ℕ) [Fact r.Prime] : capacity r≤24 := by unfold capacity; split_ifs <;> decide
  apply (trillion_bound (C:=48) cop pl ql budget (Nat.add_le_add (cap p) (cap q))).trans_lt
  rw [Nat.choose_two_right]
  norm_num

/-- At product residue five or seven, at most one local fiber doubles. -/
theorem trillion_mixed {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (budget : m≤10^12) (res : (p*q)%12=5 ∨ (p*q)%12=7) :
    chance (p*q) m < 1/(2:ℝ)^939 := by
  have cap : capacity p+capacity q≤36 := by
    rcases mixed ((by norm_num : 864<2^1023).trans_le pl) ((by norm_num : 864<2^1023).trans_le ql) res
      with ⟨h,k⟩|⟨h,k⟩ <;> simp [capacity,h,k]
  apply (trillion_bound cop pl ql budget cap).trans_lt
  rw [Nat.choose_two_right]
  norm_num

end PrimeFactors.ComplementaryPracticalBudget
