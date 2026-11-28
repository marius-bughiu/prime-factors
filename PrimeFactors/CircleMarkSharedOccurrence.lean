import PrimeFactors.CircleMarkSharedScores
import PrimeFactors.CircleMarkMaskDigitReadout

/-! When several masks share one draw, any change from the ordinary Jacobi
symbol occurs on the union of the tested coordinates. Counting that event
once avoids multiplying the work bound by the number of digit questions. -/
namespace PrimeFactors.CircleMarkSharedOccurrence

open Finset CircleMarkSharedScores CircleMarkTargetFrequency CircleMarkMaskDigitReadout
open CircleMarkDigitCoordinates
open scoped Classical

noncomputable def changed (n : ℕ) [NeZero n] (family : Finset (Finset ℕ)) : Finset (ZMod n) :=
  univ.filter fun t => ∃ C∈family, score n C t ≠ jacobiSym t.val n

private theorem cover_union (r : ℕ) (F : Finset (Finset ℕ)) (z : ZMod r) :
    z∈covered r (F.biUnion id) ↔ ∃ C∈F, z∈covered r C := by
  constructor
  · intro h
    obtain ⟨nz,im⟩ := mem_erase.mp h
    obtain ⟨x,hx,e⟩ := mem_image.mp im
    obtain ⟨C,cf,xc⟩ := mem_biUnion.mp hx
    exact ⟨C,cf,mem_erase.mpr ⟨nz, mem_image.mpr ⟨x,xc,e⟩⟩⟩
  · rintro ⟨C,cf,h⟩
    obtain ⟨nz,im⟩ := mem_erase.mp h
    obtain ⟨x,hx,e⟩ := mem_image.mp im
    exact mem_erase.mpr ⟨nz,mem_image.mpr ⟨x,mem_biUnion.mpr ⟨C,cf,hx⟩,e⟩⟩

theorem changed_iff {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (F : Finset (Finset ℕ)) (t : ZMod (p*q)) :
    t∈changed (p*q) F ↔ score (p*q) (F.biUnion id) t ≠ jacobiSym t.val (p*q) := by
  have single (C : Finset ℕ) : score (p*q) C t≠jacobiSym t.val (p*q) ↔
      jacobiSym t.val (p*q)≠0 ∧ ((t.val:ZMod p)∈covered p C ∨ (t.val:ZMod q)∈covered q C) := by
    rw [score_eq_of_covered]
    split_ifs <;> simp_all [ne_comm]
  simp only [changed,mem_filter,mem_univ,true_and,single,cover_union]
  constructor
  · rintro ⟨C,cf,nz,cp|cq⟩
    · exact ⟨nz,Or.inl ⟨C,cf,cp⟩⟩
    · exact ⟨nz,Or.inr ⟨C,cf,cq⟩⟩
  · rintro ⟨nz,⟨C,cf,cp⟩|⟨C,cf,cq⟩⟩
    · exact ⟨C,cf,nz,Or.inl cp⟩
    · exact ⟨C,cf,nz,Or.inr cq⟩

/-- Number of distinct shared samples on which any question changes the sign to zero. -/
theorem count {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (F : Finset (Finset ℕ)) :
    (changed (p*q) F).card + live p q (F.biUnion id) = (p-1)*(q-1) := by
  let U := F.biUnion id
  have plain (t : ZMod (p*q)) : score (p*q) ∅ t=jacobiSym t.val (p*q) := by
    simp [score_eq_of_covered,covered]
  have term (t : ZMod (p*q)) :
      (if t∈changed (p*q) F then (1:ℤ) else 0) =
      score (p*q) ∅ t * score (p*q) ∅ t - score (p*q) U t * score (p*q) U t := by
    simp only [changed_iff]
    change (if score (p*q) U t ≠ jacobiSym t.val (p*q) then (1:ℤ) else 0)=_
    rw [plain,score_eq]
    split_ifs <;> rcases jacobiSym.trichotomy t.val (p*q) with h|h|h <;> simp_all
  have e := Finset.sum_congr (s₁:=univ) rfl (fun t _ => term t)
  simp only [sum_boole,filter_mem_eq_inter,univ_inter,sum_sub_distrib,sum_product diff,
    union_self] at e
  have emptyLive : live p q ∅=(p-1)*(q-1) := by simp [live,covered]
  rw [emptyLive] at e
  change (changed (p*q) F).card + live p q U=_
  omega

private theorem cover_bounds (r : ℕ) [Fact r.Prime] (C : Finset ℕ) :
    (covered r C).card≤C.card ∧ (covered r C).card≤r-1 := by
  have sub : covered r C⊆univ.erase 0 := fun x hx => mem_erase.mpr ⟨(mem_erase.mp hx).1,mem_univ _⟩
  exact ⟨card_erase_le.trans card_image_le, (card_le_card sub).trans_eq (by simp)⟩

/-- Each local root accounts for at most the full opposite-prime fiber. -/
theorem upper {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (F : Finset (Finset ℕ)) :
    (changed (p*q) F).card ≤ (p+q)*(F.biUnion id).card := by
  let U := F.biUnion id
  let a := (covered p U).card
  let b := (covered q U).card
  obtain ⟨ac,ap⟩ := cover_bounds p U
  obtain ⟨bc,bq⟩ := cover_bounds q U
  have e := count diff F
  change (changed (p*q) F).card + (p-1-a)*(q-1-b)=(p-1)*(q-1) at e
  have A : p-1-a+a=p-1 := Nat.sub_add_cancel ap
  have B : q-1-b+b=q-1 := Nat.sub_add_cancel bq
  have algebra (P Q a b x y : ℕ) (ax : x+a=P) (by' : y+b=Q) :
      x*y+P*b+Q*a=P*Q+a*b := by subst P; subst Q; ring
  have expand := algebra _ _ _ _ _ _ A B
  have bound : (changed (p*q) F).card ≤ (p-1)*b+(q-1)*a := by omega
  exact bound.trans ((Nat.add_le_add (Nat.mul_le_mul (Nat.sub_le ..) bc)
    (Nat.mul_le_mul (Nat.sub_le ..) ac)).trans_eq (Nat.add_mul ..).symm)

noncomputable abbrev allCoords (n : ℕ) := coordinates n (range (base n)) (range (base n))

theorem menu_subset (n : ℕ) {J I : Finset ℕ} (bj : J⊆range (base n)) (bi : I⊆range (base n)) :
    coordinates n J I ⊆ allCoords n :=
  union_subset_union (image_subset_image (filter_subset_filter _ bj))
    (image_subset_image (filter_subset_filter _ bi))

set_option exponentiation.threshold 8192 in
/-- One shared uniform residue changes any mask in this public family with
probability strictly below 2^(-509), regardless of the number of questions. -/
theorem full_width {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (lo : 2^1023≤p)
    (order : p<q) (hi : q<2^1024) (F : Finset (Finset ℕ))
    (family : ∀ C∈F, C⊆allCoords (p*q)) :
    (changed (p*q) F).card * 2^509 < p*q := by
  have sub : F.biUnion id ⊆ allCoords (p*q) := fun x hx => by
    obtain ⟨C,cf,xc⟩ := mem_biUnion.mp hx
    exact family C cf xc
  have cap := (card_le_card sub).trans (size _ Subset.rfl Subset.rfl)
  have width := full_dimensions order hi
  have degree : (F.biUnion id).card≤2^513 :=
    cap.trans ((Nat.mul_le_mul_left 2 width).trans_eq (by decide +kernel))
  have pq := (upper order.ne F).trans (Nat.mul_le_mul_left _ degree)
  have scale : (2:ℕ)^513*2^509=2^1022 := by decide +kernel
  have twice : (2:ℕ)^1022*2=2^1023 := by decide +kernel
  calc _ ≤ ((p+q)*2^513)*2^509 := Nat.mul_le_mul_right _ pq
       _ = (p+q)*2^1022 := by rw [Nat.mul_assoc,scale]
       _ < (2*q)*2^1022 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
       _ = (2^1022*2)*q := by ring
       _ ≤ p*q := Nat.mul_le_mul_right _ (twice ▸ lo)

/-- Exact count of sequences of independent uniform residues with any changed sample. -/
theorem sequence_count (n : ℕ) [NeZero n] (E : Finset (ZMod n)) (k : ℕ) :
    (univ.filter fun f : Fin k → ZMod n => ∃i, f i∈E).card = n^k-(n-E.card)^k := by
  have eqn : (univ.filter fun f : Fin k → ZMod n => ∃i, f i∈E) =
      (Fintype.piFinset fun _ : Fin k => Eᶜ)ᶜ := by
    ext f
    simp
  rw [eqn,card_compl,Fintype.card_piFinset]
  simp [card_compl,Fintype.card_fun]

/-- Bernoulli's inequality for the event of seeing at least one changed residue. -/
private theorem repeats_bound (x : ℚ) (lo : 0≤x) (hi : x≤1) (k : ℕ) :
    1-(1-x)^k≤k*x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have cap : (1-x)^k≤1 := pow_le_one₀ (by linarith) (by linarith)
    have h := mul_le_mul_of_nonneg_right cap lo
    push_cast
    rw [pow_succ]
    nlinarith only [ih,h]

set_option exponentiation.threshold 8192 in
/-- More than 2^508 independent shared draws are needed for a half chance
of seeing a single change across the entire family. -/
theorem half_chance {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (lo : 2^1023≤p)
    (order : p<q) (hi : q<2^1024) (F : Finset (Finset ℕ))
    (family : ∀ C∈F, C⊆allCoords (p*q)) (k : ℕ) :
    let x : ℚ := ((changed (p*q) F).card:ℚ)/(p*q:ℕ)
    1/2≤1-(1-x)^k → 2^508<k := by
  let x : ℚ := ((changed (p*q) F).card:ℚ)/(p*q:ℕ)
  change 1/2≤1-(1-x)^k → _
  intro hit
  have den : (0:ℚ)<(p*q:ℕ) := by exact_mod_cast Nat.mul_pos hp.out.pos hq.out.pos
  have exactRate := full_width lo order hi F family
  have cross : ((changed (p*q) F).card:ℚ)*2^509<(p*q:ℕ) := by exact_mod_cast exactRate
  have scale : x*2^509<1 := by dsimp [x]; rw [div_mul_eq_mul_div,div_lt_one den]; exact cross
  have nz : 0≤x := by dsimp [x]; positivity
  have top : x≤1 := (le_mul_of_one_le_right nz (by norm_num : (1:ℚ)≤2^509)).trans scale.le
  have avg := hit.trans (repeats_bound x nz top k)
  apply lt_of_not_ge
  intro small
  have ncap : (k:ℚ)≤2^508 := by exact_mod_cast small
  have h := avg.trans (mul_le_mul_of_nonneg_right ncap nz)
  have twice : (2:ℚ)^509=2*(2^508) := by norm_num
  rw [twice] at scale
  linarith

end PrimeFactors.CircleMarkSharedOccurrence
