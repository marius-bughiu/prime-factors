import PrimeFactors.CircleMarkChangedPrimeSum
import PrimeFactors.CircleMarkSingletonChanges

/-! Prime extraction from individual square-prefix differences and their
product. A mixed CRT intersection is distinct from a public square even
though both give the full modulus in a single batch gcd. -/

namespace PrimeFactors.CircleMarkPrefixExtraction

open Finset CircleMarkTargetFrequency CircleMarkSharedScores CircleMarkSharedOccurrence
  CircleMarkChangedPrimeSum
open scoped Classical
open private PrimeFactors.CircleMarkSingletonChanges.count_rectangle from PrimeFactors.CircleMarkSingletonChanges

/-- Public roots, including the CRT diagonal when r is the input modulus. -/
noncomputable def roots (r d : ℕ) : Finset (ZMod r) :=
  (Icc 1 d).image fun i : ℕ => (i : ZMod r)^2

def term {n : ℕ} (t : ZMod n) (i : ℕ) : ℕ := ((t.val:ℤ)-(i:ℤ)^2).natAbs

def leaf {n : ℕ} (t : ZMod n) (i : ℕ) : ℕ := (term t i).gcd n

noncomputable def batch {n : ℕ} (t : ZMod n) (d : ℕ) : ℕ := (∏ i ∈ Icc 1 d, term t i).gcd n

/-- One gcd gives the prime whose divisibility test alone holds, the full
modulus if both hold, or one if neither holds. -/
private theorem gcd_cases {p q z : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (diff : p ≠ q) :
    z.gcd (p*q) = if p∣z then (if q∣z then p*q else p) else (if q∣z then q else 1) := by
  have cop := (Nat.coprime_primes hp.out hq.out).mpr diff
  split_ifs with P Q Q
  · exact Nat.gcd_eq_right_iff_dvd.mpr (cop.mul_dvd_of_dvd_of_dvd P Q)
  · exact NormBatchGCD.one_batch hq.out P Q
  · rw [Nat.mul_comm p q]
    exact NormBatchGCD.one_batch hp.out Q P
  · exact ((hp.out.coprime_iff_not_dvd.mpr P).symm.mul_right (hq.out.coprime_iff_not_dvd.mpr Q).symm).gcd_eq_one

private theorem dvd_term {n r i : ℕ} (t : ZMod n) :
    r ∣ term t i ↔ (t.val : ZMod r) = (i : ZMod r)^2 := by
  rw [term, ←Int.natCast_dvd, ←ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub,Int.cast_pow,Int.cast_natCast,sub_eq_zero]

theorem leaf_eq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p ≠ q) (t : ZMod (p*q)) (i : ℕ) :
    leaf t i = if (t.val : ZMod p) = (i:ZMod p)^2 then
      (if (t.val : ZMod q) = (i:ZMod q)^2 then p*q else p)
      else (if (t.val : ZMod q) = (i:ZMod q)^2 then q else 1) := by
  simp only [leaf,gcd_cases diff,dvd_term]

private theorem dvd_batch {n r : ℕ} [hr : Fact r.Prime] (t : ZMod n) (d : ℕ) :
    r∣∏ i ∈ Icc 1 d, term t i ↔ (t.val : ZMod r) ∈ roots r d := by
  simp only [hr.out.prime.dvd_finset_prod_iff,dvd_term,roots,mem_image]
  exact exists_congr fun i => and_congr_right fun _ => eq_comm

theorem batch_eq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p ≠ q) (t : ZMod (p*q)) (d : ℕ) :
    batch t d = if (t.val : ZMod p) ∈ roots p d then
      (if (t.val : ZMod q) ∈ roots q d then p*q else p)
      else (if (t.val : ZMod q) ∈ roots q d then q else 1) := by
  simp only [batch,gcd_cases diff,dvd_batch]

private theorem root_card {r d : ℕ} [Fact r.Prime] (op : r≠2) (cap : d≤(r-1)/2) :
    (roots r d).card=d := by
  have bound : ((roots r d).erase 0).card ≤ (roots r d).card := card_erase_le
  change (covered r (Icc 1 d)).card ≤ (roots r d).card at bound
  rw [prefix_cover op,min_eq_left cap] at bound
  exact le_antisymm (card_image_le.trans_eq (by simp : (Icc 1 d).card=d)) bound

private theorem covered_eq {r d : ℕ} [Fact r.Prime] (op : r≠2) (cap : d≤(r-1)/2) :
    covered r (Icc 1 d)=roots r d := by
  apply eq_of_subset_of_card_le (erase_subset ..)
  change (roots r d).card ≤ (covered r (Icc 1 d)).card
  rw [prefix_cover op,min_eq_left cap,root_card op cap]

private theorem inj {r d : ℕ} [Fact r.Prime] (op : r≠2) (cap : d≤(r-1)/2) :
    Set.InjOn (fun i : ℕ => (i:ZMod r)^2) (Icc 1 d : Finset ℕ) :=
  injOn_of_card_image_eq ((root_card op cap).trans (by simp))

private theorem nonzero {r d : ℕ} [Fact r.Prime] (op : r≠2) (cap : d≤(r-1)/2) :
    (0 : ZMod r) ∉ roots r d := by rw [←covered_eq op cap]; exact not_mem_erase 0 _

private theorem same_index {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (diff : p≠q)
    (t : ZMod (p*q)) (i : ℕ) :
    ((t.val : ZMod p)=(i:ZMod p)^2 ∧ (t.val : ZMod q)=(i:ZMod q)^2) ↔ t=(i:ZMod (p*q))^2 := by
  let e := ZMod.chineseRemainder ((Nat.coprime_primes hp.out hq.out).mpr diff)
  have co : e t = (t.val : ℕ) := by rw [←map_natCast e,ZMod.natCast_zmod_val]
  rw [←e.injective.eq_iff,co,map_pow,map_natCast]
  exact ⟨fun h => Prod.ext h.1 h.2,fun h => ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩⟩

private theorem diag_card {p q d : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q)
    (op : p≠2) (cap : d≤(p-1)/2) : (roots (p*q) d).card=d := by
  rw [roots,card_image_of_injOn]
  · simp
  · intro i im j jm eqn
    have h := (same_index diff ((i:ZMod (p*q))^2) j).mpr eqn
    have g := (same_index diff ((i:ZMod (p*q))^2) i).mpr rfl
    exact inj op cap im jm (g.1.symm.trans h.1)

/-- On a unit, an unsigned score change is exactly a hit at either prime. -/
theorem change_iff {p q d : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (cap : d≤(p-1)/2) (t : ZMod (p*q)) :
    t ∈ changed (p*q) {Icc 1 d} ↔ (t.val : ZMod p) ≠ 0 ∧ (t.val : ZMod q) ≠ 0 ∧
      ((t.val : ZMod p)∈roots p d ∨ (t.val : ZMod q)∈roots q d) := by
  have capq : d≤(q-1)/2 := by omega
  rw [changed_iff]
  simp only [singleton_biUnion,id_eq,score_eq_of_covered,covered_eq op cap,covered_eq oq capq]
  by_cases hits : (t.val : ZMod p) ∈ roots p d ∨ (t.val : ZMod q) ∈ roots q d
  · rw [if_pos hits,ExtensionTrace.jacobi_crt,ne_comm]
    simp only [Int.cast_natCast,ne_eq,mul_eq_zero,quadraticChar_eq_zero_iff,not_or,hits,and_true]
  · simp only [hits,if_false,and_false,ne_self_iff_false]

/-- A mixed intersection splits in both directions by inspecting individual
coordinates. The product gcd equals N on this same residue. -/
theorem mixed {p q d : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (t : ZMod (p*q))
    (P : (t.val : ZMod p)∈roots p d) (Q : (t.val : ZMod q)∈roots q d)
    (off : t∉roots (p*q) d) : batch t d=p*q ∧
    ∃ i∈Icc 1 d, ∃ j∈Icc 1 d, i≠j ∧ leaf t i=p ∧ leaf t j=q := by
  refine ⟨by rw [batch_eq diff,if_pos P,if_pos Q],?_⟩
  obtain ⟨i,im,ih⟩ := mem_image.mp P
  obtain ⟨j,jm,jh⟩ := mem_image.mp Q
  have qi : (t.val:ZMod q)≠(i:ZMod q)^2 :=
    fun h => off (mem_image.mpr ⟨i,im,((same_index diff t i).mp ⟨ih.symm,h⟩).symm⟩)
  have pj : (t.val:ZMod p)≠(j:ZMod p)^2 :=
    fun h => off (mem_image.mpr ⟨j,jm,((same_index diff t j).mp ⟨h,jh.symm⟩).symm⟩)
  exact ⟨i,im,j,jm,fun e => qi (e ▸ jh.symm),by rw [leaf_eq diff,if_pos ih.symm,if_neg qi],
    by rw [leaf_eq diff,if_neg pj,if_pos jh.symm]⟩

private noncomputable def side (r d : ℕ) [NeZero r] (hit unitsOnly : Bool) : Finset (ZMod r) :=
  if hit then roots r d else if unitsOnly then (univ.erase 0) \ roots r d else (roots r d)ᶜ

/-- Residues with the specified local root membership on the two CRT sides.
The final parameter selects all residues or only units. -/
noncomputable def region (p q d : ℕ) [NeZero p] [NeZero q] (hitP hitQ unitsOnly : Bool) : Finset (ZMod (p*q)) :=
  univ.filter fun t => (t.val : ZMod p) ∈ side p d hitP unitsOnly ∧
    (t.val : ZMod q) ∈ side q d hitQ unitsOnly

private theorem side_mem {r d : ℕ} [Fact r.Prime] (op : r≠2) (cap : d≤(r-1)/2)
    (x : ZMod r) (hit unitsOnly : Bool) :
    x∈side r d hit unitsOnly ↔ (x∈roots r d ↔ hit=true) ∧ (unitsOnly=true → x≠0) := by
  have nz : x∈roots r d → x≠0 := fun hx eqn => nonzero op cap (eqn ▸ hx)
  cases hit <;> cases unitsOnly <;> simp [side, and_comm]
  exact nz

theorem mem_region {p q d : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (cap : d≤(p-1)/2)
    (a b unitsOnly : Bool) (t : ZMod (p*q)) :
    t∈region p q d a b unitsOnly ↔
      ((t.val:ZMod p)∈roots p d ↔ a=true) ∧ ((t.val:ZMod q)∈roots q d ↔ b=true) ∧
      (unitsOnly=true → (t.val:ZMod p)≠0 ∧ (t.val:ZMod q)≠0) := by
  have capq : d≤(q-1)/2 := by omega
  simp only [region,mem_filter,mem_univ,true_and,side_mem op cap,side_mem oq capq]
  tauto

private theorem side_card {r d : ℕ} [Fact r.Prime] (op : r≠2) (cap : d≤(r-1)/2)
    (hit unitsOnly : Bool) : (side r d hit unitsOnly).card =
      if hit then d else if unitsOnly then r-1-d else r-d := by
  have sub : roots r d ⊆ univ.erase 0 := fun x hx =>
    mem_erase.mpr ⟨fun eqn => nonzero op cap (eqn ▸ hx),mem_univ x⟩
  cases hit <;> cases unitsOnly <;>
    simp [side,root_card op cap,card_compl,card_sdiff sub,card_erase_of_mem]

/-- This gives all four counts. For example, the first-prime-only rectangle
has d(q−d) residues and d(q−1−d) units. The double-hit rectangle has d² in
both populations. -/
theorem region_card {p q d : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (cap : d≤(p-1)/2) (a b unitsOnly : Bool) :
    (region p q d a b unitsOnly).card =
      (if a then d else if unitsOnly then p-1-d else p-d) *
      (if b then d else if unitsOnly then q-1-d else q-d) := by
  have box := PrimeFactors.CircleMarkSingletonChanges.count_rectangle order.ne
    (region p q d a b unitsOnly) (side p d a unitsOnly) (side q d b unitsOnly)
    (fun t => by simp only [region,mem_filter,mem_univ,true_and])
  rw [box,side_card op cap,side_card oq (by omega)]

theorem region_batch {p q d : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (cap : d≤(p-1)/2) {a b unitsOnly : Bool}
    {t : ZMod (p*q)} (ht : t∈region p q d a b unitsOnly) :
    batch t d = if a then (if b then p*q else p) else (if b then q else 1) := by
  obtain ⟨P,Q,_⟩ := (mem_region order op oq cap a b unitsOnly t).mp ht
  simp only [batch_eq order.ne,P,Q]

/-- At a public square one individual coordinate gives N and all others
give one. The witness index is unique in this prefix. -/
theorem diagonal {p q d : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q)
    (op : p≠2) (oq : q≠2) (cap : d≤(p-1)/2) {t : ZMod (p*q)} (ht : t∈roots (p*q) d) :
    ∃ i∈Icc 1 d, t=(i:ZMod (p*q))^2 ∧
      ∀ j∈Icc 1 d, leaf t j = if i=j then p*q else 1 := by
  obtain ⟨i,im,eqn⟩ := mem_image.mp ht
  obtain ⟨P,Q⟩ := (same_index order.ne t i).mpr eqn.symm
  refine ⟨i,im,eqn.symm,?_⟩
  intro j jm
  by_cases eq : i=j
  · subst j
    rw [if_pos rfl,leaf_eq order.ne,if_pos P,if_pos Q]
  · have capq : d≤(q-1)/2 := by omega
    have atP : (t.val:ZMod p)≠(j:ZMod p)^2 := fun h => eq (inj op cap im jm (P.symm.trans h))
    have atQ : (t.val:ZMod q)≠(j:ZMod q)^2 := fun h => eq (inj oq capq im jm (Q.symm.trans h))
    rw [if_neg eq,leaf_eq order.ne,if_neg atP,if_neg atQ]

private theorem diag_sub {p q d : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q)
    (op : p≠2) (oq : q≠2) (cap : d≤(p-1)/2) {t : ZMod (p*q)} (ht : t∈roots (p*q) d) :
    t∈changed (p*q) {Icc 1 d} ∧ t∈region p q d true true true := by
  obtain ⟨i,im,eqn⟩ := mem_image.mp ht
  obtain ⟨P,Q⟩ := (same_index order.ne t i).mpr eqn.symm
  have rp : (t.val:ZMod p)∈roots p d := mem_image.mpr ⟨i,im,P.symm⟩
  have rq : (t.val:ZMod q)∈roots q d := mem_image.mpr ⟨i,im,Q.symm⟩
  have np : (t.val:ZMod p)≠0 := fun e => nonzero op cap (e ▸ rp)
  have nq : (t.val:ZMod q)≠0 := fun e => nonzero oq (by omega : d≤(q-1)/2) (e ▸ rq)
  exact ⟨(change_iff order op oq cap t).mpr ⟨np,nq,Or.inl rp⟩,
    (mem_region order op oq cap ..).mpr ⟨⟨fun _ => rfl,fun _ => rp⟩,⟨fun _ => rfl,fun _ => rq⟩,fun _ => ⟨np,nq⟩⟩⟩

/-- Among changed score samples a proper individual gcd exists exactly off
the public diagonal. -/
theorem proper_iff {p q d : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (order : p<q)
    (op : p≠2) (oq : q≠2) (cap : d≤(p-1)/2) {t : ZMod (p*q)}
    (ht : t∈changed (p*q) {Icc 1 d}) :
    (∃ i∈Icc 1 d, leaf t i=p ∨ leaf t i=q) ↔ t∉roots (p*q) d := by
  constructor
  · rintro ⟨i,im,found⟩ diag
    obtain ⟨j,_,_,result⟩ := diagonal order op oq cap diag
    rw [result i im] at found
    have lp := lt_mul_of_one_lt_right hp.out.pos hq.out.one_lt
    have lq := lt_mul_of_one_lt_left hq.out.pos hp.out.one_lt
    have pp := hp.out.one_lt
    have qp := hq.out.one_lt
    split_ifs at found <;> omega
  · intro off
    rcases ((change_iff order op oq cap t).mp ht).2.2 with P|Q
    · obtain ⟨i,im,e⟩ := mem_image.mp P
      have noQ : (t.val:ZMod q)≠(i:ZMod q)^2 := fun h =>
        off (mem_image.mpr ⟨i,im,((same_index order.ne t i).mp ⟨e.symm,h⟩).symm⟩)
      exact ⟨i,im,Or.inl (by rw [leaf_eq order.ne,if_pos e.symm,if_neg noQ])⟩
    · obtain ⟨i,im,e⟩ := mem_image.mp Q
      have noP : (t.val:ZMod p)≠(i:ZMod p)^2 := fun h =>
        off (mem_image.mpr ⟨i,im,((same_index order.ne t i).mp ⟨h,e.symm⟩).symm⟩)
      exact ⟨i,im,Or.inr (by rw [leaf_eq order.ne,if_neg noP,if_pos e.symm])⟩

/-- The only d lost samples among the H_d changed residues are the d public
squares. Among the d² double hits, d(d−1) are mixed intersections. -/
theorem proper_counts {p q d : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q)
    (op : p≠2) (oq : q≠2) (cap : d≤(p-1)/2) :
    ((changed (p*q) {Icc 1 d}).filter (fun t => ∃ i∈Icc 1 d, leaf t i=p ∨ leaf t i=q)).card =
      tally (p*q) d-d ∧
    (roots (p*q) d).card=d ∧ ((region p q d true true true) \ roots (p*q) d).card=d*(d-1) := by
  have diag := diag_card order.ne op cap
  have eqn : (changed (p*q) {Icc 1 d}).filter (fun t => ∃ i∈Icc 1 d, leaf t i=p ∨ leaf t i=q) =
      changed (p*q) {Icc 1 d} \ roots (p*q) d := by
    ext t
    simp only [mem_filter,mem_sdiff]
    exact and_congr_right fun ht => proper_iff order op oq cap ht
  rw [eqn,card_sdiff (fun _ ht => (diag_sub order op oq cap ht).1),
    card_sdiff (fun _ ht => (diag_sub order op oq cap ht).2),diag,
    region_card order op oq cap]
  simp [tally,Nat.mul_sub]

/-- A full coordinate scan across a fixed set of rows contains exactly d
differences per row. The batch multiplies these terms for one gcd per row. -/
theorem scalar_work {n : ℕ} (rows : Finset (ZMod n)) (d : ℕ) :
    (rows ×ˢ Icc 1 d).card=rows.card*d := by simp

/-- Concrete counts among all residues, among unit residues, and among
changed residues where an individual term supplies a proper gcd. -/
theorem example_2183 :
    (region 37 59 16 true false false).card=688 ∧
    (region 37 59 16 false true false).card=336 ∧
    (region 37 59 16 true false true).card=672 ∧
    (region 37 59 16 false true true).card=320 ∧
    (region 37 59 16 false false true).card=840 ∧
    (roots 2183 16).card=16 ∧
    ((region 37 59 16 true true true) \ roots 2183 16).card=240 ∧
    ((changed 2183 {Icc 1 16}).filter (fun t => ∃ i∈Icc 1 16, leaf t i=37 ∨ leaf t i=59)).card=1232 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 59) := ⟨by decide⟩
  have regionSize := region_card (p:=37) (q:=59) (d:=16) (by decide) (by decide) (by decide) (by decide)
  have separate := proper_counts (p:=37) (q:=59) (d:=16) (by decide) (by decide) (by decide) (by decide)
  rw [tally_eq (p:=37) (q:=59) (d:=16) (by decide) (by decide) (by decide) (by decide)] at separate
  norm_num only [Nat.reduceMul,Nat.reduceSub,Nat.reduceAdd] at separate
  exact ⟨regionSize true false false,regionSize false true false,regionSize true false true,
    regionSize false true true,regionSize false false true,separate.2.1,separate.2.2,separate.1⟩

end PrimeFactors.CircleMarkPrefixExtraction
