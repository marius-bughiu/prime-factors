import PrimeFactors.CircleMarkRationalTwoHoles

/-! The exact cells needed when appending the first new denominator to a
nearly complete rectangle. The prime is used to identify the shortfall. -/
namespace PrimeFactors.CircleMarkRationalFringe

open Finset CircleMarkRationalCover CircleMarkRationalTwoHoles
open private PrimeFactors.CircleMarkRationalTwoHoles.not_cast_zero from PrimeFactors.CircleMarkRationalTwoHoles

/-- Square target reached by numerator `i` in the next denominator column. -/
noncomputable def entry (p : ℕ) [Fact p.Prime] (D i : ℕ) : ZMod p :=
  ((i : ZMod p) / ((D+1 : ℕ) : ZMod p))^2

private theorem bounds {p H D s : ℕ} (sp : 0<s) (sd : s≤D)
    (area : p=(H+1)*(D+1)+s) : 2*H<p ∧ D+1<p := by
  have := Nat.mul_le_mul_left (H+1) (show 2≤D+1 by omega)
  have := Nat.mul_le_mul_right (D+1) (show 1≤H+1 by omega)
  omega

/-- In this column, all positive numerators through H reach different square targets. -/
private theorem entry_inj {p H D : ℕ} [Fact p.Prime] (room : 2*H<p) (short : D+1<p) :
    Set.InjOn (entry p D) (Icc 1 H : Finset ℕ) := by
  intro i im j jm eqn
  obtain ⟨ip,ih⟩ := mem_Icc.mp im
  obtain ⟨jp,jh⟩ := mem_Icc.mp jm
  have unit := PrimeFactors.CircleMarkRationalTwoHoles.not_cast_zero (by omega : 0<D+1) short
  change ((i : ZMod p) / _)^2=((j : ZMod p) / _)^2 at eqn
  rw [div_pow,div_pow,div_left_inj' (pow_ne_zero 2 unit)] at eqn
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp eqn with same|opp
  · have eq := congrArg ZMod.val same
    rwa [ZMod.val_natCast_of_lt (by omega : i<p),ZMod.val_natCast_of_lt (by omega : j<p)] at eq
  · have sum : ((i+j : ℕ):ZMod p)=0 := by push_cast; rw [opp,neg_add_cancel]
    exact False.elim ((Nat.not_dvd_of_pos_of_lt (by omega : 0 < i+j) (by omega : i+j < p))
      ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp sum))

private theorem divisor_range {s H : ℕ} (sp : 0<s) (sh : s≤H) : s.divisors ⊆ Icc 1 H := by
  intro i im
  have div := (Nat.mem_divisors.mp im).1
  exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos div sp,(Nat.le_of_dvd sp div).trans sh⟩

/-- At p=(H+1)(D+1)+s, the cell (u,D+1) catches the missing root
with denominator s/u. These are all the missing nonzero square targets. -/
theorem missing_eq {p H D s : ℕ} [Fact p.Prime] (sp : 0<s) (sh : s≤H) (sd : s≤D)
    (area : p=(H+1)*(D+1)+s) :
    missingSquares p H D=s.divisors.image (entry p D) := by
  classical
  obtain ⟨room,short⟩ := bounds sp sd area
  have unit := PrimeFactors.CircleMarkRationalTwoHoles.not_cast_zero (by omega : 0<D+1) short
  have rng := divisor_range sp sh
  symm
  apply eq_of_subset_of_card_le
  · intro a am
    obtain ⟨u,ud,rfl⟩ := mem_image.mp am
    obtain ⟨t,fac⟩ := (Nat.mem_divisors.mp ud).1
    obtain ⟨up,uh⟩ := mem_Icc.mp (rng ud)
    let r : ZMod p := (u:ZMod p)/((D+1:ℕ):ZMod p)
    have rn : r≠0 := div_ne_zero (PrimeFactors.CircleMarkRationalTwoHoles.not_cast_zero up (by omega : u<p)) unit
    have rel : ((H+1:ℕ):ZMod p)*((D+1:ℕ):ZMod p)+(u:ZMod p)*(t:ZMod p)=0 := by
      have z := congrArg (fun n : ℕ => (n:ZMod p)) (area.trans (congrArg ((H+1)*(D+1)+·) fac))
      simpa only [ZMod.natCast_self,Nat.cast_add,Nat.cast_mul] using z.symm
    have tr : (t:ZMod p)*r= -((H+1:ℕ):ZMod p) := by
      change _*(_/_) = _
      rw [←mul_div_assoc,div_eq_iff unit,neg_mul]
      linear_combination rel
    have dv : t∣s := ⟨u,fac.trans (Nat.mul_comm ..)⟩
    exact mem_image.mpr ⟨r,mem_filter.mpr ⟨mem_univ _,rn,miss_of_divisor sp sh sd area dv (Or.inr tr)⟩,rfl⟩
  · rw [(missing_counts sp sh sd area).2,card_image_of_injOn ((entry_inj room short).mono rng)]

/-- An arbitrary selection of entries in the first new column completes the
rectangle precisely when it includes every positive divisor of the shortfall. -/
theorem completes_iff {p H D s : ℕ} [Fact p.Prime] (sp : 0<s) (sh : s≤H) (sd : s≤D)
    (area : p=(H+1)*(D+1)+s) (S : Finset ℕ) (rangeS : S ⊆ Icc 1 H) :
    missingSquares p H D ⊆ S.image (entry p D) ↔ s.divisors ⊆ S := by
  rw [missing_eq sp sh sd area]
  obtain ⟨room,short⟩ := bounds sp sd area
  constructor
  · intro cover i im
    obtain ⟨j,jm,eq⟩ := mem_image.mp (cover (mem_image_of_mem (entry p D) im))
    have ji := entry_inj room short (rangeS jm) (divisor_range sp sh im) eq
    exact ji ▸ jm
  · exact image_subset_image

/-- A contiguous prefix of the next column can be chosen without factoring
s. Its exact necessary and sufficient length is s. -/
theorem prefix_iff {p H D s K : ℕ} [Fact p.Prime] (sp : 0<s) (sh : s≤H) (sd : s≤D)
    (area : p=(H+1)*(D+1)+s) (cap : K≤H) :
    missingSquares p H D ⊆ (Icc 1 K).image (entry p D) ↔ s≤K := by
  rw [completes_iff sp sh sd area _ (Icc_subset_Icc_right cap)]
  exact ⟨fun sub => (mem_Icc.mp (sub (Nat.mem_divisors.mpr ⟨dvd_rfl,sp.ne'⟩))).2,
    divisor_range sp⟩

/-- The union with the neighbouring rectangle tests this prefix and no
other new cells. The equivalence concerns all nonzero square roots. -/
theorem union_iff {p H D s K : ℕ} [Fact p.Prime] (sp : 0<s) (sh : s≤H) (sd : s≤D)
    (area : p=(H+1)*(D+1)+s) (cap : K≤H) :
    (∀ r : ZMod p, r≠0 → Represents r H D ∨ Represents r K (D+1)) ↔ s≤K := by
  classical
  rw [←prefix_iff sp sh sd area cap]
  obtain ⟨_,short⟩ := bounds sp sd area
  have unit := PrimeFactors.CircleMarkRationalTwoHoles.not_cast_zero (by omega : 0<D+1) short
  have col (i : ℕ) (r : ZMod p) : entry p D i=r^2 ↔
      (i:ZMod p)=((D+1:ℕ):ZMod p)*r ∨ (i:ZMod p)= -(((D+1:ℕ):ZMod p)*r) := by
    rw [entry,sq_eq_sq_iff_eq_or_eq_neg,div_eq_iff unit,div_eq_iff unit,neg_mul,mul_comm r]
  constructor
  · intro all a am
    obtain ⟨r,rm,rfl⟩ := mem_image.mp am
    obtain ⟨nz,miss⟩ := (mem_filter.mp rm).2
    obtain ⟨i,im,j,jm,hits⟩ := (all r nz).resolve_left miss
    obtain ⟨jp,jb⟩ := mem_Icc.mp jm
    have last : j=D+1 := by
      by_contra neq
      exact miss ⟨i,Icc_subset_Icc_right cap im,j,mem_Icc.mpr ⟨jp,by omega⟩,hits⟩
    subst j
    exact mem_image.mpr ⟨i,im,(col i r).mpr hits⟩
  · intro covers r nz
    by_cases hit : Represents r H D
    · exact Or.inl hit
    have miss : r^2∈missingSquares p H D :=
      mem_image.mpr ⟨r,mem_filter.mpr ⟨mem_univ _,nz,hit⟩,rfl⟩
    obtain ⟨i,im,eq⟩ := mem_image.mp (covers miss)
    exact Or.inr ⟨i,im,D+1,mem_Icc.mpr ⟨by omega,le_rfl⟩,(col i r).mp eq⟩

/-- Offsets that could put a prime in a public shortfall window. -/
noncomputable def offsets (C L : ℕ) : Finset ℕ := (Icc 1 L).filter (fun s => (C+s).Prime)

/-- All numerator positions required by at least one of those possible primes. -/
noncomputable def required (C L : ℕ) : Finset ℕ := (offsets C L).biUnion Nat.divisors

/-- Complete coverage of every omitted square at a prime in the window. -/
def coversAt (p H D : ℕ) (S : Finset ℕ) : Prop := ∀ [Fact p.Prime],
  missingSquares p H D ⊆ S.image (entry p D)

theorem window_iff {H D L : ℕ} (lh : L≤H) (ld : L≤D) (S : Finset ℕ) (rangeS : S ⊆ Icc 1 H) :
    (∀ s∈Icc 1 L, coversAt ((H+1)*(D+1)+s) H D S) ↔ required ((H+1)*(D+1)) L ⊆ S := by
  constructor
  · intro covers u um
    obtain ⟨s,sm,ud⟩ := mem_biUnion.mp um
    obtain ⟨interval,pp⟩ := mem_filter.mp sm
    letI : Fact ((H+1)*(D+1)+s).Prime := ⟨pp⟩
    obtain ⟨pos,cap⟩ := mem_Icc.mp interval
    exact (completes_iff pos (cap.trans lh) (cap.trans ld) rfl S rangeS).mp (covers s interval) ud
  · intro sub s interval pp
    obtain ⟨pos,cap⟩ := mem_Icc.mp interval
    apply (completes_iff pos (cap.trans lh) (cap.trans ld) rfl S rangeS).mpr
    exact fun _ ud => sub (mem_biUnion.mpr ⟨s,mem_filter.mpr ⟨interval,pp.out⟩,ud⟩)

/-- Each prime candidate requires its own offset as a numerator, so even the
smallest universal correction uses at least as many cells as there are
candidate primes available for direct trial division in the same window. -/
theorem cost (C L : ℕ) : (offsets C L).card≤(required C L).card := by
  apply card_le_card
  intro s sm
  have sp : 0<s := (mem_Icc.mp (mem_filter.mp sm).1).1
  exact mem_biUnion.mpr ⟨s,sm,Nat.mem_divisors.mpr ⟨dvd_rfl,sp.ne'⟩⟩

/-- Four entries, shared by all possible primes 101, 103, 107 and 109. -/
theorem hundred : offsets 100 9={1,3,7,9} ∧ required 100 9={1,3,7,9} := by decide

end PrimeFactors.CircleMarkRationalFringe
