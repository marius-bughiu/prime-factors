import PrimeFactors.QuarticLocalSumBits

/-! The sign selected by the quartic local tests keeps exactly half the
distinct admissible modular sum labels in a complete period. -/
namespace PrimeFactors.QuarticHalfSumResidues

open Finset
open QuarticLocalSumBits (Signed)
open scoped Classical

variable {m : ℕ} [NeZero m]

noncomputable def sums (m : ℕ) [NeZero m] (N : ℤ) : Finset (ZMod m) :=
  univ.filter (AdmissibleSum (N : ZMod m))

noncomputable def selected (div : 16∣m) (N : ℤ) (yes : Bool) : Finset (ZMod m) :=
  (sums m N).filter fun s => ZMod.castHom div (ZMod 16) s =
    (((if yes then N+1 else -(N+1)) : ℤ) : ZMod 16)

private theorem mem_sums {N : ℤ} {s : ZMod m} : s∈sums m N ↔ AdmissibleSum (N : ZMod m) s := by
  simp only [sums,mem_filter,mem_univ,true_and]

/-- Membership for an integer representative is precisely the signed factor
pair condition, allowing any odd factors of the modulus. -/
theorem mem_selected (div : 16∣m) {N s : ℤ} (gate : N%16=1 ∨ N%16=5) (yes : Bool) :
    (s:ZMod m)∈selected div N yes ↔ Signed (if yes then 1 else 3) m N s := by
  have modulus : (16:ℤ)∣m := by exact_mod_cast div
  obtain ⟨positive,negative⟩ := QuarticLocalSumBits.signed_support (s:=s) modulus gate
  cases yes
  · simpa only [selected,mem_filter,mem_sums,map_intCast,Bool.false_eq_true,if_false,
      ZMod.intCast_eq_intCast_iff'] using negative.symm
  · simpa only [selected,mem_filter,mem_sums,map_intCast,if_true,
      ZMod.intCast_eq_intCast_iff'] using positive.symm

private theorem neg_sum {N : ℤ} {s : ZMod m} (mem : s∈sums m N) : -s∈sums m N := by
  obtain ⟨x,y,p,t⟩ := mem_sums.mp mem
  exact mem_sums.mpr ⟨-x,-y,by simpa only [neg_mul_neg] using p,
    by simpa only [neg_add_rev,add_comm] using congrArg Neg.neg t⟩

private theorem swap (div : 16∣m) {N : ℤ} {s : ZMod m} (b : Bool) (h : s∈selected div N b) :
    -s∈selected div N (!b) := by
  obtain ⟨allow,eq⟩ := mem_filter.mp h
  refine mem_filter.mpr ⟨neg_sum allow,?_⟩
  cases b <;> simpa only [Bool.not_true,Bool.not_false,Bool.false_eq_true,if_false,if_true,
    map_neg,Int.cast_neg,neg_neg] using congrArg Neg.neg eq

/-- Negation pairs the two signs, and the mod-16 gate ensures that these
signs exhaust the admissible labels and are disjoint. No coprimality with
the odd part of m is required. -/
theorem half (div : 16∣m) {N : ℤ} (gate : N%16=1 ∨ N%16=5) (yes : Bool) :
    2*(selected div N yes).card=(sums m N).card := by
  let f := ZMod.castHom div (ZMod 16)
  have good : (N:ZMod 16)=1 ∨ (N:ZMod 16)=5 := by
    rcases gate with h|h
    · exact Or.inl (by simpa only [Int.cast_one] using (ZMod.intCast_eq_intCast_iff' N 1 16).mpr h)
    · exact Or.inr (by simpa only [Int.cast_ofNat] using (ZMod.intCast_eq_intCast_iff' N 5 16).mpr h)
  have different : (N:ZMod 16)+1 ≠ -((N:ZMod 16)+1) := by
    rcases good with e|e <;> rw [e] <;> decide
  have classes : ∀ x y : ZMod 16, (x*y=1 ∨ x*y=5) →
      x+y=x*y+1 ∨ x+y=-(x*y+1) := by decide +kernel
  have union : selected div N true ∪ selected div N false=sums m N := by
    ext s
    constructor
    · intro h
      exact (mem_union.mp h).elim (fun h => (mem_filter.mp h).1) (fun h => (mem_filter.mp h).1)
    · intro h
      obtain ⟨a,b,prod,sum⟩ := mem_sums.mp h
      have p : f a*f b=(N:ZMod 16) := by rw [←map_mul,prod,map_intCast]
      have t : f a+f b=f s := by rw [←map_add,sum]
      have which := classes (f a) (f b) (p ▸ good)
      rw [p,t] at which
      rcases which with yes|no
      · exact mem_union_left _ (mem_filter.mpr ⟨h,by simpa only [if_true,Int.cast_add,Int.cast_one] using yes⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨h,by simpa only [Bool.false_eq_true,if_false,Int.cast_neg,
          Int.cast_add,Int.cast_one] using no⟩)
  have disjoint : Disjoint (selected div N true) (selected div N false) := by
    apply disjoint_left.mpr
    intro s l r
    have a := (mem_filter.mp l).2
    have b := (mem_filter.mp r).2
    exact different (by simpa only [if_true,Bool.false_eq_true,if_false,Int.cast_neg,Int.cast_add,Int.cast_one]
      using a.symm.trans b)
  have eq : (selected div N true).card=(selected div N false).card := by
    apply card_nbij' Neg.neg Neg.neg
    · exact fun s h => swap div true h
    · exact fun s h => swap div false h
    · exact fun s _ => neg_neg s
    · exact fun s _ => neg_neg s
  have total := congrArg Finset.card union
  rw [card_union_of_disjoint disjoint] at total
  cases yes <;> omega

end PrimeFactors.QuarticHalfSumResidues
