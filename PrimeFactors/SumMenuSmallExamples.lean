import PrimeFactors.DyadicPairSumWeight
import PrimeFactors.SumMenuWeightThreshold

/-! All ordered odd residue pairs of a fixed product modulo 512. The
two examples have different optimal sums and the same optimal coverage
with five guesses. -/
namespace PrimeFactors.SumMenuSmallExamples

open Finset PrimeSquareSumWeights

abbrev Residue := ZMod 512
noncomputable abbrev top65 : Finset Residue := {130,382}
noncomputable abbrev ties65 : Finset Residue := {18,66,110,146,190,238,274,322,366,402,446,494}
noncomputable abbrev top209 : Finset Residue := {210,302}
noncomputable abbrev ties209 : Finset Residue := {30,98,110,146,158,226,286,354,366,402,414,482}

private abbrev Row := ℕ×ℕ×ℕ

/-- One pair and the exponent of two dividing its ordinary positive
difference. The local gap law gives the weight for its sum. -/
private def validates (n : ℕ) (s : Residue) (mass : ℕ) (r : Row) : Prop :=
  let a := r.1
  let b := r.2.1
  let t := r.2.2
  let u := (b-a)/2^t
  0<t ∧ Odd u ∧ b=a+2^t*u ∧ b*a ≡ n [MOD 512] ∧ (b+a:ℕ)=s.val ∧
    (if 9≤2*t then 16 else 2^(t+1))=mass

private noncomputable instance (n : ℕ) (s : Residue) (mass : ℕ) (r : Row) :
    Decidable (validates n s mass r) := by unfold validates; infer_instance

private theorem weight_of_row {n k : ℕ} {s : Residue} {r : Row} (h : validates n s k r) :
    weight n s=k := by
  rcases r with ⟨a,b,t⟩
  obtain ⟨pos,odd,gap,prod,sum,mass⟩ := h
  let u := (b-a)/2^t
  have product : (b:Residue)*a=n := by exact_mod_cast (ZMod.natCast_eq_natCast_iff ..).mpr prod
  have diff : (b:Residue)-a=((2^t*u:ℕ):Residue) := by
    have cast := congrArg (fun z : ℕ => (z:Residue)) gap
    push_cast at cast ⊢
    linear_combination cast
  have label : (b:Residue)+a=s := by rw [←Nat.cast_add,sum,ZMod.natCast_zmod_val]
  have result := DyadicPairSumWeight.pair_weight (e:=9) pos odd product diff
  rw [label] at result
  exact result.trans mass

private noncomputable abbrev rows65 : Finset Row :=
  {(9,121,4),(7,375,4),(5,13,3),(1,65,6),(11,99,3),(21,125,3),(15,175,5),
   (19,219,3),(37,237,3),(17,305,5),(3,363,3),(29,373,3),(31,415,7),(51,443,3)}
private noncomputable abbrev rows209 : Finset Row :=
  {(1,209,4),(15,287,4),(11,19,3),(37,61,3),(7,103,5),(9,137,7),(35,123,3),
   (13,213,3),(43,243,3),(5,349,3),(23,343,6),(25,377,5),(3,411,3),(45,437,3)}

private theorem receipt {n : ℕ} {H T : Finset Residue} (rows : Finset Row)
    (hi : ∀ s∈H,∃ r∈rows,validates n s 32 r) (lo : ∀ s∈T,∃ r∈rows,validates n s 16 r) :
    (∀ s∈H,weight n s=32) ∧ (∀ s∈T,weight n s=16) := by
  constructor
  · intro s hs
    obtain ⟨_,_,h⟩ := hi s hs
    exact weight_of_row h
  · intro s hs
    obtain ⟨_,_,h⟩ := lo s hs
    exact weight_of_row h

private theorem mass65 : (∀ s∈top65,weight 65 s=32) ∧ (∀ s∈ties65,weight 65 s=16) :=
  receipt rows65 (by decide +kernel) (by decide +kernel)
private theorem mass209 : (∀ s∈top209,weight 209 s=32) ∧ (∀ s∈ties209,weight 209 s=16) :=
  receipt rows209 (by decide +kernel) (by decide +kernel)

/-- The complete 14 labels already account for all 256 ordered pairs.
Hence no unlisted sum can improve a menu. -/
private theorem account {n : ℕ} {H T : Finset Residue} (unit : Nat.Coprime n 512)
    (sizes : H.card=2 ∧ T.card=12) (dis : Disjoint H T)
    (masses : (∀ s∈H,weight n s=32) ∧ (∀ s∈T,weight n s=16)) :
    (∀ s,weight n s=if s∈H then 32 else if s∈T then 16 else 0) ∧
    IsGreatest {k : ℕ | ∃ S : Finset Residue,S.card≤5 ∧ k=∑ s∈S,weight n s} 112 := by
  have highs : ∑ s∈H,weight n s=64 := by simp only [sum_congr rfl masses.1,sum_const,sizes.1]; decide
  have lows : ∑ s∈T,weight n s=192 := by simp only [sum_congr rfl masses.2,sum_const,sizes.2]; decide
  have total : ∑ s : Residue,weight n s=256 := by
    rw [←LocalSumGuessCoverage.covered_eq_sum,LocalSumGuessCoverage.covered_univ,
      PrimeSquareSumWeights.total ((ZMod.isUnit_iff_coprime _ _).mpr unit)]
    decide +kernel
  have outside {s : Residue} (miss : s∉H∪T) : weight n s=0 := by
    have limit := sum_le_univ_sum_of_nonneg (fun x : Residue => Nat.zero_le (weight n x)) (s:=insert s (H∪T))
    rw [sum_insert miss,sum_union dis,highs,lows,total] at limit
    omega
  have table (s : Residue) : weight n s=if s∈H then 32 else if s∈T then 16 else 0 := by
    split_ifs with hi lo
    · exact masses.1 s hi
    · exact masses.2 s lo
    · exact outside (by simp [hi,lo])
  refine ⟨table,?_⟩
  have result := SumMenuWeightThreshold.optimal (weight n) H (H∪T) 5 16
    subset_union_left (by omega) (by rw [card_union_of_disjoint dis,sizes.1,sizes.2]; decide)
    (fun s hs => by rw [masses.1 s hs]; decide)
    (fun s hs => by rw [table,if_neg hs]; split <;> decide)
    (fun s hs => masses.2 s ((mem_union.mp (mem_sdiff.mp hs).1).resolve_left (mem_sdiff.mp hs).2))
  simpa only [highs,sizes.1] using result

theorem product65 :
    (∀ s,weight 65 s=if s∈top65 then 32 else if s∈ties65 then 16 else 0) ∧
    IsGreatest {k : ℕ | ∃ S : Finset Residue,S.card≤5 ∧ k=∑ s∈S,weight 65 s} 112 :=
  account (by decide) (by decide +kernel) (by decide +kernel) mass65

theorem product209 :
    (∀ s,weight 209 s=if s∈top209 then 32 else if s∈ties209 then 16 else 0) ∧
    IsGreatest {k : ℕ | ∃ S : Finset Residue,S.card≤5 ∧ k=∑ s∈S,weight 209 s} 112 :=
  account (by decide) (by decide +kernel) (by decide +kernel) mass209

/-- One concrete optimum for each product. Other selections of three
among the twelve tied labels have the same mass. -/
theorem example_menus :
    LocalSumGuessCoverage.covered 65 ({130,382,18,66,110} : Finset Residue)=112 ∧
    LocalSumGuessCoverage.covered 209 ({210,302,30,98,110} : Finset Residue)=112 := by
  constructor
  · rw [LocalSumGuessCoverage.covered_eq_sum]
    simp_rw [product65.1]; decide +kernel
  · rw [LocalSumGuessCoverage.covered_eq_sum]
    simp_rw [product209.1]; decide +kernel

end PrimeFactors.SumMenuSmallExamples
