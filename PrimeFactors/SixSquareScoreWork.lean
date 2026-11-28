import PrimeFactors.SixSquareScoreVisits
import PrimeFactors.ScorePrefixSieve

/-! The number of integer square tests through the first hit after six
additional small-square filters. The comparison uses the same scored
order on the remaining candidates, for every eligible full-size input. -/
namespace PrimeFactors.SixSquareScoreWork

open Finset
open MixedPrefixSample (eligible)
open WithinResidueSearchFloor (scoreVisits low target)
open SixSquareScoreVisits (visits)
open SixSquareAuxiliarySieve (A L)
open FullRangeResidueEstimates (X)
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible

/-- The exact-density term and a ten-stream allowance for partial periods. -/
theorem pointwise {v : ℕ×ℕ} (hv : v∈eligible) :
    940839860961*(visits v).card≤6285399120*(scoreVisits v).card+10*940839860961*6285399120 := by
  let n := v.1*v.2
  have bound := ScorePrefixSieve.filtered_bound (SixSquareScoreVisits.mod_five hv)
    SixSquareAuxiliarySieve.coprime (A n) (low v) (ProductDeficitBand.sumCap n X) (target v)
  have cap := SixSquareAuxiliarySieve.card_bound (SixSquareScoreVisits.product_coprime hv)
  change L*(visits v).card≤(scoreVisits v).card*(A n).card+10*L*(A n).card at bound
  have limit := bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ cap) (Nat.mul_le_mul_left _ cap))
  simpa only [SixSquareAuxiliarySieve.value,Nat.mul_comm 6285399120 (scoreVisits v).card] using limit

private theorem ratio {old new count : ℕ}
    (work : 940839860961*new≤6285399120*old+(10*940839860961*6285399120)*count)
    (scale : 2^891*count≤old) (positive : 0<count) : 1000000*new<6681*old := by
  omega

/-- The bound applies separately to any input whose earlier order visits
at least 2^891 candidates before the square hit. -/
theorem long {v : ℕ×ℕ} (hv : v∈eligible) (size : 2^891≤(scoreVisits v).card) :
    1000000*(visits v).card<6681*(scoreVisits v).card :=
  ratio (count:=1) (by simpa only [Nat.mul_one] using pointwise hv)
    (by simpa only [Nat.mul_one] using size) (by decide)

private theorem large_baseline {α : Type*} (S : Finset α) (cost : α→ℕ)
    (few : 2^35*(S.filter (fun x => cost x<2^893)).card<S.card) :
    2^891*S.card≤∑ x∈S,cost x := by
  let small (x : α) := cost x<2^893
  let many := S.filter fun x => ¬small x
  have partition := filter_card_add_filter_neg_card_eq_card (s:=S) small
  change (S.filter small).card+many.card=S.card at partition
  change 2^35*(S.filter small).card<S.card at few
  have half : S.card≤2*many.card := by omega
  have enough : 2^891*S.card≤many.card*2^893 := calc
    _ ≤ 2^891*(2*many.card) := Nat.mul_le_mul_left _ half
    _ = many.card*(2^891*2) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by decide +kernel)
  have mass := sum_le_sum (s:=many) (f:=fun _ => 2^893) (g:=cost)
    (fun x hx => Nat.le_of_not_gt (mem_filter.mp hx).2)
  have all := sum_le_sum_of_subset (f:=cost) (filter_subset (fun x => ¬small x) S)
  exact (enough.trans (by simpa only [sum_const,nsmul_eq_mul,Nat.cast_id] using mass)).trans all

private theorem large_baseline_visits {α : Type*} (S : Finset α) (V : α→Finset ℕ)
    (few : 2^35*(S.filter (fun x => (V x).card<2^893)).card<S.card) :
    2^891*S.card≤∑ x∈S,(V x).card :=
  large_baseline S (fun x => (V x).card) few

/-- The previous work floor on almost every pair bounds the total old work
from below. Short searches are included in the denominator. -/
theorem baseline : 2^891*eligible.card ≤ ∑ v∈eligible,(scoreVisits v).card :=
  large_baseline_visits eligible scoreVisits WithinResidueSearchFloor.score_population

private theorem totals {α : Type*} (S : Finset α) (old new : α→ℕ)
    (base : 2^891*S.card≤∑ v∈S,old v) (nonempty : 0<S.card)
    (bound : ∀ v∈S,940839860961*new v≤6285399120*old v+10*940839860961*6285399120) :
    1000000*(∑ v∈S,new v)<6681*(∑ v∈S,old v) := by
  have work := sum_le_sum (s:=S) bound
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,Nat.cast_id] at work
  apply ratio (count:=S.card) _ base nonempty
  simpa only [Nat.mul_comm S.card,Nat.mul_assoc] using work

private theorem visits_totals {α : Type*} (S : Finset α) (V W : α→Finset ℕ)
    (base : 2^891*S.card≤∑ v∈S,(V v).card) (nonempty : 0<S.card)
    (bound : ∀ v∈S,940839860961*(W v).card≤6285399120*(V v).card+10*940839860961*6285399120) :
    1000000*(∑ v∈S,(W v).card)<6681*(∑ v∈S,(V v).card) :=
  totals S (fun v=> (V v).card) (fun v=> (W v).card) base nonempty bound

/-- Over all distinct eligible prime pairs, the new search spends under
0.6681% of the old number of square tests, charging the successful test.
Small-residue lookups are a separate cost. -/
theorem population :
    1000000*(∑ v∈eligible,(visits v).card)<6681*(∑ v∈eligible,(scoreVisits v).card) :=
  visits_totals eligible scoreVisits visits baseline
    ((Nat.zero_le _).trans_lt WithinResidueSearchFloor.score_population) (fun _ hv => pointwise hv)

end PrimeFactors.SixSquareScoreWork
