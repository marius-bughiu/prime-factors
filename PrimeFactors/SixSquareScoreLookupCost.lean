import PrimeFactors.ScorePrefixLookupWork
import PrimeFactors.SixSquareLookupStages
import PrimeFactors.SixSquareScoreWork

/-! Scalar table lookups charged before each of the six auxiliary residue tests,
over score prefixes through the successful square test. The priced comparison
charges one unit per integer square test and a fixed price per scalar lookup. -/
namespace PrimeFactors.SixSquareScoreLookupCost

open Finset SixSquareLookupStages
open MixedPrefixSample (eligible)
open WithinResidueSearchFloor (low target scoreVisits)
open SixSquareScoreVisits (visits)
open FullRangeResidueEstimates (X)

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible

/-- The entry checks before the next scalar lookup correspond to passing every earlier prime. -/
theorem entry (n t : ℕ) (i : Fin 7) :
    (t:ZMod (period i))∈A n i ↔ ∀ j : Fin 6, j.val < i.val →
      AdmissibleSum (n:ZMod ((prime j)^2)) (t:ZMod ((prime j)^2)) := by
  induction i using Fin.induction with
  | zero => exact ⟨fun _ _ hj => (Nat.not_lt_zero _ hj).elim, fun _ => first n t⟩
  | succ i prev =>
    rw [step,prev]
    constructor
    · rintro ⟨before,now⟩ j hj
      change j.val < i.val+1 at hj
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with lt|eq
      · exact before j lt
      · exact (Fin.ext eq).symm ▸ now
    · intro h
      exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h i (Nat.lt_succ_self _)⟩

theorem short_circuit (n lo hi s : ℕ) :
    lookupWork n (ScoreSumOrder.«prefix» n lo hi s) = ∑ t∈ScoreSumOrder.«prefix» n lo hi s,
      ScorePrefixLookupWork.checks (fun i : Fin 6 => fun x : ℕ =>
        AdmissibleSum (n:ZMod ((prime i)^2)) (x:ZMod ((prime i)^2))) t :=
  ScorePrefixLookupWork.short_circuit n lo hi s (fun i : Fin 6 => period i.castSucc)
    (fun i => A n i.castSucc) _ (fun i t _ => entry n t i.castSucc)

/-- A prefix can end in an incomplete period in each of its at most ten streams. -/
theorem prefix_bound {n : ℕ} (five : n%5≠0) (unit : n.Coprime SixSquareAuxiliarySieve.L)
    (lo hi s : ℕ) :
    (lookupWork n (ScoreSumOrder.«prefix» n lo hi s):ℚ) ≤
      ((ScoreSumOrder.«prefix» n lo hi s).card:ℚ)*(80926/51051)+10*37030522 := by
  have h := ScorePrefixLookupWork.bound_of_caps five lo hi s (fun i : Fin 6 => period i.castSucc)
    (fun _ => NeZero.pos _) (fun i => coprime i.castSucc) (fun i => A n i.castSucc)
    (fun i => cap i.castSucc) (fun i => card_bound unit i.castSucc)
  rw [density_sum, cap_sum] at h
  exact h

/-- Number of scalar residue lookups through the actual factor sum for this ordered pair. -/
noncomputable def work (v : ℕ×ℕ) := lookupWork (v.1*v.2) (scoreVisits v)

theorem pointwise {v : ℕ×ℕ} (hv : v∈eligible) :
    (work v:ℚ) ≤ ((scoreVisits v).card:ℚ)*(80926/51051)+10*37030522 :=
  prefix_bound (SixSquareScoreVisits.mod_five hv) (SixSquareScoreVisits.product_coprime hv)
    (low v) (ProductDeficitBand.sumCap (v.1*v.2) X) (target v)

private theorem clear_fraction {old new : ℕ}
    (h : (new:ℚ) ≤ (old:ℚ)*(80926/51051)+10*37030522) :
    51051*new≤80926*old+51051*370305220 := by
  have q : (51051:ℚ)*new≤80926*old+51051*370305220 := by linarith only [h]
  exact_mod_cast q

private theorem round_total {old new count : ℕ}
    (h : 51051*new≤80926*old+count*(51051*370305220))
    (base : 2^891*count≤old) (positive : 0<count) :
    10000*new<15852*old := by omega

private theorem totals {α : Type*} (S : Finset α) (old : α→Finset ℕ) (new : α→ℕ)
    (base : 2^891*S.card≤∑ v∈S,(old v).card) (positive : 0<S.card)
    (each : ∀ v∈S,(new v:ℚ)≤((old v).card:ℚ)*(80926/51051)+10*37030522) :
    10000*(∑ v∈S,new v)<15852*(∑ v∈S,(old v).card) := by
  have h := sum_le_sum (s:=S) (fun v hv => clear_fraction (each v hv))
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,Nat.cast_id] at h
  apply round_total (count:=S.card) _ base positive
  rw [Nat.mul_left_comm 51051 S.card] at h
  exact h

/-- In aggregate there are fewer than 1.5852 scalar lookups for each square test
in the original score order. This ratio includes the prefixes on every eligible pair. -/
theorem population : 10000*(∑ v∈eligible,work v)<15852*(∑ v∈eligible,(scoreVisits v).card) :=
  totals eligible scoreVisits work SixSquareScoreWork.baseline
    ((Nat.zero_le _).trans_lt WithinResidueSearchFloor.score_population) (fun _ hv => pointwise hv)

private theorem price_bound {old new look : ℕ} (square : 1000000*new<6681*old)
    (lookups : 10000*look<15852*old) {price : ℚ} (hp : 0≤price) :
    (new:ℚ)+price*look < (6681/1000000+price*(15852/10000))*(old:ℚ) := by
  have hs : (1000000:ℚ)*new<6681*old := by exact_mod_cast square
  have hl : (10000:ℚ)*look<15852*old := by exact_mod_cast lookups
  have sq : (new:ℚ)<(6681/1000000)*(old:ℚ) := by linarith only [hs]
  have lk : (look:ℚ)≤(15852/10000)*(old:ℚ) := by linarith only [hl]
  exact (add_lt_add_of_lt_of_le sq (mul_le_mul_of_nonneg_left lk hp)).trans_eq (by ring)

/-- Total normalized cost for the two counted operations at a supplied lookup price. -/
theorem priced {price : ℚ} (hp : 0≤price) :
    ((∑ v∈eligible,(visits v).card:ℕ):ℚ)+price*(∑ v∈eligible,work v:ℕ) <
    (6681/1000000+price*(15852/10000))*((∑ v∈eligible,(scoreVisits v).card:ℕ):ℚ) :=
  price_bound SixSquareScoreWork.population population hp

/-- At this price or below, the two-operation total is strictly below the original
square-test total. Table setup and other work are outside the price model. -/
theorem cheaper {price : ℚ} (hp : 0≤price) (limit : price≤993319/1585200) :
    ((∑ v∈eligible,(visits v).card:ℕ):ℚ)+price*(∑ v∈eligible,work v:ℕ) <
      ((∑ v∈eligible,(scoreVisits v).card:ℕ):ℚ) := by
  have coeff : (6681/1000000:ℚ)+price*(15852/10000)≤1 := by linarith only [limit]
  exact (priced hp).trans_le (mul_le_of_le_one_left (Nat.cast_nonneg _) coeff)

end PrimeFactors.SixSquareScoreLookupCost
