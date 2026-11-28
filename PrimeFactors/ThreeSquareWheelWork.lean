import PrimeFactors.SixSquareScoreLookupCost

/-! The first three auxiliary squares form a cyclic table shared by all score
streams for one product. Counts include the successful candidate. -/
namespace PrimeFactors.ThreeSquareWheelWork

open Finset SixSquareLookupStages
open MixedPrefixSample (eligible)
open WithinResidueSearchFloor (low target scoreVisits)
open FullRangeResidueEstimates (X)
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible

/-- The indices of the single step-100 cycle which pass all three squares. -/
noncomputable def slots (n : ℕ) : Finset (ZMod (period 3)) :=
  univ.filter fun j => (100 : ZMod (period 3))*j ∈ A n 3

private noncomputable def stride := ZMod.unitOfCoprime 100 (coprime 3)

/-- Each stream starts at a translate of the same cycle. -/
noncomputable def shift (start : ℕ) : ZMod (period 3) := (↑(stride⁻¹) : ZMod (period 3))*start

theorem slot_iff (n start j : ℕ) : (j : ZMod (period 3))+shift start∈slots n ↔
    ((start+100*j : ℕ) : ZMod (period 3))∈A n 3 := by
  have val : (stride : ZMod (period 3))=100 := ZMod.coe_unitOfCoprime ..
  have cancel : (100 : ZMod (period 3))*shift start=start := by
    rw [shift,←mul_assoc,←val,Units.mul_inv,one_mul]
  simp only [slots,mem_filter,mem_univ,true_and,mul_add,cancel,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  rw [add_comm]

theorem period_size : period 3=53361 := by decide +kernel

theorem slot_cap {n : ℕ} (unit : n.Coprime SixSquareAuxiliarySieve.L) : (slots n).card≤3465 := by
  have subset : (slots n).image (fun j => (100:ZMod (period 3))*j) ⊆ A n 3 := by
    rintro _ h
    obtain ⟨j,hj,rfl⟩ := mem_image.mp h
    exact (mem_filter.mp hj).2
  have inj : Function.Injective (fun j : ZMod (period 3) => 100*j) :=
    fun _ _ eq => ((ZMod.isUnit_iff_coprime 100 _).mpr (coprime 3)).mul_left_cancel eq
  have count := card_le_card subset
  rw [card_image_of_injective _ inj] at count
  exact (count.trans (card_bound unit 3)).trans_eq (by decide +kernel : cap 3=3465)

/-- One simple setup scans every wheel slot and charges three lookups for each. -/
def setup : ℕ := 3*53361

private theorem single_scan (m : ℕ) : (∑ _ ∈ range m,(3:ℕ))=3*m := by
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_id,mul_comm]

theorem setup_checks : (∑ _ ∈range (period 3), (3:ℕ))=setup :=
  (single_scan (period 3)).trans (congrArg (3*·) period_size)

/-- All candidates emitted through the successful score under the three-square wheel. -/
noncomputable def generated (v : ℕ×ℕ) := hits (v.1*v.2) 3 (scoreVisits v)

theorem mem_generated (v : ℕ×ℕ) (t : ℕ) : t∈generated v ↔ t∈scoreVisits v ∧
    ∀ i : Fin 6, i.val < 3 → AdmissibleSum ((v.1*v.2 : ℕ):ZMod ((prime i)^2)) (t:ZMod ((prime i)^2)) := by
  rw [generated,hits,mem_filter,SixSquareScoreLookupCost.entry]
  rfl

theorem unique_hit {v : ℕ×ℕ} (hv : v∈eligible) :
    (generated v).filter (fun t => IsSquare (t^2-4*(v.1*v.2)))={target v} := by
  obtain ⟨pl,pq,qu,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp hv
  have top : v.2<2*X := (by decide +kernel : WideResiduePrimeSupply.B=2*X) ▸ qu
  apply ScorePrefixSieve.true_hit (A (v.1*v.2) 3) (by decide +kernel : 3≤X) pl pq top pp qp
  rw [mem_A]
  exact ⟨v.1,v.2,by push_cast; rfl,by push_cast; rfl⟩

/-- A generated candidate is charged for each remaining test whose entry
conditions it meets. These are the entries before 13², 17² and 19². -/
private def tailStage (i : Fin 3) : Fin 7 := ⟨i.val+3,by omega⟩

noncomputable def remaining (v : ℕ×ℕ) := ∑ i : Fin 3,(hits (v.1*v.2) (tailStage i) (scoreVisits v)).card

theorem remaining_eq (v : ℕ×ℕ) : remaining v = (generated v).card+
    (hits (v.1*v.2) 4 (scoreVisits v)).card+(hits (v.1*v.2) 5 (scoreVisits v)).card := by
  rw [remaining,Fin.sum_univ_three]
  unfold generated
  rfl

private theorem tail_density : (∑ i : Fin 3,(cap (tailStage i):ℚ)/period (tailStage i))=265/2431 := by decide +kernel
private theorem tail_cap : (∑ i : Fin 3,cap (tailStage i))=37030455 := by decide +kernel

theorem generated_bound {v : ℕ×ℕ} (hv : v∈eligible) :
    77*(generated v).card≤5*(scoreVisits v).card+77*34650 := by
  let n := v.1*v.2
  have h := ScorePrefixSieve.filtered_bound (SixSquareScoreVisits.mod_five hv) (coprime 3)
    (A n 3) (low v) (ProductDeficitBand.sumCap n X) (target v)
  change period 3*(generated v).card≤(scoreVisits v).card*(A n 3).card+10*period 3*(A n 3).card at h
  have size := card_bound (SixSquareScoreVisits.product_coprime hv) 3
  have upper := h.trans (Nat.add_le_add (Nat.mul_le_mul_left _ size) (Nat.mul_le_mul_left _ size))
  rw [period_size,show cap 3=3465 by decide +kernel] at upper
  omega

theorem remaining_bound {v : ℕ×ℕ} (hv : v∈eligible) :
    (remaining v:ℚ)≤((scoreVisits v).card:ℚ)*(265/2431)+10*37030455 := by
  let n := v.1*v.2
  have h := ScorePrefixLookupWork.bound_of_caps (SixSquareScoreVisits.mod_five hv) (low v)
    (ProductDeficitBand.sumCap n X) (target v) (fun i : Fin 3 => period (tailStage i))
    (fun _ => NeZero.pos _) (fun i => coprime (tailStage i)) (fun i => A n (tailStage i))
    (fun i => cap (tailStage i)) (fun i => card_bound (SixSquareScoreVisits.product_coprime hv) (tailStage i))
  rw [tail_density,tail_cap] at h
  exact h

private theorem setup_and_remaining {old work : ℕ}
    (h : (work:ℚ)≤(old:ℚ)*(265/2431)+10*37030455) :
    2431*(setup+work)≤265*old+2431*370464633 := by
  have q : (2431:ℚ)*(160083+work)≤265*old+2431*370464633 := by linarith only [h]
  exact_mod_cast q

private theorem aggregate {α : Type*} (S : Finset α) (old : α→Finset ℕ) (work : α→ℕ) (a b c : ℕ)
    (each : ∀ v∈S,a*work v≤b*(old v).card+c) :
    a*(∑ v∈S,work v)≤b*(∑ v∈S,(old v).card)+S.card*c := by
  simpa only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,Nat.cast_id]
    using sum_le_sum (s:=S) each

private theorem round_generated {old new count : ℕ}
    (work : 77*new≤5*old+count*(77*34650)) (base : 2^891*count≤old) (positive : 0<count) :
    100000*new<6494*old := by omega

private theorem round_lookups {old new count : ℕ}
    (work : 2431*new≤265*old+count*(2431*370464633)) (base : 2^891*count≤old) (positive : 0<count) :
    100000*new<10901*old := by omega

private theorem generated_total {α : Type*} (S : Finset α) (V W : α→Finset ℕ)
    (base : 2^891*S.card≤∑ v∈S,(V v).card) (pos : 0<S.card)
    (each : ∀ v∈S,77*(W v).card≤5*(V v).card+77*34650) :
    100000*(∑ v∈S,(W v).card)<6494*(∑ v∈S,(V v).card) :=
  round_generated (aggregate S V (fun v => (W v).card) _ _ _ each) base pos

private theorem lookup_total {α : Type*} (S : Finset α) (V : α→Finset ℕ) (W : α→ℕ)
    (base : 2^891*S.card≤∑ v∈S,(V v).card) (pos : 0<S.card)
    (each : ∀ v∈S,(W v:ℚ)≤((V v).card:ℚ)*(265/2431)+10*37030455) :
    100000*(∑ v∈S,(setup+W v))<10901*(∑ v∈S,(V v).card) :=
  round_lookups (aggregate S V (fun v => setup+W v) _ _ _
    (fun v hv => setup_and_remaining (each v hv))) base pos

/-- Under 6.494% of the original candidates are emitted, including successful ones. -/
theorem generated_population :
    100000*(∑ v∈eligible,(generated v).card)<6494*(∑ v∈eligible,(scoreVisits v).card) :=
  generated_total eligible scoreVisits generated SixSquareScoreWork.baseline
    ((Nat.zero_le _).trans_lt WithinResidueSearchFloor.score_population) (fun _ hv => generated_bound hv)

/-- Under 10.901 scalar lookups per 100 original square tests in aggregate,
including one three-lookup-per-slot setup per product. -/
theorem lookup_population :
    100000*(∑ v∈eligible,(setup+remaining v))<10901*(∑ v∈eligible,(scoreVisits v).card) :=
  lookup_total eligible scoreVisits remaining SixSquareScoreWork.baseline
    ((Nat.zero_le _).trans_lt WithinResidueSearchFloor.score_population) (fun _ hv => remaining_bound hv)

end PrimeFactors.ThreeSquareWheelWork
