import PrimeFactors.PersistentScorePrefix
import PrimeFactors.PrimeMenuPeriodMinimum

/-! An individual full-width product may have its own set of test primes.
Every permitted menu still leaves many wrong candidates in the actual early
score prefix outside a common exceptional set of prime pairs. -/
namespace PrimeFactors.PrimeMenuScorePrefix

open Finset ArbitraryMidpointMenu
open WithinResidueSearchFloor (low target scoreVisits)
open MixedPrefixSample (eligible)
open FullRangeResidueEstimates (X)
open private PrimeFactors.PersistentScorePrefix.false_square from PrimeFactors.PersistentScorePrefix
open private PrimeFactors.WithinResidueSearchFloor.rare_of_long
  PrimeFactors.WithinResidueSearchFloor.eligible_hit from PrimeFactors.WithinResidueSearchFloor
open scoped Classical

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible

/-- The primary score menu uses 5. The period accounts for 2 and 3 separately. -/
def Permitted (S : Finset ℕ) : Prop :=
  5∈S ∧ (∀ p∈S,p.Prime ∧ 5≤p) ∧ period S≤2^896

/-- Each selected base fits below the factor-width endpoint, so no menu in
the stated budget can include a prime divisor of an eligible product. -/
theorem units {v : ℕ×ℕ} (hv : v∈eligible) {S : Finset ℕ} (allow : Permitted S) :
    ∀ p∈bases S, ¬p∣v.1*v.2 := by
  obtain ⟨_,valid,budget⟩ := allow
  obtain ⟨pl,ord,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp hv
  have prodPos := prod_pos (s:=S) (f:=fun p => p) (fun p hp => (valid p hp).1.pos)
  have cost : 3456*(∏ p∈S,p)≤2^896 := budget
  have bound : (∏ p∈S,p)≤2^896 := by omega
  have cap : (2:ℕ)^896<X := by decide +kernel
  have large : 3<X := by decide +kernel
  intro p hp
  have props : p.Prime ∧ p<X := by
    rcases mem_insert.mp hp with rfl|rest
    · exact ⟨Nat.prime_two,(by decide : 2<3).trans large⟩
    rcases mem_insert.mp rest with rfl|inS
    · exact ⟨Nat.prime_three,large⟩
    · exact ⟨(valid p inS).1,(Nat.le_of_dvd prodPos (dvd_prod_of_mem (fun q => q) inS)).trans_lt
        (bound.trans_lt cap)⟩
  have a := pp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt props.1.pos (props.2.trans_le pl))
  have b := qp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt props.1.pos ((props.2.trans_le pl).trans ord))
  exact props.1.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_left.mpr ⟨a,b⟩).symm

private theorem local_factors {S : Finset ℕ} {n h : ℕ} (ok : Passes S n h) {p : ℕ}
    (hp : p∈bases S) (e : ℕ) : AdmissibleSum (n:ZMod (p^e)) ((2*h:ℕ):ZMod (p^e)) := by
  rw [Nat.cast_mul,Nat.cast_ofNat,LocalMidpointLanes.midpoint_iff]
  simpa only [Int.cast_sub,Int.cast_pow,Int.cast_natCast] using ok p hp e

/-- The all-depth hypotheses imply both components of the original mod-100 row. -/
theorem passes_menu {S : Finset ℕ} (five : 5∈S) {n h : ℕ} (odd : n%2=1) (pass : Passes S n h) :
    PeriodicSumRank.passes (n%100) (2*h%100)=true := by
  apply (PeriodicSumRank.passes_iff n (2*h)).mpr
  exact ⟨(PublicWheelLookupCosts.first_prefix odd _).mp (local_factors pass (mem_insert_self ..) 2),
    local_factors pass (mem_insert_of_mem (mem_insert_of_mem five)) 2⟩

/-- Wrong sums in the first 2^896 midpoint offsets that were actually reached
and cannot be rejected using any precision at any of the chosen bases. -/
noncomputable def wrong (S : Finset ℕ) (v : ℕ×ℕ) :=
  let n := v.1*v.2
  let start := n.sqrt+1
  (scoreVisits v).filter (fun t => t<target v ∧ t/2∈Ico start (start+2^896) ∧
    t=2*(t/2) ∧ Passes S n (t/2) ∧ ¬IsSquare (t^2-4*n))

theorem evidence {S : Finset ℕ} {v : ℕ×ℕ} {t : ℕ} (inside : t∈wrong S v) :
    t∈scoreVisits v ∧ t<target v ∧ ¬IsSquare (t^2-4*(v.1*v.2)) ∧
    ∀ p∈bases S, ∀ e : ℕ, AdmissibleSum ((v.1*v.2:ℕ):ZMod (p^e)) (t:ZMod (p^e)) ∧
      IsSquare ((t^2-4*(v.1*v.2):ℕ):ZMod (p^e)) := by
  obtain ⟨visit,lt,_,even,ok,bad⟩ := mem_filter.mp inside
  refine ⟨visit,lt,bad,?_⟩
  intro p hp e
  have f := local_factors ok hp e
  rw [←even] at f
  have lower : ceilSqrt (4*(v.1*v.2))≤t := (ScoreSumOrder.mem_prefix.mp visit).1.1
  refine ⟨f,?_⟩
  rw [Nat.cast_sub (ceilSqrt_le_iff.mp lower),Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat]
  obtain ⟨x,y,prod,sum⟩ := f
  exact ⟨x-y,by rw [←prod,←sum]; ring⟩

/-- Every distinct surviving early midpoint contributes a distinct actual wrong visit. -/
theorem tally {v : ℕ×ℕ} (hv : v∈eligible) (long : low v+2^900≤target v)
    {S : Finset ℕ} (five : 5∈S) (unit : ∀ p∈bases S, ¬p∣v.1*v.2) :
    Nat.card (survivors S ((v.1*v.2).sqrt+1) (2^896) (v.1*v.2))≤(wrong S v).card := by
  let n := v.1*v.2
  let start := n.sqrt+1
  have two : ¬2∣n := unit 2 (mem_insert_self ..)
  have odd : n%2=1 := by omega
  have np : 0<n := Nat.pos_of_ne_zero (fun hz => two (hz ▸ dvd_zero _))
  have member (k : Fin (2^896)) (ok : Passes S n (start+k.val)) :
      2*(start+k.val)∈wrong S v := by
    have lt : 2*(start+k.val)<target v := (EarlyScoreWindow.early np long k.isLt).2.1
    have visit : 2*(start+k.val)∈scoreVisits v := EarlyScoreWindow.mem_prefix np long k.isLt
      (PrimeFactors.WithinResidueSearchFloor.eligible_hit hv).1 (passes_menu five odd ok)
    apply mem_filter.mpr
    refine ⟨visit,lt,?_,?_,?_,PrimeFactors.PersistentScorePrefix.false_square hv visit lt⟩
    · simp only [Nat.mul_div_cancel_left _ (by decide : 0<2),mem_Ico]
      exact ⟨Nat.le_add_right _ _,Nat.add_lt_add_left k.isLt _⟩
    · rw [Nat.mul_div_cancel_left _ (by decide : 0<2)]
    · simpa only [Nat.mul_div_cancel_left _ (by decide : 0<2)] using ok
  let f (k : survivors S start (2^896) n) : wrong S v := ⟨2*(start+k.val.val),member k.val k.property⟩
  have inj : Function.Injective f := by
    intro k j eq
    have same : 2*(start+k.val.val)=2*(start+j.val.val) := congrArg Subtype.val eq
    exact Subtype.ext (Fin.ext (by omega))
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective f inj

theorem long_floor {v : ℕ×ℕ} (hv : v∈eligible) (long : low v+2^900≤target v)
    {S : Finset ℕ} (allow : Permitted S) : 2^765<(wrong S v).card := by
  have unit := units hv allow
  exact (PrimeMenuPeriodMinimum.count S ((v.1*v.2).sqrt+1) (v.1*v.2) allow.2.1 allow.2.2 unit).trans_le
    (tally hv long allow.1 unit)

/-- The exceptional set is common to every menu. Even selecting the menu using
both actual primes cannot move any long prefix into this set. -/
theorem simultaneous_population :
    2^35*(eligible.filter (fun v => ∃ S, Permitted S ∧ (wrong S v).card≤2^765)).card<eligible.card := by
  apply lt_of_le_of_lt _ WithinResidueSearchFloor.exceptional
  apply Nat.mul_le_mul_left _ (card_le_card _)
  intro v hv
  obtain ⟨mem,S,allow,few⟩ := mem_filter.mp hv
  exact mem_filter.mpr ⟨mem,lt_of_not_ge (fun long => not_le_of_gt (long_floor mem long allow) few)⟩

/-- Specializing to one potentially different menu for each factor pair also
covers any rule which chooses its menu from the product alone. -/
theorem population (menu : (ℕ×ℕ)→Finset ℕ) (valid : ∀ v∈eligible,Permitted (menu v)) :
    2^35*(eligible.filter (fun v => (wrong (menu v) v).card≤2^765)).card<eligible.card := by
  have h := PrimeFactors.WithinResidueSearchFloor.rare_of_long (visits:=fun v => wrong (menu v) v) (n:=2^765+1)
    (fun v hv long => long_floor hv long (valid v hv))
  simpa only [Nat.lt_succ_iff] using h

end PrimeFactors.PrimeMenuScorePrefix
