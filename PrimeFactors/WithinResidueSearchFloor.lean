import PrimeFactors.ScoreSumOrder
import PrimeFactors.ChebyshevPrimeSample
import PrimeFactors.SumGridPopulation

/-! A work floor for complete periodic menus that keep numerical order inside
each allowed residue. Each visited integer is charged one candidate check.
The schedule may interleave residues with full knowledge of the true target.
Further tests that skip members of the true residue require a different model. -/

namespace PrimeFactors.WithinResidueSearchFloor

open Finset PeriodicSumRank FactorSumPrefixCost GlobalSumOrderCost
open MixedPrefixSample (eligible)
open WideResiduePrimeSupply (B)
open FullRangeResidueEstimates (X)
open scoped Classical

set_option exponentiation.threshold 4096
attribute [local irreducible] eligible

/-- Every integer from the true residue through the successful target has
been visited. The modulo-M menu must accept the entire true residue. -/
def Covers (visits : Finset ℕ) (m lo s : ℕ) : Prop :=
  ∀ t, lo ≤ t → t ≤ s → t % m = s % m → t ∈ visits

/-- In a periodic menu, ascending order inside each admitted residue suffices
for coverage, regardless of the order between residues. -/
theorem covers_of_menu {visits : Finset ℕ} {m lo s : ℕ} (menu : ℕ → Prop)
    (hit : menu (s % m))
    (ascending_inside : ∀ t, lo ≤ t → t ≤ s → menu (t % m) → t % m = s % m → t ∈ visits) :
    Covers visits m lo s := by
  intro t lower upper eq
  exact ascending_inside t lower upper (eq.symm ▸ hit) eq

/-- The exact arithmetic progression ending at the target fits in the visited
set. The extra one counts the successful endpoint. -/
theorem prefix_floor {visits : Finset ℕ} {m lo s : ℕ} (mp : 0 < m) (lower : lo ≤ s)
    (cover : Covers visits m lo s) : (s-lo)/m + 1 ≤ visits.card := by
  let r := range ((s-lo)/m+1)
  have room {k : ℕ} (ok : k ∈ r) : k*m ≤ s-lo :=
    (Nat.le_div_iff_mul_le mp).mp (Nat.le_of_lt_succ (mem_range.mp ok))
  have count : r.card ≤ visits.card := by
    apply card_le_card_of_injOn (fun k => s-k*m)
    · intro k hk
      have h := room hk
      apply cover _ (by omega) (Nat.sub_le ..)
      have eq := Nat.sub_add_cancel (h.trans (Nat.sub_le s lo))
      calc
        (s-k*m)%m = (s-k*m+k*m)%m := by simp
        _ = s%m := congrArg (fun t => t%m) eq
    · intro k hk j hj eq
      have a := room hk
      have b := room hj
      change s-k*m = s-j*m at eq
      exact Nat.eq_of_mul_eq_mul_right mp (by omega)
  simpa only [r,card_range] using count

theorem ascending_covers {n lo s : ℕ} (target : passes (n%100) (s%100)=true) :
    Covers (passingPrefix n lo s) 100 lo s := by
  intro t low high cls
  exact mem_filter.mpr ⟨mem_Ico.mpr ⟨low, Nat.lt_succ_of_le high⟩, cls ▸ target⟩

theorem global_covers {n lo hi s : ℕ} (target : passes (n%100) (s%100)=true) :
    Covers (globalPrefix n lo hi s) 100 lo s := by
  intro t low high cls
  have inAsc := ascending_covers target t low high cls
  unfold globalPrefix
  split_ifs with mark
  · exact mem_filter.mpr ⟨inAsc,cls ▸ mark⟩
  · exact mem_union_left _ inAsc

theorem score_covers {n lo hi s : ℕ} (upper : s ≤ hi)
    (target : passes (n%100) (s%100)=true) :
    Covers (ScoreSumOrder.«prefix» n lo hi s) 100 lo s := by
  intro t low high cls
  exact ScoreSumOrder.mem_prefix.mpr ⟨⟨low,high.trans upper⟩,cls ▸ target,
    (ScoreSumOrder.same_group (congrArg (favored (n%100)) cls)).mpr high⟩

private abbrev Pair := ℕ × ℕ

def low (v : Pair) := ceilSqrt (4*(v.1*v.2))
def target (v : Pair) := v.1+v.2

noncomputable def short := eligible.filter (fun v => target v < low v+2^900)

/-- For uniformly drawn sorted, distinct 1024-bit primes with a full 2048-bit
product, fewer than one in 2^35 have sum less than 2^900 above the lower end.
The local Chebyshev proof supplies the denominator unconditionally. -/
theorem exceptional : 2^35*short.card < eligible.card := by
  have num : short.card ≤ 2^1986 := by
    apply FullRangeLongSumPrefix.wide_short_bound
    intro v hv
    obtain ⟨elig,h⟩ := mem_filter.mp hv
    obtain ⟨bot,ord,top,_⟩ := SumGridPopulation.eligible_data.mp elig
    exact ⟨bot,ord,top,h⟩
  have den := MixedPrefixSample.denominator ChebyshevPrimeSample.prime_count
  have margin : (21000000:ℕ)*(2^35*2^1986)<2^2046 := by decide +kernel
  have bound := Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left (2^35) num)
  exact Nat.lt_of_mul_lt_mul_left (bound.trans_lt (margin.trans den))

private theorem rare_of_long {visits : Pair → Finset ℕ} {n : ℕ}
    (work : ∀ v∈eligible, low v + 2^900 ≤ target v → n ≤ (visits v).card) :
    2^35*(eligible.filter (fun v => (visits v).card<n)).card < eligible.card := by
  have sub : eligible.filter (fun v => (visits v).card<n) ⊆ short := by
    intro v hv
    obtain ⟨member,small⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨member,lt_of_not_ge (fun h => (not_le_of_gt small) (work v member h))⟩
  exact (Nat.mul_le_mul_left _ (card_le_card sub)).trans_lt exceptional

/-- This bound even permits choosing the modulus and all visits separately
for each factor pair, provided that its true residue is complete. -/
theorem periods_at_most_128 (M : Pair → ℕ) (visits : Pair → Finset ℕ)
    (policy : ∀ v∈eligible, 0 < M v ∧ M v ≤ 2^128 ∧ Covers (visits v) (M v) (low v) (target v)) :
    2^35*(eligible.filter (fun v => (visits v).card<2^772)).card < eligible.card := by
  apply rare_of_long
  intro v ok width
  obtain ⟨mp,cap,cover⟩ := policy v ok
  have mul := (Nat.mul_le_mul_left (2^772) cap).trans_eq
    (by decide +kernel : (2:ℕ)^772*2^128=2^900)
  have pay := prefix_floor mp (by omega) cover
  have pos : 2^772 ≤ (target v-low v)/M v := (Nat.le_div_iff_mul_le mp).mpr
    (mul.trans (by omega))
  omega

theorem period_100 (visits : Pair → Finset ℕ)
    (policy : ∀ v∈eligible, Covers (visits v) 100 (low v) (target v)) :
    2^35*(eligible.filter (fun v => (visits v).card<2^893)).card < eligible.card := by
  apply rare_of_long
  intro v ok width
  have pay := prefix_floor (by decide : 0<100) (by omega) (policy v ok)
  have pos : 2^893 ≤ (target v-low v)/100 := (Nat.le_div_iff_mul_le (by decide)).mpr
    ((by decide +kernel : (2:ℕ)^893*100≤2^900).trans (by omega))
  omega

noncomputable def scoreVisits (v : Pair) :=
  ScoreSumOrder.«prefix» (v.1*v.2) (low v) (ProductDeficitBand.sumCap (v.1*v.2) X) (target v)

private theorem eligible_hit {v : Pair} (hv : v∈eligible) :
    target v ≤ ProductDeficitBand.sumCap (v.1*v.2) X ∧
    passes ((v.1*v.2)%100) ((target v)%100)=true := by
  obtain ⟨p,q⟩ := v
  obtain ⟨pl,pq,qh,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp hv
  have width : q < 2*X := (by decide : B=2*X) ▸ qh
  have hit := ScoreSumOrder.unique_hit (by decide : 3≤X) pl pq width pp qp
  dsimp only at hit
  have row := ScoreSumOrder.mem_prefix.mp (mem_filter.mp (hit.symm ▸ mem_singleton_self _)).1
  exact ⟨row.1.2,row.2.1⟩

/-- The actual score-ordered search incurs this floor with the successful
integer included. The population result needs no external estimate. -/
theorem score_population :
    2^35*(eligible.filter (fun v => (scoreVisits v).card<2^893)).card < eligible.card :=
  period_100 scoreVisits (fun _ hv => score_covers (eligible_hit hv).1 (eligible_hit hv).2)

noncomputable def ascendingVisits (v : Pair) := passingPrefix (v.1*v.2) (low v) (target v)

noncomputable def globalVisits (v : Pair) :=
  globalPrefix (v.1*v.2) (low v) (ProductDeficitBand.sumCap (v.1*v.2) X) (target v)

theorem ascending_population :
    2^35*(eligible.filter (fun v => (ascendingVisits v).card<2^893)).card < eligible.card :=
  period_100 ascendingVisits (fun v hv =>
    ascending_covers (n:=v.1*v.2) (s:=target v) (eligible_hit hv).2)

theorem global_population :
    2^35*(eligible.filter (fun v => (globalVisits v).card<2^893)).card < eligible.card :=
  period_100 globalVisits (fun v hv =>
    global_covers (n:=v.1*v.2) (s:=target v) (eligible_hit hv).2)

end PrimeFactors.WithinResidueSearchFloor
