import PrimeFactors.SixTraceResidues
import PrimeFactors.SwitchedBatchComparison

/-! Compare equal square-test budgets at multiplier six. The starting
integer need not be aligned to either residue schedule. -/
namespace PrimeFactors.SixTraceBudget
open Finset SixTraceResidues InteriorBatchPopulation

set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

/-- Number of admissible labels strictly below x. In a final incomplete
block of six only residue one can occur. -/
def unitCount (x : ℕ) : ℕ := 2*(x/6) + if 1<x%6 then 1 else 0

/-- Certify the public starting label by two integer square comparisons. -/
theorem first_of_squares {n f : ℕ} (lower : (f-1)^2<24*n) (upper : 24*n≤f^2) :
    ceilSqrt (24*n)=f := by
  apply le_antisymm (ceilSqrt_le_iff.mpr upper)
  by_contra! h
  have earlier : ceilSqrt (24*n) ≤ f-1 := by omega
  exact (not_le_of_gt lower) (ceilSqrt_le_iff.mp earlier)

private theorem unit_succ (x : ℕ) :
    unitCount (x+1)=unitCount x + if admissible x then 1 else 0 := by
  simp only [unitCount,admissible]
  split_ifs <;> omega

theorem unitCount_eq (x : ℕ) : ((range x).filter admissible).card=unitCount x := by
  induction x with
  | zero => decide
  | succ x ih =>
    rw [Finset.card_filter] at ih ⊢
    rw [sum_range_succ,ih,unit_succ]

theorem oddCount_eq (x : ℕ) : ((range x).filter (fun s => s%2=1)).card=x/2 := by
  induction x with
  | zero => decide
  | succ x ih =>
    rw [Finset.card_filter] at ih ⊢
    rw [sum_range_succ,ih]
    split_ifs <;> omega

private theorem odd_decomposition (x : ℕ) : unitCount x+(x+2)/6=x/2 := by
  simp only [unitCount]
  split_ifs <;> omega

/-- The label is in the first budget odd labels if fewer than budget odd
labels between first (inclusive) and that label (exclusive) precede it. -/
def oddHit (n first budget : ℕ) : Prop :=
  ∃ s, first≤s ∧ s%2=1 ∧ s/2<first/2+budget ∧ properSquare n 6 s

/-- The same rank criterion after the mod-six filter. -/
def unitHit (n first budget : ℕ) : Prop :=
  ∃ s, first≤s ∧ admissible s ∧ unitCount s<unitCount first+budget ∧ properSquare n 6 s

/-- Filtering never sacrifices a split at a fixed number of square tests. -/
theorem retain {n first budget : ℕ} (unit : n.Coprime 6)
    (hit : oddHit n first budget) : unitHit n first budget := by
  obtain ⟨s,lo,_,rank,square⟩ := hit
  have allowed := of_square unit square.1
  refine ⟨s,lo,allowed,?_,square⟩
  have firstCount := odd_decomposition first
  have lastCount := odd_decomposition s
  omega

/-- The earliest possible proper square for balanced prime factors has
label 3p+2q. The other three allocations of six can only increase it. -/
theorem min_label {p q s : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p<q)
    (balanced : q≤2*p) (hit : properSquare (p*q) 6 s) : 3*p+2*q≤s := by
  obtain ⟨sq,lo,hi⟩ := hit
  let d := (s^2-4*6*(p*q)).sqrt
  have h := OffsetSquareSplit.root_identities (k:=1) (N:=6*(p*q)) (d:=d) (S:=s)
    (by simpa only [d,one_pow,mul_one,mul_assoc] using sq)
  dsimp only at h
  obtain ⟨a,b,w,tr⟩ := ShiftedEndpointPopulation.allocation pp qp order.ne
    (by simpa using h.2 : (s+d)/2*((s-d)/2)=6*(p*q)) lo hi
  rw [h.1] at tr
  have bound : a≤6 := Nat.le_of_dvd (by decide) ⟨b,w⟩
  have forms : (a=1 ∧ b=6) ∨ (a=2 ∧ b=3) ∨ (a=3 ∧ b=2) ∨ (a=6 ∧ b=1) := by
    interval_cases a <;> omega
  rcases forms with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega

theorem min_splits {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (unit : (p*q).Coprime 6) : properSquare (p*q) 6 (3*p+2*q) := by
  let s := 3*p+2*q
  have ident := multiplier_sum_square p q 3 2
  change s^2=24*(p*q)+(3*p).dist (2*q)^2 at ident
  change s^2=24*(p*q)+(s^2-24*(p*q)).sqrt^2 ∧ _
  constructor
  · rw [ident,Nat.add_sub_cancel_left,Nat.sqrt_eq']
  · have g := WeightedTracePrefix.shared_gcd (p:=p) (q:=q) rfl (a:=3) (b:=2) (by decide : 3*2=6) unit.symm rfl
    rcases g with hp|hq
    · rw [hp]
      exact ⟨pp.one_lt,by nlinarith only [Nat.mul_le_mul_left p qp.two_le,pp.pos]⟩
    · rw [hq]
      exact ⟨qp.one_lt,by nlinarith only [Nat.mul_le_mul_right q pp.two_le,qp.pos]⟩

/-- first+(1-first%2)+2*budget is the first omitted odd label. -/
theorem odd_miss_of_endpoint {p q first budget : ℕ} (pp : p.Prime) (qp : q.Prime)
    (order : p<q) (balanced : q≤2*p)
    (beyond : first+(1-first%2)+2*budget ≤ 3*p+2*q) : ¬oddHit (p*q) first budget := by
  rintro ⟨s,_,odd,rank,split⟩
  have lo := min_label pp qp order balanced split
  omega

theorem unit_hit_at_minimum {p q first budget : ℕ} (pp : p.Prime) (qp : q.Prime)
    (unit : (p*q).Coprime 6) (lo : first≤3*p+2*q)
    (rank : unitCount (3*p+2*q)<unitCount first+budget) : unitHit (p*q) first budget := by
  have split := min_splits pp qp unit
  exact ⟨3*p+2*q,lo,of_square unit split.1,rank,split⟩

/-- Given the factors for analysis, these are exact budget thresholds for
both product-only searches, including the first square at the cutoff. -/
theorem exact_ranks {p q budget : ℕ} (pp : p.Prime) (qp : q.Prime) (pq : p<q)
    (balanced : q≤2*p) (unit : (p*q).Coprime 6) :
    let first := ceilSqrt (24*(p*q))
    let target := 3*p+2*q
    (oddHit (p*q) first budget ↔ target/2 < first/2+budget) ∧
    (unitHit (p*q) first budget ↔ unitCount target < unitCount first+budget) := by
  let first := ceilSqrt (24*(p*q))
  let target := 3*p+2*q
  have square := min_splits pp qp unit
  have lower : first≤target := by
    apply ceilSqrt_le_iff.mpr
    have sq := square.1
    change target^2=24*(p*q)+_ at sq
    omega
  have allowed : admissible target := of_square unit square.1
  have odd : target%2=1 := by rcases allowed with h|h <;> omega
  constructor
  · constructor
    · rintro ⟨s,_,_,rank,hit⟩
      exact (Nat.div_le_div_right (min_label pp qp pq balanced hit)).trans_lt rank
    · exact fun rank => ⟨target,lower,odd,rank,square⟩
  · constructor
    · rintro ⟨s,_,_,rank,hit⟩
      have le : unitCount target≤unitCount s := by
        rw [←unitCount_eq,←unitCount_eq]
        exact card_le_card (filter_subset_filter _ (range_mono (min_label pp qp pq balanced hit)))
      exact le.trans_lt rank
    · exact unit_hit_at_minimum pp qp unit lower

/-- The population contains each 2048-bit input having two distinct
1024-bit prime factors once. -/
noncomputable def population : Finset ℕ :=
  MixedPrefixSample.eligible.image fun z => z.1*z.2

noncomputable def successes (hit : ℕ → ℕ → ℕ → Prop) (budget : ℕ) : Finset ℕ := by
  classical exact population.filter (fun n => hit n (ceilSqrt (24*n)) budget)

attribute [local irreducible] MixedPrefixSample.eligible MixedPrefixSample.sample
  MixedPrefixSample.ordered MixedPrefixSample.primes

theorem mem_population {n : ℕ} : n∈population ↔
    ∃ p q, 2^1023≤p ∧ p<q ∧ q<2^1024 ∧ p.Prime ∧ q.Prime ∧ 2^2047≤n ∧ p*q=n := by
  classical
  have primes {p : ℕ} : p∈MixedPrefixSample.primes ↔
      (2^1023≤p ∧ p<2^1024) ∧ p.Prime := by
    simp only [MixedPrefixSample.primes,mem_filter,mem_Ico,MixedPrefixSample.X]
    rfl
  have bit : 2*MixedPrefixSample.X^2=2^2047 := by decide +kernel
  rw [population]
  constructor
  · intro h
    obtain ⟨⟨p,q⟩,pair,eq⟩ := mem_image.mp h
    rw [MixedPrefixSample.eligible,MixedPrefixSample.sample] at pair
    obtain ⟨ord,lt⟩ := mem_filter.mp pair
    obtain ⟨lp,lq,_,big,_⟩ := MixedPrefixSample.mem_ordered.mp ord
    obtain ⟨pl,pp⟩ := primes.mp lp
    obtain ⟨qu,qp⟩ := primes.mp lq
    change p*q=n at eq
    exact ⟨p,q,pl.1,lt,qu.2,pp,qp,bit ▸ eq ▸ big,eq⟩
  · rintro ⟨p,q,pl,pq,qu,pp,qp,full,rfl⟩
    apply mem_image.mpr ⟨(p,q),?_,rfl⟩
    rw [MixedPrefixSample.eligible,MixedPrefixSample.sample]
    exact mem_filter.mpr ⟨MixedPrefixSample.mem_ordered.mpr
      ⟨primes.mpr ⟨⟨pl,pq.trans qu⟩,pp⟩,primes.mpr ⟨⟨pl.trans pq.le,qu⟩,qp⟩,
       pq.ne,bit ▸ full,trivial⟩,pq⟩

attribute [local irreducible] population successes

theorem mem_success {n budget : ℕ} {hit : ℕ → ℕ → ℕ → Prop} :
    n∈successes hit budget ↔ n∈population ∧ hit n (ceilSqrt (24*n)) budget := by
  classical rw [successes,mem_filter]

theorem population_inclusion (budget : ℕ) : successes oddHit budget ⊆ successes unitHit budget := by
  intro n h
  obtain ⟨member,hit⟩ := mem_success.mp h
  refine mem_success.mpr ⟨member,retain ?_ hit⟩
  obtain ⟨p,q,pl,pq,_,pp,qp,_,rfl⟩ := mem_population.mp member
  have cop {r : ℕ} (pr : r.Prime) (lo : 6<r) : r.Coprime 6 :=
    pr.coprime_iff_not_dvd.mpr fun d => (not_le_of_gt lo) (Nat.le_of_dvd (by decide) d)
  have large : 6<p := (show 6<2^1023 by decide +kernel).trans_le pl
  exact Nat.coprime_mul_iff_left.mpr ⟨cop pp large,cop qp (large.trans pq)⟩

/-- A single checked witness makes retention a strict inclusion on the entire
population. No statistical assumption or prime-count estimate enters. -/
theorem population_strict_at {p q budget : ℕ} (pp : p.Prime) (qp : q.Prime)
    (pl : 2^1023≤p) (pq : p<q) (qu : q<2^1024) (full : 2^2047≤p*q)
    (newHit : unitHit (p*q) (ceilSqrt (24*(p*q))) budget)
    (miss : ¬oddHit (p*q) (ceilSqrt (24*(p*q))) budget) :
    successes oddHit budget ⊂ successes unitHit budget := by
  apply (ssubset_iff_of_subset (population_inclusion budget)).mpr
  have member := mem_population.mpr ⟨p,q,pl,pq,qu,pp,qp,full,rfl⟩
  exact ⟨p*q,mem_success.mpr ⟨member,newHit⟩,fun h => miss (mem_success.mp h).2⟩

end PrimeFactors.SixTraceBudget
