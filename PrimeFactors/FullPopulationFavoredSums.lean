import PrimeFactors.FullRangeLongSumPrefix
import PrimeFactors.MixedPrefixSample

/-! Frequency of equal factor remainders modulo five in the entire population
of distinct 1,024-bit prime pairs with 2,048-bit product. -/

namespace PrimeFactors.FullPopulationFavoredSums

open Finset FullRangeResidueEstimates PrimeProductRegion
open WideResiduePrimeSupply (B)
open MixedPrefixSample (eligible)

open private PrimeFactors.PrimeProductRegion.whole PrimeFactors.PrimeProductRegion.pool
  PrimeFactors.PrimeProductRegion.mem_whole PrimeFactors.PrimeProductRegion.mem_pool
  PrimeFactors.PrimeProductRegion.residues PrimeFactors.PrimeProductRegion.fiber
  from PrimeFactors.PrimeProductRegion
open private PrimeFactors.MixedPrefixSample.mem_primes PrimeFactors.MixedPrefixSample.mem_sample
  from PrimeFactors.MixedPrefixSample

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

noncomputable def favoredPairs := eligible.filter fun v => v.1%5=v.2%5

/-- Both conditions on the target sum are imposed on the uniform unordered population. -/
noncomputable def longFavored := favoredPairs.filter fun v => ceilSqrt (4*(v.1*v.2))+2^900≤v.1+v.2

attribute [local irreducible] PrimeFactors.PrimeProductRegion.whole PrimeFactors.PrimeProductRegion.pool
  eligible MixedPrefixSample.primes MixedPrefixSample.ordered favoredPairs longFavored cell

private theorem mem_eligible {p q : ℕ} : (p,q)∈eligible ↔
    X≤p ∧ p<q ∧ q<B ∧ p.Prime ∧ q.Prime ∧ K≤p*q := by
  have hi : 2*MixedPrefixSample.X=B := by decide +kernel
  have size : 2*MixedPrefixSample.X^2=K := by decide +kernel
  simp only [MixedPrefixSample.eligible,PrimeFactors.MixedPrefixSample.mem_sample,
    MixedPrefixSample.mem_ordered,PrimeFactors.MixedPrefixSample.mem_primes,
    and_true]
  constructor
  · rintro ⟨⟨⟨⟨ppLo,_⟩,pp⟩,⟨⟨_,qqHi⟩,qp⟩,_,prod⟩,lt⟩
    exact ⟨ppLo,lt,hi ▸ qqHi,pp,qp,size ▸ prod⟩
  · rintro ⟨lo,lt,upper,pp,qp,prod⟩
    exact ⟨⟨⟨⟨lo,hi ▸ lt.trans upper⟩,pp⟩,⟨⟨lo.trans lt.le,hi ▸ upper⟩,qp⟩,
      lt.ne,size ▸ prod⟩,lt⟩

theorem mem_longFavored {p q : ℕ} : (p,q)∈longFavored ↔ X≤p ∧ p<q ∧ q<B ∧
    p.Prime ∧ q.Prime ∧ K≤p*q ∧ p%5=q%5 ∧ ceilSqrt (4*(p*q))+2^900≤p+q := by
  simp only [longFavored,favoredPairs,mem_filter,mem_eligible,and_assoc]

private abbrev Label := ZMod 25 × ZMod 25

private noncomputable def unitCells : Finset Label :=
  univ.filter fun v => v.1.val.Coprime 25 ∧ v.2.val.Coprime 25

private noncomputable def sameCells := unitCells.filter fun v => v.1.val%5=v.2.val%5

private theorem cell_counts : sameCells.card=100 ∧ unitCells.card=400 := by decide +kernel


private theorem units {v : Label} (ok : v∈unitCells) : IsUnit v.1 ∧ IsUnit v.2 := by
  have lift (a : ZMod 25) (h : a.val.Coprime 25) : IsUnit a := by
    simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime a.val 25).mpr h
  obtain ⟨a,b⟩ := (mem_filter.mp ok).2
  exact ⟨lift _ a,lift _ b⟩

private theorem prime_unit {p : ℕ} (lo : X<p) (pp : p.Prime) : (p%25).Coprime 25 := by
  rw [Nat.coprime_iff_gcd_eq_one,←Nat.gcd_rec,Nat.gcd_comm,←Nat.coprime_iff_gcd_eq_one]
  exact pp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) ((by decide : 25≤X).trans_lt lo))

private theorem pool_unit {p : ℕ} (hp : p∈PrimeFactors.PrimeProductRegion.pool) :
    (p%25).Coprime 25 := by
  obtain ⟨lo,_,pp⟩ := PrimeFactors.PrimeProductRegion.mem_pool.mp hp
  exact prime_unit lo pp

private theorem whole_marks {p q : ℕ} (hpq : (p,q)∈PrimeFactors.PrimeProductRegion.whole) :
    PrimeFactors.PrimeProductRegion.residues (p,q)∈unitCells := by
  obtain ⟨hp,hq,_⟩ := PrimeFactors.PrimeProductRegion.mem_whole.mp hpq
  exact mem_filter.mpr ⟨mem_univ _,by simpa only [PrimeFactors.PrimeProductRegion.residues,
    ZMod.val_natCast] using (And.intro (pool_unit hp) (pool_unit hq))⟩

/-- Endpoint powers of two and the product threshold itself are composite. -/
private theorem whole_sorted {p q : ℕ} (order : p<q) :
    (p,q)∈PrimeFactors.PrimeProductRegion.whole ↔ (p,q)∈eligible := by
  rw [PrimeFactors.PrimeProductRegion.mem_whole,PrimeFactors.PrimeProductRegion.mem_pool,
    PrimeFactors.PrimeProductRegion.mem_pool,mem_eligible]
  constructor
  · rintro ⟨⟨lo,_,pp⟩,⟨_,hi,qp⟩,size,_⟩
    have ne : q≠B := fun eq => (Nat.Prime.not_prime_pow (by decide : 2≤1024) (x:=2))
      ((congrArg Nat.Prime eq).mp qp)
    exact ⟨lo.le,order,hi.lt_of_ne ne,pp,qp,size.le⟩
  · rintro ⟨lo,_,hi,pp,qp,size⟩
    have ne : X≠p := fun eq => (Nat.Prime.not_prime_pow (by decide : 2≤1023) (x:=2))
      ((congrArg Nat.Prime eq).mpr pp)
    have oddp := pp.odd_of_ne_two ((by decide : 2<X).trans_le lo).ne'
    have oddq := qp.odd_of_ne_two (((by decide : 2<X).trans_le lo).trans order).ne'
    have threshold : K≠p*q := fun eq => (by decide : K%2≠1) (eq ▸ Nat.odd_iff.mp (oddp.mul oddq))
    exact ⟨⟨lo.lt_of_ne ne,(order.trans hi).le,pp⟩,⟨(lo.trans_lt order),hi.le,qp⟩,
      size.lt_of_ne threshold,order.ne⟩

private theorem flip {p q : ℕ} (h : (p,q)∈PrimeFactors.PrimeProductRegion.whole) :
    (q,p)∈PrimeFactors.PrimeProductRegion.whole := by
  obtain ⟨hp,hq,size,ne⟩ := PrimeFactors.PrimeProductRegion.mem_whole.mp h
  exact PrimeFactors.PrimeProductRegion.mem_whole.mpr ⟨hq,hp,by rwa [Nat.mul_comm q p],ne.symm⟩

private theorem ordered_card (f : ℕ×ℕ → Prop) [DecidablePred f]
    (sym : ∀ p q, f (p,q) → f (q,p)) :
    (PrimeFactors.PrimeProductRegion.whole.filter f).card=2*(eligible.filter f).card := by
  classical
  let S := PrimeFactors.PrimeProductRegion.whole.filter f
  let small (v : ℕ×ℕ) := v.1<v.2
  have reversed {p q} (h : (p,q)∈S) : (q,p)∈S :=
    mem_filter.mpr ⟨flip (mem_filter.mp h).1,sym _ _ (mem_filter.mp h).2⟩
  have sides : (S.filter small).card=(S.filter fun v => ¬small v).card := by
    apply card_nbij' Prod.swap Prod.swap
    · rintro ⟨p,q⟩ hv
      obtain ⟨inS,lt⟩ := mem_filter.mp hv
      exact mem_filter.mpr ⟨reversed inS,not_lt_of_ge (le_of_lt lt)⟩
    · rintro ⟨p,q⟩ hv
      obtain ⟨inS,nlt⟩ := mem_filter.mp hv
      have ne := (PrimeFactors.PrimeProductRegion.mem_whole.mp (mem_filter.mp inS).1).2.2.2
      exact mem_filter.mpr ⟨reversed inS,lt_of_le_of_ne (le_of_not_gt nlt) ne.symm⟩
    all_goals intro _ _; rfl
  have canon : S.filter small = eligible.filter f := by
    ext ⟨p,q⟩
    simp only [S,small,mem_filter]
    constructor
    · rintro ⟨⟨inW,pass⟩,lt⟩
      exact ⟨(whole_sorted lt).mp inW,pass⟩
    · rintro ⟨ok,pass⟩
      have lt := (mem_eligible.mp ok).2.1
      exact ⟨⟨(whole_sorted lt).mpr ok,pass⟩,lt⟩
  have part := filter_card_add_filter_neg_card_eq_card (s:=S) small
  change S.card=2*(eligible.filter f).card
  rw [←sides,canon] at part
  omega

private theorem cell_sum (T : Finset Label) :
    (PrimeFactors.PrimeProductRegion.whole.filter (fun v => PrimeFactors.PrimeProductRegion.residues v∈T)).card =
      ∑ w∈T,cell w :=
  (sum_card_fiberwise_eq_card_filter _ _ _).symm.trans
    (sum_congr rfl fun w _ => PrimeFactors.PrimeProductRegion.fiber w)

private theorem totals :
    2*eligible.card = ∑ w∈unitCells,cell w ∧ 2*favoredPairs.card = ∑ w∈sameCells,cell w := by
  have all : PrimeFactors.PrimeProductRegion.whole.filter
      (fun v => PrimeFactors.PrimeProductRegion.residues v∈unitCells)=PrimeFactors.PrimeProductRegion.whole :=
    filter_eq_self.mpr (fun _ h => whole_marks h)
  have selected : PrimeFactors.PrimeProductRegion.whole.filter
      (fun v => PrimeFactors.PrimeProductRegion.residues v∈sameCells) =
      PrimeFactors.PrimeProductRegion.whole.filter (fun v => v.1%5=v.2%5) := by
    ext ⟨p,q⟩
    simp only [sameCells,mem_filter]
    apply and_congr_right
    intro inW
    rw [and_iff_right (whole_marks inW)]
    simp only [PrimeFactors.PrimeProductRegion.residues,ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 5∣25)]
  have wholeCount := ordered_card (fun _ => True) (fun _ _ h => h)
  simp only [filter_True] at wholeCount
  refine ⟨wholeCount ▸ all ▸ cell_sum unitCells,?_⟩
  rw [favoredPairs,←ordered_card _ (fun _ _ h => h.symm),←selected]
  exact cell_sum _

/-- The total and favored counts here include all unit products. -/
private theorem comparison {D upper floor : ℕ} (h : Estimates D upper floor) :
    eligible.card ≤ 4*favoredPairs.card + 200*(2*D*upper+upper) ∧
    200*(floor*(floor-1)) ≤ eligible.card := by
  let δ := 2*D*upper+upper
  have row (v : Label) (hv : v∈unitCells) :
      100*cell v ≤ (∑ w∈sameCells,cell w)+100*δ := by
    have u := units hv
    have sums := sum_le_sum (s:=sameCells) (fun w hw => cell_spread h u.1 u.2
      (units (mem_filter.mp hw).1).1 (units (mem_filter.mp hw).1).2)
    simpa only [sum_const,smul_eq_mul,sum_add_distrib,cell_counts.1,δ] using sums
  have both := sum_le_sum row
  rw [←mul_sum,sum_const,smul_eq_mul,cell_counts.2,←totals.1,←totals.2] at both
  have low := sum_le_sum (s:=unitCells) (fun v hv => cell_lower h (units hv).1 (units hv).2)
  rw [sum_const,smul_eq_mul,cell_counts.2,←totals.1] at low
  dsimp only [δ] at both
  have arithmetic {t g d m : ℕ} (h₁ : 100*(2*t)≤400*(2*g+100*d))
      (h₂ : 400*m≤2*t) : t≤4*g+200*d ∧ 200*m≤t := by omega
  exact arithmetic both low

private theorem count_short :
    favoredPairs.card ≤ longFavored.card+2^1986 := by
  let long (v : ℕ×ℕ) := ceilSqrt (4*(v.1*v.2))+2^900≤v.1+v.2
  let short := favoredPairs.filter (fun v => ¬long v)
  have bound : short.card≤2^1986 := by
    apply FullRangeLongSumPrefix.wide_short_bound
    rintro ⟨p,q⟩ inS
    obtain ⟨member,fail⟩ := mem_filter.mp inS
    have eligiblePair := (mem_filter.mp (by simpa only [favoredPairs] using member)).1
    obtain ⟨lo,order,hi,_⟩ := mem_eligible.mp eligiblePair
    exact ⟨lo,order,hi,lt_of_not_ge fail⟩
  have split := filter_card_add_filter_neg_card_eq_card (s:=favoredPairs) long
  rw [show favoredPairs.filter long=longFavored by rw [longFavored]] at split
  exact split ▸ Nat.add_le_add_left bound _

/-- With the published unconditional prime-count input, more than 24.9% of
all eligible distinct prime pairs satisfy both the residue and distance tests. -/
theorem bmor_card {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) :
    249*eligible.card < 1000*longFavored.card := by
  obtain ⟨spread,lower⟩ := comparison (bmor h)
  have thin : 10000*(2^1986)<eligible.card :=
    (by decide +kernel : 10000*(2^1986)<200*(M*(M-1))).trans_le lower
  have arithmetic {t g l s d m : ℕ} (ratio : t≤4*g+200*d) (total : 200*m≤t)
      (budget : 412*d≤m) (lost : g≤l+s) (small : 10000*s<t) :
      249*t<1000*l := by omega
  exact arithmetic spread lower bmor_precision count_short thin

/-- Share when sampling all eligible unordered pairs uniformly. -/
theorem bmor_share {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) :
    249/1000 < (longFavored.card:ℚ)/eligible.card := by
  have positive := (by decide +kernel : 0<200*(M*(M-1))).trans_le (comparison (bmor h)).2
  apply (div_lt_div_iff₀ (by norm_num) (Nat.cast_pos.mpr positive)).mpr
  exact_mod_cast (show 249*eligible.card < longFavored.card*1000 by
    simpa only [Nat.mul_comm longFavored.card 1000] using bmor_card h)

end PrimeFactors.FullPopulationFavoredSums
