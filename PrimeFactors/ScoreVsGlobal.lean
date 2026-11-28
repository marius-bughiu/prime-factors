import PrimeFactors.ScoreOrderSlowdown
import PrimeFactors.OtherSumGridPopulation

/-! Pointwise differences between two orderings of the same exhaustive
square tests. The continuous endpoints bound counts in a finite prefix. -/

namespace PrimeFactors.ScoreVsGlobal

open Finset Real FactorSumPrefixCost GlobalSumOrderCost ScoreSumOrder PeriodicSumRank
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open NormalizedSumWork (coord)
open MixedPrefixSample (eligible)
open private PrimeFactors.GlobalSumOrderCost.inGroup PrimeFactors.GlobalSumOrderCost.cover
  PrimeFactors.GlobalSumOrderCost.group_block from PrimeFactors.GlobalSumOrderCost
open private PrimeFactors.FactorSumPrefixCost.whole_blocks from PrimeFactors.FactorSumPrefixCost
open private PrimeFactors.NormalizedSumWork.floor_endpoint PrimeFactors.NormalizedSumWork.prime_nonzero
  PrimeFactors.NormalizedSumWork.target_high PrimeFactors.NormalizedSumWork.marks_opposite
  from PrimeFactors.NormalizedSumWork
open private PrimeFactors.FavoredSumWork.marks_same from PrimeFactors.FavoredSumWork
open scoped Classical

set_option exponentiation.threshold 4096
attribute [local irreducible] eligible

/-- Square tests saved by merging the two rows, relative to visiting every favored sum first. -/
noncomputable def gain (p q : ℕ) : ℝ :=
  let n := p*q
  let lo := ceilSqrt (4*n)
  let hi := ProductDeficitBand.sumCap n X
  ((globalPrefix n lo hi (p+q)).card:ℝ)-(ScoreSumOrder.prefix n lo hi (p+q)).card

/-- Inclusive number of square tests in score order at the true sum. -/
noncomputable def scored (p q : ℕ) : ℝ :=
  let n := p*q
  ((ScoreSumOrder.prefix n (ceilSqrt (4*n)) (ProductDeficitBand.sumCap n X) (p+q)).card:ℝ)

theorem gain_eq (p q : ℕ) : gain p q=NormalizedSumWork.prioritized p q-scored p q := rfl

theorem gain_zero {p q : ℕ} (h : (p,q)∈OtherSumGridPopulation.other) : gain p q=0 := by
  obtain ⟨member,ns⟩ := OtherSumGridPopulation.mem_other.mp h
  obtain ⟨pl,ord,qu,_⟩ := SumGridPopulation.eligible_data.mp member
  dsimp only [gain]
  rw [AllResidueSumCost.same_prefix ns,ScoreOrderSlowdown.nonsquare_prefix ns
    (PrimeFactors.NormalizedSumWork.target_high pl ord qu),sub_self]

private noncomputable def endpoint (c x y : ℝ) := sqrt (4*(x*y)+(c*(y-x))^2)
noncomputable def U (x y : ℝ) := endpoint (2/5) x y-2*sqrt (x*y)
noncomputable def V (x y : ℝ) := endpoint (5/2) x y-2*sqrt (x*y)
noncomputable def E (x y : ℝ) := (1-sqrt (x*y))^2

private theorem scale_endpoint (c : ℝ) (p q : ℕ) :
    (B:ℝ)*endpoint c (coord p) (coord q)=endpoint c p q := by
  have bp : (0:ℝ)<B := by norm_num [B]
  have eq : 4*(coord p*coord q)+(c*(coord q-coord p))^2 =
      (4*((p:ℝ)*q)+(c*((q:ℝ)-p))^2)/(B:ℝ)^2 := by
    unfold coord
    field_simp [bp.ne']
    ring
  rw [endpoint,eq,sqrt_div (by positivity),Real.sqrt_sq bp.le]
  field_simp [bp.ne',endpoint]

private theorem scale_root (p q : ℕ) :
    (B:ℝ)*sqrt (coord p*coord q)=sqrt (p*q:ℕ) := by
  have bp : (0:ℝ)<B := by norm_num [B]
  have eq : coord p*coord q=(p*q:ℕ)/(B:ℝ)^2 := by
    simp only [coord,div_mul_div_comm,pow_two,Nat.cast_mul]
  rw [eq,sqrt_div (by positivity),Real.sqrt_sq bp.le]
  field_simp [bp.ne']

private theorem root_le (c : ℝ) (p q : ℕ) : 2*sqrt (p*q:ℕ)≤endpoint c p q := by
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity),mul_pow,Real.sq_sqrt (by positivity),Nat.cast_mul]
  nlinarith only [sq_nonneg (c*((q:ℝ)-p))]

private theorem test_endpoint {p q t : ℕ} {c : ℝ} {a b : ℕ}
    (ap : (0:ℝ)<a) (ratio : (a:ℝ)*c^2=b) (lo : ceilSqrt (4*(p*q))≤t)
    (scores : a*(t^2-4*(p*q))≤b*((p+q)^2-4*(p*q))) :
    (t:ℝ)≤endpoint c p q := by
  have nonneg := ceilSqrt_le_iff.mp lo
  have target : 4*(p*q)≤(p+q)^2 := by
    zify
    nlinarith only [sq_nonneg ((p:ℤ)-q)]
  have cast : (a:ℝ)*((t:ℝ)^2-4*((p:ℝ)*q))≤(b:ℝ)*(((p:ℝ)+q)^2-4*((p:ℝ)*q)) := by
    have hc : ((a*(t^2-4*(p*q)):ℕ):ℝ)≤((b*((p+q)^2-4*(p*q)):ℕ):ℝ) := by exact_mod_cast scores
    simpa only [Nat.cast_mul,Nat.cast_sub nonneg,Nat.cast_sub target,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat] using hc
  have eq : (((p:ℝ)+q)^2-4*((p:ℝ)*q))=((q:ℝ)-p)^2 := by ring
  rw [eq,←ratio] at cast
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity)]
  apply (mul_le_mul_iff_of_pos_left ap).mp
  nlinarith only [cast]

private theorem card_top {n lo : ℕ} (sq : n%5=1 ∨ n%5=4) {R z : ℝ}
    (zn : 0≤z) (zr : z≤R) (inside : z≤lo) :
    let S := (Ico lo (⌊R⌋₊+1)).filter (PrimeFactors.GlobalSumOrderCost.inGroup n false)
    100*(S.card:ℝ)≤5*(R-z)+505 := by
  let w := ⌊R⌋₊+1-lo
  let k := w/100+1
  have top : ⌊R⌋₊+1≤lo+100*k := by dsimp [k,w]; omega
  have count := PrimeFactors.GlobalSumOrderCost.cover _
    (fun a => PrimeFactors.GlobalSumOrderCost.group_block sq a false) top
  let S := (Ico lo (⌊R⌋₊+1)).filter (PrimeFactors.GlobalSumOrderCost.inGroup n false)
  change S.card≤5*k at count
  have work : 100*S.card≤5*w+500 := by dsimp only [k] at count; omega
  have h : (w:ℝ)≤R-z+1 := by
    by_cases range : lo≤⌊R⌋₊+1
    · dsimp only [w]
      rw [Nat.cast_sub range,Nat.cast_add,Nat.cast_one]
      linarith only [Nat.floor_le (zn.trans zr),inside]
    · simp only [w,Nat.sub_eq_zero_of_le (not_le.mp range).le,Nat.cast_zero]
      linarith
  change 100*(S.card:ℝ)≤_
  have work' : 100*(S.card:ℝ)≤5*(w:ℝ)+500 := by exact_mod_cast work
  linarith

private theorem card_tail {n hi : ℕ} (sq : n%5=1 ∨ n%5=4) {R : ℝ} (rp : 0≤R) :
    let S := (Ico (⌊R⌋₊+1) (hi+1)).filter (PrimeFactors.GlobalSumOrderCost.inGroup n true)
    2*((hi:ℝ)-R)-200≤100*(S.card:ℝ) := by
  let start := ⌊R⌋₊+1
  let k := (hi+1-start)/100
  let S := (Ico start (hi+1)).filter (PrimeFactors.GlobalSumOrderCost.inGroup n true)
  have count : 2*k≤S.card := by
    by_cases range : start≤hi+1
    · have fit : start+100*k≤hi+1 := by dsimp [k]; omega
      have low := card_le_card (filter_subset_filter (PrimeFactors.GlobalSumOrderCost.inGroup n true)
        (Ico_subset_Ico_right (a:=start) fit))
      rwa [PrimeFactors.FactorSumPrefixCost.whole_blocks _ 2
        (fun a => PrimeFactors.GlobalSumOrderCost.group_block sq a true)] at low
    · simp only [k,Nat.sub_eq_zero_of_le (not_le.mp range).le,Nat.zero_div,mul_zero,Nat.zero_le]
  have bound : 2*hi ≤ 100*S.card+2*⌊R⌋₊+200 := by dsimp [k,start] at count; omega
  have realBound : 2*(hi:ℝ)≤100*(S.card:ℝ)+2*(⌊R⌋₊:ℝ)+200 := by exact_mod_cast bound
  change _≤100*(S.card:ℝ)
  linarith only [realBound,Nat.floor_le rp]

private theorem cap_lower_aux {a n : ℕ} (ap : 0<a) (full : 2*a*a≤n) :
    2*a+n/(2*a)≤ProductDeficitBand.sumCap n a+1 := by
  have dp : 0<2*a := by omega
  have large : a≤n/(2*a) := (Nat.le_div_iff_mul_le dp).mpr (by simpa only [Nat.mul_comm a (2*a)] using full)
  have twice : 2*(n/(2*a))≤n/a := (Nat.le_div_iff_mul_le ap).mpr (by
    calc _ = n/(2*a)*(2*a) := by ring
         _ ≤ n := Nat.div_mul_le_self ..)
  have small : n/(2*a)≤n/(2*a-1) := Nat.div_le_div_left (Nat.sub_le ..) (by omega)
  unfold ProductDeficitBand.sumCap
  omega

/-- Full product width places the cap within two integer units of the
continuous right endpoint, including both integer divisions. -/
theorem cap_lower {n : ℕ} (full : PrimeProductRegion.K≤n) :
    (B:ℝ)+(n:ℝ)/B-2≤(ProductDeficitBand.sumCap n X:ℝ) := by
  have shape : 2*X*X=PrimeProductRegion.K := by decide +kernel
  have width : 2*X=B := by decide +kernel
  have cap := cap_lower_aux (by decide : 0<X) (shape ▸ full : 2*X*X≤n)
  rw [width] at cap
  have bp : 0<B := by decide +kernel
  have floor := (Nat.div_lt_iff_lt_mul bp).mp (Nat.lt_succ_self (n/B))
  have realCap : (B:ℝ)+(n/B:ℕ)≤(ProductDeficitBand.sumCap n X:ℝ)+1 := by exact_mod_cast cap
  have realFloor : (n:ℝ)/B < (n/B:ℕ)+1 := (div_lt_iff₀ (by exact_mod_cast bp)).mpr (by exact_mod_cast floor)
  linarith only [realCap,realFloor]

private theorem regular_before_cut {p q t : ℕ} (low : ceilSqrt (4*(p*q))≤t)
    (target : favored ((p*q)%100) ((p+q)%100)=true)
    (row : favored ((p*q)%100) (t%100)=false) (ord : before (p*q) t (p+q)) :
    (t:ℝ)≤endpoint (2/5) p q := by
  have keys := key_le ord
  simp only [key,target,row,if_true,Bool.false_eq_true,if_false] at keys
  exact test_endpoint (a:=25) (b:=4) (by norm_num) (by norm_num) low keys

private theorem favored_before_cut {p q t : ℕ} (low : ceilSqrt (4*(p*q))≤t)
    (target : favored ((p*q)%100) ((p+q)%100)=false)
    (row : favored ((p*q)%100) (t%100)=true) (ord : before (p*q) t (p+q)) :
    (t:ℝ)≤endpoint (5/2) p q := by
  have keys := key_le ord
  simp only [key,target,row,if_true,Bool.false_eq_true,if_false] at keys
  exact test_endpoint (a:=4) (b:=25) (by norm_num) (by norm_num) low keys

private theorem norm_U (p q : ℕ) :
    (B:ℝ)*U (coord p) (coord q)=endpoint (2/5) p q-2*sqrt (p*q:ℕ) := by
  calc
    _ = (B:ℝ)*endpoint (2/5) (coord p) (coord q)-2*((B:ℝ)*sqrt (coord p*coord q)) := by unfold U; ring
    _ = _ := by rw [scale_endpoint,scale_root]

private theorem norm_EV (p q : ℕ) :
    (B:ℝ)*(E (coord p) (coord q)-V (coord p) (coord q))=
      (B:ℝ)+(p*q:ℕ)/B-endpoint (5/2) p q := by
  have eq : (B:ℝ)*(coord p*coord q)=(p*q:ℕ)/B := by
    simp only [coord,Nat.cast_mul]
    field_simp [show (B:ℝ)≠0 by norm_num [B]]
    ring
  calc
    _ = (B:ℝ)+(B:ℝ)*(sqrt (coord p*coord q))^2-(B:ℝ)*endpoint (5/2) (coord p) (coord q) := by unfold E V; ring
    _ = _ := by rw [Real.sq_sqrt (by unfold coord; positivity),eq,scale_endpoint]

/-- Loss relative to global favored-first when the true sum is favored.
Only ordinary tests through the smaller discriminant cutoff can contribute. -/
theorem favored_bound {p q : ℕ} (h : (p,q)∈eligible) (same : p%5=q%5) :
    -5*(B:ℝ)*U (coord p) (coord q)-2000≤100*gain p q := by
  obtain ⟨pl,_,_,pp,_⟩ := SumGridPopulation.eligible_data.mp h
  obtain ⟨sq,mark⟩ := PrimeFactors.FavoredSumWork.marks_same
    (PrimeFactors.NormalizedSumWork.prime_nonzero pl pp) same
  let n := p*q
  let s := p+q
  let lo := ceilSqrt (4*n)
  let hi := ProductDeficitBand.sumCap n X
  let R := endpoint (2/5) p q
  let G := globalPrefix n lo hi s
  let S := ScoreSumOrder.prefix n lo hi s
  let extra := (Ico lo (⌊R⌋₊+1)).filter (PrimeFactors.GlobalSumOrderCost.inGroup n false)
  have sub : S⊆G ∪ extra := by
    intro t ht
    obtain ⟨⟨lower,_⟩,pass,ahead⟩ := mem_prefix.mp ht
    cases flag : favored (n%100) (t%100)
    · have bound := regular_before_cut lower mark flag ahead
      have fit : t≤⌊R⌋₊ := Nat.le_floor bound
      exact mem_union_right _ (mem_filter.mpr ⟨mem_Ico.mpr ⟨lower,by omega⟩,pass,flag⟩)
    · have le := (same_group (flag.trans mark.symm)).mp ahead
      have base : t∈passingPrefix n lo s := mem_filter.mpr ⟨mem_Ico.mpr ⟨lower,by omega⟩,pass⟩
      apply mem_union_left
      change t∈globalPrefix n lo hi s
      rw [globalPrefix,if_pos mark]
      exact mem_filter.mpr ⟨base,flag⟩
  have count : S.card≤G.card+extra.card := (card_le_card sub).trans (card_union_le ..)
  have count' : (S.card:ℝ)≤G.card+extra.card := by exact_mod_cast count
  have top := card_top sq (by positivity : (0:ℝ)≤2*sqrt (p*q:ℕ))
    (root_le (2/5) p q) (PrimeFactors.NormalizedSumWork.floor_endpoint n)
  change 100*(extra.card:ℝ)≤5*(R-2*sqrt (p*q:ℕ))+505 at top
  change _≤100*((G.card:ℝ)-S.card)
  rw [mul_assoc,norm_U]
  change 100*(extra.card:ℝ)≤5*(endpoint (2/5) p q-2*sqrt (p*q:ℕ))+505 at top
  linarith only [top,count']

/-- Savings relative to global favored-first on an ordinary target. All
favored tests strictly beyond the larger discriminant cutoff are avoided. -/
theorem ordinary_bound {p q : ℕ} (h : (p,q)∈eligible) (opp : (p%5+q%5)%5=0) :
    0≤gain p q ∧
      2*(B:ℝ)*max 0 (E (coord p) (coord q)-V (coord p) (coord q))-2000≤100*gain p q := by
  obtain ⟨pl,pq,qu,pp,_,full⟩ := SumGridPopulation.eligible_data.mp h
  obtain ⟨sq,mark⟩ := PrimeFactors.NormalizedSumWork.marks_opposite
    (PrimeFactors.NormalizedSumWork.prime_nonzero pl pp) opp
  let n := p*q
  let s := p+q
  let lo := ceilSqrt (4*n)
  let hi := ProductDeficitBand.sumCap n X
  let R := endpoint (5/2) p q
  let G := globalPrefix n lo hi s
  let S := ScoreSumOrder.prefix n lo hi s
  let tail := (Ico (⌊R⌋₊+1) (hi+1)).filter (PrimeFactors.GlobalSumOrderCost.inGroup n true)
  have low : lo≤s := ceilSqrt_le_iff.mpr (by dsimp [n,s]; zify; nlinarith only [sq_nonneg ((p:ℤ)-q)])
  have upper : s≤hi := PrimeFactors.NormalizedSumWork.target_high pl pq qu
  have reach : (s:ℝ)≤R := test_endpoint (a:=4) (b:=25) (by norm_num) (by norm_num) low
    (Nat.mul_le_mul_right _ (by decide : 4≤25))
  have sub : S⊆G := by
    intro t ht
    obtain ⟨⟨left,right⟩,pass,ahead⟩ := mem_prefix.mp ht
    change t∈globalPrefix n lo hi s
    rw [regular_phase low upper mark]
    cases flag : favored (n%100) (t%100)
    · have le := (same_group (flag.trans mark.symm)).mp ahead
      exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ico.mpr ⟨left,by omega⟩,pass⟩,flag⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ico.mpr ⟨left,by omega⟩,pass⟩,flag⟩)
  have beyond {t : ℕ} (ht : t∈tail) : R<(t:ℝ) ∧ t≤hi ∧
      passes (n%100) (t%100)=true ∧ favored (n%100) (t%100)=true := by
    obtain ⟨bounds,tests⟩ := mem_filter.mp ht
    obtain ⟨l,u⟩ := mem_Ico.mp bounds
    have lower : (⌊R⌋₊:ℝ)+1≤t := by exact_mod_cast l
    exact ⟨(Nat.lt_floor_add_one R).trans_le lower,by omega,tests⟩
  have tail_sub : tail⊆G := by
    intro t ht
    obtain ⟨strict,cap,pass,fav⟩ := beyond ht
    have past : s<t := by exact_mod_cast reach.trans_lt strict
    change t∈globalPrefix n lo hi s
    change favored (n%100) (s%100)=false at mark
    rw [globalPrefix,mark,if_neg (by decide)]
    exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ico.mpr ⟨past,by omega⟩,pass⟩,fav⟩)
  have dis : Disjoint S tail := by
    apply disjoint_left.mpr
    intro t hs ht
    obtain ⟨⟨left,_⟩,_,ahead⟩ := mem_prefix.mp hs
    obtain ⟨strict,_,_,fav⟩ := beyond ht
    exact (not_le_of_gt strict) (favored_before_cut left mark fav ahead)
  have count := card_le_card (union_subset sub tail_sub)
  rw [card_union_of_disjoint dis] at count
  have count' : (S.card:ℝ)+tail.card≤G.card := by exact_mod_cast count
  have zero : 0≤gain p q := by
    change 0≤(G.card:ℝ)-S.card
    linarith only [count',Nat.cast_nonneg tail.card (α:=ℝ)]
  refine ⟨zero,?_⟩
  cases max_cases 0 (E (coord p) (coord q)-V (coord p) (coord q)) with
  | inl he => rw [he.1]; linarith
  | inr he =>
    rw [he.1]
    have tailBound := card_tail (hi:=hi) sq (show 0≤R from Real.sqrt_nonneg _)
    change 2*((hi:ℝ)-R)-200≤100*(tail.card:ℝ) at tailBound
    change _≤100*((G.card:ℝ)-S.card)
    have cap := cap_lower full
    change (B:ℝ)+(p*q:ℕ)/B-2≤(hi:ℝ) at cap
    rw [mul_assoc,norm_EV]
    change 2*((hi:ℝ)-endpoint (5/2) p q)-200≤100*(tail.card:ℝ) at tailBound
    linarith only [count',tailBound,cap]

end PrimeFactors.ScoreVsGlobal
