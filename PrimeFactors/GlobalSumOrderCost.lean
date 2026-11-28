import PrimeFactors.FactorSumPrefixCost

/-! Signed square-test counts for the ascending and global favored-first
traversals of one public sum interval. Both traversals include the
successful target in their prefix. -/

open private PrimeFactors.FactorSumPrefixCost.whole_blocks
  PrimeFactors.FactorSumPrefixCost.square_digit from PrimeFactors.FactorSumPrefixCost
open private PrimeFactors.ProductDeficitBand.endpoint_step
  PrimeFactors.ProductDeficitBand.left_cap from PrimeFactors.ProductDeficitBand

namespace PrimeFactors.GlobalSumOrderCost

open Finset PeriodicSumRank FactorSumPrefixCost
open scoped Classical

/-- Ascending tests through s on the preferred branch. On the other branch
the traversal also checks every favored candidate strictly after s. -/
noncomputable def globalPrefix (n lo hi s : ℕ) : Finset ℕ :=
  if favored (n%100) (s%100) then favoredPrefix n lo s
  else passingPrefix n lo s ∪ favoredPrefix n (s+1) hi

/-- Positive values save square tests. Negative values pay extra tests. -/
noncomputable def saving (n lo hi s : ℕ) : ℤ :=
  ((passingPrefix n lo s).card : ℤ)-(globalPrefix n lo hi s).card

private abbrev inGroup (n : ℕ) (f : Bool) (x : ℕ) : Prop :=
  passes (n%100) (x%100)=true ∧ favored (n%100) (x%100)=f

noncomputable def regularBefore (n lo s : ℕ) : Finset ℕ :=
  (Ico lo s).filter (inGroup n false)

/-- The global traversal of an ordinary target first exhausts every favored
candidate in the interval, then visits ordinary candidates in ascending order. -/
theorem regular_phase {n lo hi s : ℕ} (lower : lo≤s) (upper : s≤hi)
    (mark : favored (n%100) (s%100)=false) :
    globalPrefix n lo hi s = favoredPrefix n lo hi ∪
      ((passingPrefix n lo s).filter fun x => favored (n%100) (x%100)=false) := by
  ext x
  cases flag : favored (n%100) (x%100) <;> cases ok : passes (n%100) (x%100) <;>
    simp [globalPrefix,mark,favoredPrefix,passingPrefix,flag,ok]
  omega

/-- A favored target saves precisely the ordinary candidates strictly before it. -/
theorem favored_exact {n lo hi s : ℕ} (mark : favored (n%100) (s%100)=true) :
    saving n lo hi s = (regularBefore n lo s).card := by
  let S := passingPrefix n lo s
  let F (x : ℕ) := favored (n%100) (x%100)=true
  have split := filter_card_add_filter_neg_card_eq_card (s:=S) F
  have yes : S.filter F=favoredPrefix n lo s := rfl
  have no : S.filter (fun x => ¬F x)=regularBefore n lo s := by
    ext x
    simp only [S,F,passingPrefix,regularBefore,inGroup,mem_filter,mem_Ico,Bool.not_eq_true]
    have ne (fail : favored (n%100) (x%100)=false) : x≠s := by
      intro eq
      rw [eq,mark] at fail
      contradiction
    constructor
    · rintro ⟨⟨⟨left,right⟩,pass⟩,fail⟩
      exact ⟨⟨left,by have := ne fail; omega⟩,pass,fail⟩
    · rintro ⟨⟨left,right⟩,pass,fail⟩
      exact ⟨⟨⟨left,by omega⟩,pass⟩,fail⟩
  rw [yes,no] at split
  unfold saving globalPrefix
  rw [if_pos mark]
  change (S.card : ℤ)-_ = _
  omega

/-- An ordinary target pays precisely the favored candidates strictly after
it, including the upper endpoint when that endpoint passes and is favored. -/
theorem ordinary_exact {n lo hi s : ℕ} (mark : favored (n%100) (s%100)=false) :
    saving n lo hi s = -((favoredPrefix n (s+1) hi).card : ℤ) := by
  have dis : Disjoint (passingPrefix n lo s) (favoredPrefix n (s+1) hi) := by
    apply disjoint_left.mpr
    intro x left right
    have u := (mem_Ico.mp (mem_filter.mp left).1).2
    have l := (mem_Ico.mp (mem_filter.mp (mem_filter.mp right).1).1).1
    omega
  simp only [saving,globalPrefix,mark,Bool.false_eq_true,if_false,card_union_of_disjoint dis,
    Nat.cast_add]
  omega

private theorem group_block {n : ℕ} (sq : n%5=1 ∨ n%5=4) (a : ℕ) (f : Bool) :
    ((Ico a (a+100)).filter (inGroup n f)).card = if f then 2 else 5 := by
  have sizes := row_sizes ⟨n%100,Nat.mod_lt _ (by decide)⟩
    (PrimeFactors.FactorSumPrefixCost.square_digit sq)
  have size : (row (n%100) f).card = if f then 2 else 5 := by
    cases f <;> first | exact sizes.2 | exact sizes.1
  simpa only [window,show a+99+1=a+100 by omega,min_self,filter_filter,inGroup] using
    (complete_group (r:=n%100) a f).trans size

private theorem count_block {n : ℕ} (sq : n%5=1 ∨ n%5=4) (a : ℕ) :
    ((Ico a (a+100)).filter fun x => passes (n%100) (x%100)=true).card=7 := by
  simpa only [window,show a+99+1=a+100 by omega,min_self] using
    complete_count (Nat.mod_lt n (by decide)) (PrimeFactors.FactorSumPrefixCost.square_digit sq) a

private theorem cover (P : ℕ → Prop) [DecidablePred P] {c a b k : ℕ}
    (full : ∀ z, ((Ico z (z+100)).filter P).card=c) (top : b≤a+100*k) :
    ((Ico a b).filter P).card≤c*k :=
  (card_le_card (filter_subset_filter P (Ico_subset_Ico_right top))).trans_eq
    (PrimeFactors.FactorSumPrefixCost.whole_blocks P c full a k)

theorem favored_lower {n lo hi s : ℕ} (sq : n%5=1 ∨ n%5=4) (lower : lo≤s)
    (mark : favored (n%100) (s%100)=true) :
    5*((s-lo : ℕ):ℤ)-500 ≤ 100*saving n lo hi s := by
  rw [favored_exact mark]
  let k := (s-lo)/100
  have inside : lo+100*k≤s := by dsimp [k]; omega
  have small := card_le_card (filter_subset_filter (inGroup n false) (Ico_subset_Ico_right (a:=lo) inside))
  rw [PrimeFactors.FactorSumPrefixCost.whole_blocks _ 5 (fun a => group_block sq a false)] at small
  change 5*k≤(regularBefore n lo s).card at small
  dsimp only [k] at small
  omega

theorem ordinary_lower {n lo hi s : ℕ} (sq : n%5=1 ∨ n%5=4) (upper : s≤hi)
    (mark : favored (n%100) (s%100)=false) :
    -(2*((hi-s : ℕ):ℤ))-200 ≤ 100*saving n lo hi s := by
  rw [ordinary_exact mark]
  let k := (hi-s)/100+1
  have top : hi+1≤(s+1)+100*k := by dsimp [k]; omega
  have bound := cover (inGroup n true) (c:=2) (fun a => group_block sq a true) top
  have eq : favoredPrefix n (s+1) hi=(Ico (s+1) (hi+1)).filter (inGroup n true) := by
    simp only [favoredPrefix,passingPrefix,filter_filter,inGroup]
  rw [←eq] at bound
  dsimp only [k] at bound
  omega

theorem ascending_upper {n lo s : ℕ} (sq : n%5=1 ∨ n%5=4) (lower : lo≤s) :
    100*(passingPrefix n lo s).card ≤ 7*(s-lo)+700 := by
  let k := (s-lo)/100+1
  have top : s+1≤lo+100*k := by dsimp [k]; omega
  have count := cover _ (count_block sq) top
  change (passingPrefix n lo s).card≤7*k at count
  dsimp only [k] at count
  omega

/-- Both actual traversals' square tests contain the true sum and have no
earlier success, whether its residue is favored or ordinary. -/
theorem semiprime_unique {p q A : ℕ} (size : 3≤A) (pl : A≤p) (pq : p<q) (qu : q<2*A)
    (pp : p.Prime) (qp : q.Prime) :
    let n := p*q
    let s := p+q
    let lo := ceilSqrt (4*n)
    let hi := ProductDeficitBand.sumCap n A
    (passingPrefix n lo s).filter (fun t => IsSquare (t^2-4*n)) = {s} ∧
    (globalPrefix n lo hi s).filter (fun t => IsSquare (t^2-4*n)) = {s} := by
  dsimp only
  let n := p*q
  let s := p+q
  let lo := ceilSqrt (4*n)
  let hi := ProductDeficitBand.sumCap n A
  have low : lo≤s := ceilSqrt_le_iff.mpr (balanced_factorSum_bounds pq.le (by omega : q≤2*p)).1
  have high : s≤hi := le_min (PrimeFactors.ProductDeficitBand.left_cap (by omega) pl (pl.trans pq.le))
    (CenteredSumQuartic.sum_upper rfl (by omega) (by omega) (by omega))
  have parity := SumIntervalExclusion.sum_congruence (Nat.odd_iff.mp
    ((pp.odd_of_ne_two (by omega)).mul (qp.odd_of_ne_two (by omega))))
  have pass : passes (n%100) (s%100)=true := (passes_iff n s).mpr
    ⟨parity,admissibleSum_of_factor_pair 25 rfl⟩
  have base : s∈passingPrefix n lo s := mem_filter.mpr ⟨mem_Ico.mpr ⟨low,by omega⟩,pass⟩
  have target : s∈globalPrefix n lo hi s := by
    unfold globalPrefix
    split_ifs with f
    · exact mem_filter.mpr ⟨base,f⟩
    · exact mem_union_left _ base
  have inside (P : Finset ℕ) (hit : s∈P)
      (data : ∀ t∈P, lo≤t ∧ t≤hi ∧ passes (n%100) (t%100)=true) :
      P.filter (fun t => IsSquare (t^2-4*n)) = {s} := by
    ext t
    simp only [mem_filter,mem_singleton]
    constructor
    · rintro ⟨mem,square⟩
      obtain ⟨l,u,ok⟩ := data t mem
      exact (pass_square_iff (by omega : 2≤A) pl pq.le pp qp l u ok).mp square
    · rintro rfl
      exact ⟨hit,(pass_square_iff (by omega : 2≤A) pl pq.le pp qp low high pass).mpr rfl⟩
  have data (t : ℕ) (ok : t∈passingPrefix n lo s) : lo≤t ∧ t≤hi ∧ passes (n%100) (t%100)=true := by
    obtain ⟨range,test⟩ := mem_filter.mp ok
    obtain ⟨l,u⟩ := mem_Ico.mp range
    exact ⟨l,by omega,test⟩
  refine ⟨inside _ base data,inside _ target ?_⟩
  intro t ok
  unfold globalPrefix at ok
  split_ifs at ok with flag
  · exact data _ (mem_filter.mp ok).1
  · rcases mem_union.mp ok with before|after
    · exact data _ before
    · obtain ⟨range,test⟩ := mem_filter.mp (mem_filter.mp after).1
      obtain ⟨l,u⟩ := mem_Ico.mp range
      change s+1≤t at l
      change t<hi+1 at u
      exact ⟨by omega,by omega,test⟩

/-- Real bounds at the endpoints of the advertised balanced-width interval. -/
theorem hi_upper {n A : ℕ} (pos : 0<A) (size : n≤(2*A-1)^2) :
    (ProductDeficitBand.sumCap n A:ℝ)≤2*(A:ℝ)+(n:ℝ)/(2*(A:ℝ)) := by
  have bpos : 0<2*A-1 := by omega
  have step := PrimeFactors.ProductDeficitBand.endpoint_step bpos
    (show n≤(2*A-1)*(2*A-1) by simpa only [pow_two] using size)
  rw [Nat.sub_add_cancel (by omega : 1≤2*A)] at step
  have natBound : ProductDeficitBand.sumCap n A≤2*A+n/(2*A) :=
    (min_le_right ..).trans step
  have realBound : (ProductDeficitBand.sumCap n A:ℝ) ≤
      2*(A:ℝ)+((n/(2*A):ℕ):ℝ) := by exact_mod_cast natBound
  exact realBound.trans (add_le_add_left (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using
    (Nat.cast_div_le (m:=n) (n:=2*A) (α:=ℝ))) _)

theorem lo_upper (n : ℕ) : (ceilSqrt (4*n):ℝ)≤2*Real.sqrt n+1 := by
  let f := (4*n).sqrt
  have low : (f:ℝ)^2≤4*(n:ℝ) := by exact_mod_cast (Nat.sqrt_le' (4*n))
  have pos := Real.sq_sqrt (Nat.cast_nonneg n : 0≤(n:ℝ))
  have bound : (f:ℝ)≤2*Real.sqrt n :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp (by nlinarith only [low,pos])
  have top := ceilSqrt_le_iff.mpr (Nat.lt_succ_sqrt' (4*n)).le
  have cap : (ceilSqrt (4*n):ℝ)≤(f:ℝ)+1 := by exact_mod_cast top
  linarith

end PrimeFactors.GlobalSumOrderCost
