import PrimeFactors.HighWordSuffixRanking
import PrimeFactors.GeometricWheelBlocks
import Mathlib.Data.Nat.Size

/-! # Certifying an integer-pair ranking using fractional square-root tables

Only the word, remainder, factor width, and lookup precision enter the row counts.
Intervals are inclusive and tie-breaking uses the earliest positive maximum.
-/
namespace PrimeFactors.FractionalWordRanking
open Finset HighWordSumRanking HighWordSuffixRanking

private theorem lower_sqrt {x d n : ℕ} (dp : 0<d) (sq : x^2≤n*d^2) :
    x/d≤n.sqrt := by
  have h := Nat.pow_le_pow_left (Nat.div_mul_le_self x d) 2
  rw [mul_pow] at h
  apply Nat.le_sqrt'.mpr
  exact Nat.le_of_mul_le_mul_right (h.trans sq) (pow_pos dp 2)

private theorem upper_sqrt {x d n : ℕ} (dp : 0<d) (sq : n*d^2<x^2) :
    n.sqrt≤(x-1)/d := by
  have h := Nat.mul_le_mul_right (d^2) (Nat.sqrt_le' n)
  have s : (n.sqrt*d)^2<x^2 := by rw [mul_pow]; exact h.trans_lt sq
  have lt := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp s
  exact (Nat.le_div_iff_mul_le dp).mpr (by omega)

/-- t is a stored floor of D sqrt(a) and c is a stored ceiling of D sqrt(a+1).
Only the indicated sides of the entry certificates are needed for validity. -/
theorem lookup {n h D a t c : ℕ} (hp : 0<h) (dp : 0<D) (index : a=n/h^2)
    (atLower : t^2≤D^2*a) (atUpper : D^2*(a+1)≤c^2) :
    h*t/D≤n.sqrt ∧ n.sqrt≤(h*c-1)/D := by
  have inside : h^2*a≤n := by rw [index]; apply Nat.mul_div_le
  have past : n<h^2*(a+1) := by
    rw [index]
    exact Nat.lt_mul_div_succ n (pow_pos hp _)
  constructor
  · apply lower_sqrt dp
    calc (h*t)^2 = h^2*t^2 := mul_pow ..
         _ ≤ h^2*(D^2*a) := Nat.mul_le_mul_left _ atLower
         _ = (h^2*a)*D^2 := by ring
         _ ≤ n*D^2 := Nat.mul_le_mul_right _ inside
  · apply upper_sqrt dp
    calc n*D^2 < (h^2*(a+1))*D^2 := Nat.mul_lt_mul_of_pos_right past (pow_pos dp _)
         _ = h^2*(D^2*(a+1)) := by ring
         _ ≤ h^2*c^2 := Nat.mul_le_mul_left _ atUpper
         _ = (h*c)^2 := (mul_pow ..).symm

/-- The table builder can obtain an exact ceiling using just its floor entry and
a square comparison, including at square boundaries. -/
theorem ceil_from_floor (z : ℕ) :
    (if z.sqrt^2=z then z.sqrt else z.sqrt+1)=ceilSqrt z := by
  have lower := Nat.sqrt_le' z
  have upper := Nat.lt_succ_sqrt' z
  have cLow : z≤(ceilSqrt z)^2 := ceilSqrt_le_iff.mp le_rfl
  split_ifs with exactRoot
  · have left : z.sqrt≤ceilSqrt z := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (by omega)
    exact le_antisymm left (ceilSqrt_le_iff.mpr exactRoot.ge)
  · have left : z.sqrt<ceilSqrt z := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp (by omega)
    exact le_antisymm left (ceilSqrt_le_iff.mpr upper.le)

/-- Number of low pairs of bits removed to fit the table index. -/
noncomputable def shift (k n : ℕ) := (n.size+1-k)/2

noncomputable def index (k n : ℕ) := n/(2^(shift k n))^2

theorem index_lt (k n : ℕ) : index k n<2^k := by
  unfold index
  apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
  rw [←pow_mul,←pow_add]
  apply (Nat.lt_size_self n).trans_le
  apply Nat.pow_le_pow_right (by decide)
  unfold shift
  omega

/-- Floor and ceiling entries are computed once for each leading index. -/
noncomputable def floorEntry (f a : ℕ) := (((2^f)^2)*a).sqrt
noncomputable def ceilEntry (f a : ℕ) :=
  let t := floorEntry f a
  if t^2=(2^f)^2*a then t else t+1

/-- The exact integer code can substitute bit shifts for these power-of-two
multiplications and divisions. The s=0 branch reads only the floor entry. -/
noncomputable def readBracket (k f n : ℕ) (floors ceilings : ℕ → ℕ) : ℕ×ℕ :=
  let s := shift k n
  let a := index k n
  let lower := (2^s)*floors a/2^f
  if s=0 then (lower,lower) else (lower,((2^s)*ceilings (a+1)-1)/2^f)

noncomputable def bracket (k f n : ℕ) := readBracket k f n (floorEntry f) (ceilEntry f)

/-- The extra table entry at index 2^k accommodates a+1 in the last cell. -/
theorem checked_table (k f n : ℕ) (floors ceilings : ℕ → ℕ)
    (table : ∀ a≤2^k, floors a=floorEntry f a ∧ ceilings a=ceilEntry f a) :
    readBracket k f n floors ceilings=bracket k f n := by
  have fit := index_lt k n
  dsimp only [bracket,readBracket]
  rw [(table _ fit.le).1,(table _ (show index k n+1≤2^k by omega)).2]

private theorem unshifted (n : ℕ) {D : ℕ} (dp : 0<D) :
    (D^2*n).sqrt/D=n.sqrt := by
  have bot : n.sqrt*D≤(D^2*n).sqrt := Nat.le_sqrt'.mpr (by
    rw [mul_pow,Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.sqrt_le' _))
  have top : (D^2*n).sqrt<(n.sqrt+1)*D := Nat.sqrt_lt'.mpr (by
    rw [mul_pow,Nat.mul_comm ((n.sqrt+1)^2)]
    exact Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_sqrt' _) (pow_pos dp _))
  exact le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul dp).mpr top))
    ((Nat.le_div_iff_mul_le dp).mpr bot)

theorem bracket_spec (k f n : ℕ) : (bracket k f n).1≤n.sqrt ∧ n.sqrt≤(bracket k f n).2 := by
  let D := 2^f
  let a := index k n
  have dp : 0<D := by dsimp [D]; positivity
  by_cases flat : shift k n=0
  · have same : index k n=n := by simp [index,flat]
    simp [bracket,readBracket,flat,same,floorEntry,unshifted n (show 0<2^f by positivity)]
  · have ceiling : ceilEntry f (a+1)=ceilSqrt (D^2*(a+1)) := ceil_from_floor _
    simpa only [bracket,readBracket,if_neg flat] using
      lookup (h:=2^(shift k n)) (D:=D) (a:=a) (t:=floorEntry f a) (c:=ceilEntry f (a+1))
        (by positivity) dp rfl (Nat.sqrt_le' _) (by rw [ceiling]; exact ceilSqrt_le_iff.mp le_rfl)

/-- Obtain the lower gap endpoint using its predecessor. This handles the
integer word boundary and exact squares without approximating a strict test. -/
noncomputable def ceilBand (k f : ℕ) : ℕ → ℕ×ℕ
  | 0 => (0,0)
  | n+1 => ((bracket k f n).1+1,(bracket k f n).2+1)

theorem ceil_spec (k f n : ℕ) :
    (ceilBand k f n).1≤ceilSqrt n ∧ ceilSqrt n≤(ceilBand k f n).2 := by
  cases n with
  | zero => exact ⟨le_rfl,le_rfl⟩
  | succ n => exact ⟨Nat.succ_le_succ (bracket_spec k f n).1,Nat.succ_le_succ (bracket_spec k f n).2⟩

noncomputable def support (lo hi : ℕ) (accept : ℕ→Bool) :=
  ((Icc lo hi).filter fun v => accept v = true).card

/-- Compute an inclusive interval count from the two endpoint counts for a
short list of residues. The subtraction also handles an empty interval. -/
theorem support_lanes (lo hi P : ℕ) (residues : Finset ℕ) (inside : ∀ r∈residues, r<P) :
    support lo hi (fun v => decide (v%P∈residues)) =
      (∑ r∈residues, GeometricWheelBlocks.laneLength P (hi+1) r) -
      (∑ r∈residues, GeometricWheelBlocks.laneLength P lo r) := by
  let pref := fun n => (range n).filter (fun v => v%P∈residues)
  have monotone : Monotone pref := by
    intro a b hab v hv
    obtain ⟨small,ok⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp small).trans_le hab),ok⟩
  rw [←GeometricWheelBlocks.retained_count residues inside (hi+1),
      ←GeometricWheelBlocks.retained_count residues inside lo]
  change _ = (pref (hi+1)).card - (pref lo).card
  by_cases h : lo≤hi+1
  · rw [←card_sdiff (monotone h)]
    unfold support
    congr 1
    ext v
    simp only [pref,mem_filter,mem_Icc,decide_eq_true_eq,mem_sdiff,mem_range]
    constructor
    · rintro ⟨⟨lv,vh⟩,ok⟩
      exact ⟨⟨by omega,ok⟩,fun bad => (Nat.not_lt_of_ge lv) bad.1⟩
    · rintro ⟨⟨vh,ok⟩,bad⟩
      exact ⟨⟨Nat.le_of_not_gt (fun small => bad ⟨small,ok⟩),by omega⟩,ok⟩
  · have empty : Icc lo hi=∅ := Icc_eq_empty_of_lt (by omega)
    simp [support,empty,Nat.sub_eq_zero_of_le (card_le_card (monotone (by omega : hi+1≤lo)))]

private theorem support_mono {l L h H : ℕ} (accept : ℕ→Bool) (low : L≤l) (high : h≤H) :
    support l h accept ≤ support L H accept := by
  apply card_le_card
  intro v hv
  obtain ⟨iv,ok⟩ := mem_filter.mp hv
  obtain ⟨vl,vh⟩ := mem_Icc.mp iv
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨low.trans vl,vh.trans high⟩,ok⟩

/-- Truncated square roots bracket the exact support for any row's residue filter.
The two radicands select their own shifts from the same table precision. -/
noncomputable def rowBounds (x B n w u k f P : ℕ) (accept : ℕ→ℕ→Bool) : ℕ×ℕ :=
  if x≤u ∧ u<B ∧ n≤u^2 then
    let low := ceilBand k f (u^2-(n+w))
    let high := bracket k f (u^2-n)
    let clip := min (u-x) (B-1-u)
    let keep := fun v => decide (v%2=(u+1)%2) && accept (u%P) (v%P)
    (support (max 1 low.2) (min high.1 clip) keep,
     support (max 1 low.1) (min high.2 clip) keep)
  else (0,0)

theorem support_bounds (x B n w u k f P : ℕ) (accept : ℕ→ℕ→Bool) :
    let bounds := rowBounds x B n w u k f P accept
    let exact := (options x B n w P accept u).card
    bounds.1≤exact ∧ exact≤bounds.2 := by
  let keep := fun v => decide (v%2=(u+1)%2) && accept (u%P) (v%P)
  let l := u^2-(n+w)
  let h := u^2-n
  let clip := min (u-x) (B-1-u)
  by_cases valid : x≤u ∧ u<B ∧ n≤u^2
  · have exact_count : (options x B n w P accept u).card =
        support (max 1 (ceilSqrt l)) (min h.sqrt clip) keep := by
      simp only [options,gaps,if_pos valid,support,filter_filter]
      congr 1
      ext v
      simp [keep,l,h,clip,and_comm]
    dsimp only
    rw [rowBounds,if_pos valid,exact_count]
    exact ⟨support_mono keep (max_le_max_left _ (ceil_spec k f l).2)
            (min_le_min_right _ (bracket_spec k f h).1),
           support_mono keep (max_le_max_left _ (ceil_spec k f l).1)
            (min_le_min_right _ (bracket_spec k f h).2)⟩
  · simp [rowBounds,options,gaps,valid]

/-- The same enclosure applies to physical odd pairs whose product has the
specified remainder. Each admissible half-gap counts one such pair. -/
theorem physical_bounds {P m : ℕ} (part : m∣P) (x B n w u k f σ : ℕ) :
    let bounds := rowBounds x B n w u k f P (productSuffix m σ)
    bounds.1≤(suffixPairs x B n w m σ u).card ∧ (suffixPairs x B n w m σ u).card≤bounds.2 := by
  simpa only [options_card_pairs part] using support_bounds x B n w u k f P (productSuffix m σ)

/-- Same convention as the finite ranking loop: first index with largest positive
score, returning none when the block has no occupied row. -/
noncomputable def winner (pool : Finset ℕ) (score : ℕ→ℕ) : Option ℕ := by
  classical
  let best := pool.filter fun k => 0<score k ∧ ∀ j∈pool, score j≤score k
  exact if h : best.Nonempty then some (best.min' h) else none

theorem winner_of_bounds {pool : Finset ℕ} {score lo hi : ℕ→ℕ} {a : ℕ}
    (bounds : ∀ j∈pool, lo j≤score j ∧ score j≤hi j) (member : a∈pool) (positive : 0<lo a)
    (earlier : ∀ j∈pool, j<a → hi j<lo a) (later : ∀ j∈pool, a<j → hi j≤lo a) :
    winner pool score=some a := by
  classical
  let best := pool.filter fun k => 0<score k ∧ ∀ j∈pool, score j≤score k
  have a_bound := (bounds a member).1
  have am : a∈best := by
    apply mem_filter.mpr
    refine ⟨member,positive.trans_le a_bound,?_⟩
    intro j jp
    rcases lt_trichotomy j a with h|rfl|h
    · exact (bounds _ jp).2.trans ((earlier _ jp h).le.trans a_bound)
    · rfl
    · exact (bounds _ jp).2.trans ((later _ jp h).trans a_bound)
  have live : best.Nonempty := ⟨a,am⟩
  have m := best.min'_mem live
  obtain ⟨mm,_,dominates⟩ := mem_filter.mp m
  have eq : best.min' live=a := by
    apply le_antisymm (best.min'_le _ am)
    by_contra! bad
    have h := earlier _ mm bad
    have z := (bounds _ mm).2
    have s := dominates a member
    omega
  change (if h : best.Nonempty then some (best.min' h) else none)=some a
  rw [dif_pos live,eq]

theorem winner_none_of_upper {pool : Finset ℕ} {score hi : ℕ→ℕ}
    (empty : ∀ k∈pool, score k≤hi k ∧ hi k=0) : winner pool score=none := by
  classical
  dsimp only [winner]
  split_ifs with h
  · obtain ⟨a,ma⟩ := h
    obtain ⟨mem,pos,_⟩ := mem_filter.mp ma
    obtain ⟨bound,zero⟩ := empty a mem
    omega
  · rfl

/-- A row that fails the comparison against an anchor's lower score is strictly
dominated, or loses the tie because the anchor occurs first. -/
theorem discard_at_anchor {score lo hi : ℕ→ℕ} {a j : ℕ}
    (upper : score j≤hi j) (lower : lo a≤score a)
    (discard : ¬(lo a<hi j ∨ hi j=lo a ∧ j≤a)) :
    score j<score a ∨ score j=score a ∧ a<j := by omega

/-- During the left-to-right exact pass an incumbent also wins every tie
with a later row whose upper score is at most its exact count. -/
theorem skip_after {score upper : ℕ→ℕ} {a j : ℕ} (before : a<j)
    (bound : score j≤upper j) (cutoff : upper j≤score a) :
    score j<score a ∨ score j=score a ∧ a<j := by omega

/-- Replace a chosen subset of row bounds by exact counts. Rows whose original
endpoints agree already have that exact count. -/
noncomputable def refined (done : Finset ℕ) (bounds : ℕ→ℕ×ℕ) (score : ℕ→ℕ) (u : ℕ) : ℕ×ℕ :=
  if u∈done then (score u,score u) else bounds u

theorem refine_spec {done : Finset ℕ} {bounds : ℕ→ℕ×ℕ} {score : ℕ→ℕ} {u : ℕ}
    (valid : (bounds u).1≤score u ∧ score u≤(bounds u).2) :
    (refined done bounds score u).1≤score u ∧ score u≤(refined done bounds score u).2 := by
  by_cases h : u∈done <;> simp [refined,h,valid]

theorem exact_if_equal {score l h : ℕ} (low : l≤score) (high : score≤h) (eq : l=h) :
    score=l := by omega

/-- Any mix of table bounds and exact refinements can certify the first positive
winner. The midpoint block may be the one proved sufficient by first_block. -/
theorem certified_choice (x B n w k f P : ℕ) (accept : ℕ→ℕ→Bool)
    (pool done : Finset ℕ) {a : ℕ} (member : a∈pool) :
    let score := fun u => (options x B n w P accept u).card
    let reading := refined done (fun u => rowBounds x B n w u k f P accept) score
    0<(reading a).1 →
    (∀ j∈pool, j<a → (reading j).2<(reading a).1) →
    (∀ j∈pool, a<j → (reading j).2≤(reading a).1) →
    winner pool score=some a := by
  intro score reading pos before after
  exact winner_of_bounds (lo:=fun u => (reading u).1) (hi:=fun u => (reading u).2)
    (fun u _ => refine_spec (support_bounds x B n w u k f P accept))
    member pos before after

/-- When every upper score is zero, the exact search returns no row. -/
theorem certified_empty (x B n w k f P : ℕ) (accept : ℕ→ℕ→Bool) (pool : Finset ℕ)
    (all : ∀ u∈pool, (rowBounds x B n w u k f P accept).2=0) :
    winner pool (fun u => (options x B n w P accept u).card)=none :=
  winner_none_of_upper (hi:=fun u => (rowBounds x B n w u k f P accept).2)
    (fun u inside => ⟨(support_bounds x B n w u k f P accept).2,all u inside⟩)

end PrimeFactors.FractionalWordRanking
