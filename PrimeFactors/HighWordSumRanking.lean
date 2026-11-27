import PrimeFactors.HighWordSumRankingBounds

/-! For a full-width word Bh..B(h+1)-1 with B=2^b and b≥14, one of the
two even sums nearest twice the square root of the word's upper endpoint
maximizes the number of distinct sorted odd integer factor pairs. -/

namespace PrimeFactors.HighWordSumRanking
open Finset

/-- The high word of (u-v)(u+v) gives precisely the row inequalities. -/
private theorem from_product {n w u v : ℕ} (le : v≤u)
    (lo : n≤(u-v)*(u+v)) (hi : (u-v)*(u+v)≤n+w) :
    n+v^2≤u^2 ∧ u^2≤n+w+v^2 := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le le
  rw [Nat.add_sub_cancel_left] at lo hi
  constructor <;> nlinarith

/-- The candidate half-gaps for a midpoint with no integer factor below x
or above B-1. The guard and clipping also handle both endpoints. -/
noncomputable def gaps (x B n w u : ℕ) : Finset ℕ :=
  if x≤u ∧ u<B ∧ n≤u^2 then
    (Finset.Icc (max 1 (PrimeFactors.ceilSqrt (u^2-(n+w))))
      (min (u^2-n).sqrt (min (u-x) (B-1-u)))).filter fun v => v%2=(u+1)%2
  else ∅

theorem mem_gaps {x B n w u v : ℕ} :
    v∈gaps x B n w u ↔
    0<v ∧ x+v≤u ∧ u+v<B ∧ n+v^2≤u^2 ∧ u^2≤n+w+v^2 ∧ v%2=(u+1)%2 := by
  by_cases possible : x≤u ∧ u<B ∧ n≤u^2
  · simp only [gaps,if_pos possible,Finset.mem_filter,Finset.mem_Icc,max_le_iff,
      le_min_iff,PrimeFactors.ceilSqrt_le_iff,Nat.le_sqrt']
    omega
  · rw [gaps,if_neg possible]
    constructor
    · simp
    · intro h
      exact (possible (by omega)).elim

/-- Sorted odd factor pairs with a selected sum and a product inside
the public word. -/
noncomputable def pairs (x B n w u : ℕ) : Finset (ℕ×ℕ) :=
  ((Ico x B) ×ˢ (Ico x B)).filter fun z =>
    z.1<z.2 ∧ z.1%2=1 ∧ z.2%2=1 ∧ n≤z.1*z.2 ∧ z.1*z.2≤n+w ∧ z.1+z.2=2*u

/-- Midpoint and half-gap coordinates count each actual factor pair once. -/
theorem gaps_card (x B n w u : ℕ) : (gaps x B n w u).card=(pairs x B n w u).card := by
  apply card_nbij' (fun v => (u-v,u+v)) (fun z => z.2-u)
  · intro v hv
    obtain ⟨pos,l,b,low,high,par⟩ := mem_gaps.mp hv
    simp only [pairs,mem_filter,mem_product,mem_Ico]
    have rec : u=u-v+v := by omega
    have identity : (u-v)*(u+v)+v^2=u^2 := by
      calc (u-v)*(u+v)+v^2 = (u-v)*((u-v+v)+v)+v^2 := congrArg (fun a => (u-v)*(a+v)+v^2) rec
           _ = (u-v+v)^2 := by ring
           _ = u^2 := by rw [←rec]
    repeat' constructor <;> omega
  · rintro ⟨p,q⟩ hpq
    simp only [pairs,mem_filter,mem_product,mem_Ico] at hpq
    obtain ⟨⟨⟨pl,pb⟩,⟨ql,qb⟩⟩,pq,po,qo,lo,hi,sum⟩ := hpq
    let v := q-u
    have l : v≤u := by dsimp [v]; omega
    have pe : u-v=p := by dsimp [v]; omega
    have qe : u+v=q := by dsimp [v]; omega
    have bound := from_product l (n:=n) (w:=w) (by rwa [pe,qe]) (by rwa [pe,qe])
    apply mem_gaps.mpr
    change 0<v ∧ _
    exact ⟨by dsimp [v]; omega,by dsimp [v]; omega,by dsimp [v]; omega,bound.1,bound.2,by dsimp [v]; omega⟩
  · intro v hv
    dsimp
    omega
  · rintro ⟨p,q⟩ hpq
    simp only [pairs,mem_filter,mem_product,mem_Ico] at hpq
    obtain ⟨_,pq,_,_,_,_,sum⟩ := hpq
    exact Prod.ext (by dsimp; omega) (by dsimp; omega)

/-- If R is the first whole midpoint above the top of a positive word,
an integer factor-width endpoint active at R makes later rows inject
into R by preserving the smaller factor. -/
private theorem clip_map {x B n w r u v : ℕ} (ru : r≤u) (top : n+w<r^2)
    (mid : u+v<B) (xmin : x+v≤u)
    (share : u^2≤n+w+v^2) (clip : min (r-x) (B-1-r) ≤ (r^2-n).sqrt)
    (rlo : n≤r^2) :
    let z := v-(u-r)
    0<z ∧ x+z≤r ∧ r+z<B ∧ n+z^2≤r^2 ∧ r^2≤n+w+z^2 ∧
      (v%2=(u+1)%2 → z%2=(r+1)%2) := by
  let p := u-v
  have pu : u=p+v := by dsimp [p]; omega
  have p_sq : p^2 ≤ n+w := by
    rw [pu] at share
    nlinarith only [share,Nat.zero_le (p*v)]
  have small : p<r := by
    by_contra! bad
    have sq := Nat.pow_le_pow_left bad 2
    omega
  let z := v-(u-r)
  have pz : r=p+z := by dsimp [z]; omega
  have z_le : z≤v := by dsimp [z]; omega
  have zz : z≤min (r-x) (B-1-r) := by
    exact le_min (by omega) (by omega)
  have zs := Nat.le_sqrt'.mp (zz.trans clip)
  have fall : p*z≤p*v := Nat.mul_le_mul_left p z_le
  change 0<z ∧ x+z≤r ∧ r+z<B ∧ n+z^2≤r^2 ∧ r^2≤n+w+z^2 ∧ (v%2=(u+1)%2 → z%2=(r+1)%2)
  refine ⟨by omega,by omega,by omega,by omega,?_,by dsimp [z]; omega⟩
  rw [pu] at share
  rw [pz]
  nlinarith only [share,fall]

private theorem root_up {v D : ℕ} : (v:ℝ) ≤ Real.sqrt (D:ℝ) ↔ v^2≤D := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  norm_cast

private theorem root_down {v D : ℕ} : Real.sqrt (D:ℝ) ≤ (v:ℝ) ↔ D≤v^2 := by
  rw [Real.sqrt_le_left (by positivity)]
  norm_cast

private theorem first_parity (x : ℝ) (xp : 0<x) (r : ℕ) :
    ∃ j : ℕ, 0<j ∧ j%2=(r+1)%2 ∧ x≤j ∧ (j:ℝ)<x+2 := by
  let f : ℕ := ⌈x⌉₊
  have low : x≤(f:ℝ) := Nat.le_ceil _
  have hi : (f:ℝ)<x+1 := Nat.ceil_lt_add_one xp.le
  have fp : 0<f := by exact_mod_cast xp.trans_le low
  by_cases parity : f%2=(r+1)%2
  · exact ⟨f,fp,parity,low,by linarith⟩
  · exact ⟨f+1,by omega,by omega,by push_cast; linarith,by push_cast; linarith⟩

/-- A window at least two real units wider than another contains enough
points of either required parity. The larger window is at midpoint r,
where the width clipping is known to leave the full interval available. -/
private theorem dominate_width {x B n w r u : ℕ} (top : n+w<r^2) (ru : r≤u)
    (full : (r^2-n).sqrt ≤ min (r-x) (B-1-r))
    (width : Real.sqrt ((u^2-n:ℕ):ℝ) - Real.sqrt ((u^2-(n+w):ℕ):ℝ) + 2 ≤
      Real.sqrt ((r^2-n:ℕ):ℝ) - Real.sqrt ((r^2-(n+w):ℕ):ℝ)) :
    (gaps x B n w u).card ≤ (gaps x B n w r).card := by
  classical
  let S := gaps x B n w u
  by_cases live : S.Nonempty
  · let a := S.min' live
    have am : a∈S := S.min'_mem live
    have ah := mem_gaps.mp am
    have alow : Real.sqrt ((u^2-(n+w):ℕ):ℝ) ≤ (a:ℝ) :=
      root_down.mpr (by obtain ⟨_,_,_,_,upper,_⟩ := ah; omega)
    obtain ⟨j,jp,par,ja,jb⟩ := first_parity (Real.sqrt ((r^2-(n+w):ℕ):ℝ))
      (Real.sqrt_pos.mpr (by exact_mod_cast Nat.sub_pos_of_lt top)) r
    have ulo : n≤u^2 := by have := Nat.pow_le_pow_left ru 2; omega
    apply Finset.card_le_card_of_injOn (fun v => j+(v-a))
    · intro v hv
      change v∈S at hv
      have vl : a≤v := S.min'_le _ hv
      obtain ⟨_,_,vB,vlo,_,vp⟩ := mem_gaps.mp hv
      have vhigh : (v:ℝ)≤Real.sqrt ((u^2-n:ℕ):ℝ) := root_up.mpr (by omega)
      let z := j+(v-a)
      have zlow : r^2-(n+w)≤z^2 := root_down.mp (ja.trans (by exact_mod_cast (show j≤z by dsimp [z]; omega)))
      have zhigh : z^2≤r^2-n := by
        apply root_up.mp
        dsimp [z]
        rw [Nat.cast_add,Nat.cast_sub vl]
        linarith only [vhigh,alow,width,jb]
      have bound := (Nat.le_sqrt'.mpr zhigh).trans full
      obtain ⟨left,right⟩ := le_min_iff.mp bound
      have zp : 0<z := by dsimp [z]; omega
      apply mem_gaps.mpr
      change 0<z ∧ x+z≤r ∧ r+z<B ∧ n+z^2≤r^2 ∧ r^2≤n+w+z^2 ∧ z%2=(r+1)%2
      refine ⟨zp,by omega,by omega,by omega,by omega,?_⟩
      have ap := ah.2.2.2.2.2
      dsimp [z]
      omega
    · intro v hv t ht eq
      have av : a≤v := S.min'_le _ hv
      have at' : a≤t := S.min'_le _ ht
      change j+(v-a)=j+(t-a) at eq
      omega
  · change S.card ≤ _
    simp [Finset.not_nonempty_iff_eq_empty.mp live]

/-- When a factor-width bound controls the reference midpoint, preserve
the smaller factor and inject every later row directly into that row. -/
private theorem dominate_clipped {x B n w r u : ℕ} (top : n+w<r^2) (ru : r≤u)
    (clip : min (r-x) (B-1-r) ≤ (r^2-n).sqrt) :
    (gaps x B n w u).card ≤ (gaps x B n w r).card := by
  apply Finset.card_le_card_of_injOn (fun v => v-(u-r))
  · intro v hv
    obtain ⟨_,xl,bu,_,sq,par⟩ := mem_gaps.mp hv
    obtain ⟨pos,left,right,low,high,parity⟩ :=
      clip_map ru top bu xl sq clip (by omega)
    exact mem_gaps.mpr ⟨pos,left,right,low,high,parity par⟩
  · intro v hv t ht eq
    have pos {a} (ha : a∈gaps x B n w u) : 0<a-(u-r) := by
      obtain ⟨_,xl,bu,_,sq,_⟩ := mem_gaps.mp ha
      exact (clip_map ru top bu xl sq clip (by omega)).1
    have vp := pos hv
    have tp := pos ht
    change v-(u-r)=t-(u-r) at eq
    omega

private theorem two_best {b h : ℕ} (size : 14≤b) (lo : 2^b/2≤h) (hi : h<2^b) (u : ℕ) :
    let B := 2^b
    let n := B*h
    let w := B-1
    let T := n+w
    let C := fun m => (gaps (B/2) B n w m).card
    C u ≤ max (C T.sqrt) (C (PrimeFactors.ceilSqrt T)) := by
  let B := 2^b
  let n := B*h
  let w := B-1
  let T := n+w
  let a := T.sqrt
  let r := a+1
  let C := fun m => (gaps (B/2) B n w m).card
  have bounds : HighWordSumRankingBounds.Frame B n T := HighWordSumRankingBounds.endpoints size lo hi
  have hw : 16384 ≤ B := Nat.pow_le_pow_right (by decide : 0<2) size
  have span : w+1=B := by dsimp only [w]; omega
  change C u ≤ max (C a) (C (PrimeFactors.ceilSqrt T))
  rw [bounds.ceil_eq]
  change C u ≤ max (C a) (C r)
  by_cases early : u<a
  · have prev : (a-1)^2<n := bounds.prev
    have before := (Nat.pow_le_pow_left (by omega : u≤a-1) 2).trans_lt prev
    have empty : gaps (B/2) B n w u=∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro v hv
      have low := (mem_gaps.mp hv).2.2.2.1
      omega
    change (gaps (B/2) B n w u).card ≤ _
    simp [empty]
  by_cases later : r<u
  · apply le_trans _ (le_max_right (C a) (C r))
    have above : n+w<r^2 := bounds.above
    rcases le_total (min (r-B/2) (B-1-r)) ((r^2-n).sqrt) with clipped|full
    · exact dominate_clipped above later.le clipped
    · exact dominate_width above later.le full
        (HighWordSumRankingBounds.drop_two hw span above bounds.excess bounds.space later)
  rcases (show u=a ∨ u=r by dsimp only [r] at *; omega) with eq|eq
  · rw [eq]; exact le_max_left ..
  · rw [eq]; exact le_max_right ..

/-- In a balanced word Bh..B(h+1)-1 of odd products for B=2^b and b≥14,
at least one of two proposed sums maximizes the count of possible integer
factor pairs. Their midpoints are the floor and ceiling square roots of the
word's top. -/
theorem maximum {b h : ℕ} (size : 14≤b) (lo : 2^b/2≤h) (hi : h<2^b) (u : ℕ) :
    let B := 2^b
    let n := B*h
    let w := B-1
    let T := n+w
    let C := fun m => (pairs (B/2) B n w m).card
    C u ≤ max (C T.sqrt) (C (PrimeFactors.ceilSqrt T)) := by
  simpa only [←gaps_card] using two_best size lo hi u

/-- The number of integers in the closed interval having the supplied parity.
The first matching integer determines the count by one division by two. -/
private theorem parity_count (lo hi k : ℕ) :
    ((Icc lo hi).filter (fun v => v%2=k%2)).card =
      let f := lo+(if lo%2=k%2 then 0 else 1)
      if hi<f then 0 else (hi-f)/2+1 := by
  let f := lo+(if lo%2=k%2 then 0 else 1)
  change _ = if hi<f then 0 else (hi-f)/2+1
  have step : lo≤f ∧ f≤lo+1 ∧ f%2=k%2 := by
    dsimp only [f]
    split <;> omega
  have first (v : ℕ) (hv : lo≤v) (matchParity : v%2=k%2) : f≤v := by omega
  by_cases empty : hi<f
  · rw [if_pos empty]
    apply card_eq_zero.mpr
    apply eq_empty_of_forall_not_mem
    intro v hv
    obtain ⟨⟨vl, vh⟩, matchParity⟩ := mem_filter.mp hv |>.imp_left mem_Icc.mp
    have := first v vl matchParity
    omega
  · rw [if_neg empty]
    have eq : (Icc lo hi).filter (fun v => v%2=k%2) =
        (range ((hi-f)/2+1)).image (fun j => f+2*j) := by
      ext v
      simp only [mem_filter,mem_Icc,mem_image,mem_range]
      constructor
      · rintro ⟨⟨vl,vh⟩,matchParity⟩
        have lower := first v vl matchParity
        refine ⟨(v-f)/2,?_,?_⟩ <;> omega
      · rintro ⟨j,jl,rfl⟩
        omega
    rw [eq,card_image_of_injective _ (by intro a b h; change f+2*a=f+2*b at h; omega),card_range]

/-- Exact count without generating the permitted gaps. The two integer roots
bound the gap interval. The parity adjustment identifies its first element. -/
def rowCount (x B n w u : ℕ) : ℕ :=
  if x≤u ∧ u<B ∧ n≤u^2 then
    let lo := max 1 (PrimeFactors.ceilSqrt (u^2-(n+w)))
    let hi := min (u^2-n).sqrt (min (u-x) (B-1-u))
    let first := lo+(if lo%2=(u+1)%2 then 0 else 1)
    if hi<first then 0 else (hi-first)/2+1
  else 0

theorem rowCount_eq (x B n w u : ℕ) : rowCount x B n w u=(pairs x B n w u).card := by
  rw [←gaps_card]
  by_cases ok : x≤u ∧ u<B ∧ n≤u^2
  · simp only [rowCount,gaps,if_pos ok,parity_count]
  · simp only [rowCount,gaps,if_neg ok,card_empty]

namespace PrimeExample

/-- Half-gaps that give two primes in the word with 14-bit high part 8197. -/
noncomputable def primeGaps (u : ℕ) : Finset ℕ :=
  (gaps 8192 16384 (16384*8197) 16383 u).filter
    fun v => (u-v).Prime ∧ (u+v).Prime

private noncomputable def localPass (z : ℕ) : Bool :=
  (List.range 127).all fun k => z%(k+2) != 0

private theorem sieve {z : ℕ} (low : 128<z) (high : z<16384) :
    z.Prime ↔ localPass z = true := by
  simp only [localPass, List.all_eq_true, List.mem_range, bne_iff_ne]
  constructor
  · intro prime i small zero
    have divides := Nat.dvd_of_mod_eq_zero zero
    rcases (Nat.dvd_prime prime).mp divides with one | same <;> omega
  · intro ok
    by_contra composite
    have small := Nat.minFac_sq_le_self (show 0<z by omega) composite
    have mlow := (Nat.minFac_prime (show z≠1 by omega)).two_le
    have maxdiv : z.minFac≤128 := by
      by_contra! bad
      have far := Nat.pow_le_pow_left (show 129≤z.minFac by omega) 2
      omega
    have nz := ok (z.minFac-2) (by omega)
    have zero := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd z)
    rw [show z.minFac-2+2=z.minFac by omega] at nz
    exact nz zero

private noncomputable def table (u : ℕ) : List ℕ :=
  (List.range 228).filter fun v =>
    decide (0<v ∧ 8192+v≤u ∧ u+v<16384 ∧ 16384*8197+v^2≤u^2 ∧
      u^2≤16384*8197+16383+v^2 ∧ v%2=(u+1)%2) &&
    localPass (u-v) && localPass (u+v)

private theorem read_table (u : ℕ) (hu : u≤11591) : primeGaps u=(table u).toFinset := by
  ext v
  simp only [primeGaps,Finset.mem_filter,mem_gaps,table,
    List.mem_toFinset,List.mem_filter,List.mem_range,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨word,pp,qq⟩
    have wordCopy := word
    obtain ⟨pv,lv,uv,sq,_,_⟩ := wordCopy
    have small : v<228 := by
      by_contra! bad
      have far := Nat.pow_le_pow_left bad 2
      have top := Nat.pow_le_pow_left hu 2
      omega
    exact ⟨small,⟨word, (sieve (by omega) (by omega)).mp pp⟩,
      (sieve (by omega) (by omega)).mp qq⟩
  · rintro ⟨_,⟨word,pp⟩,qq⟩
    have wordCopy := word
    obtain ⟨_,lv,uv,_,_,_⟩ := wordCopy
    exact ⟨word,(sieve (by omega) (by omega)).mpr pp,(sieve (by omega) (by omega)).mpr qq⟩

/-- Three adjacent rows contain respectively zero, one and three prime pairs. -/
theorem exact_sets :
    primeGaps 11589 = ∅ ∧ primeGaps 11590 = {153} ∧
    primeGaps 11591 = {192,198,222} := by
  have tables : table 11589=[] ∧ table 11590=[153] ∧ table 11591=[192,198,222] := by decide +kernel
  obtain ⟨a,b,c⟩ := tables
  rw [read_table _ (by decide : 11589≤11591),read_table _ (by decide : 11590≤11591),
    read_table _ (by decide : 11591≤11591),a,b,c]
  decide

theorem counts :
    (primeGaps 11589).card=0 ∧ (primeGaps 11590).card=1 ∧ (primeGaps 11591).card=3 := by
  obtain ⟨a,b,c⟩ := exact_sets
  rw [a,b,c]
  decide

/-- Although one of the two endpoint midpoints maximizes integer-pair
coverage, the immediately following row has more genuine prime pairs
than both endpoint rows combined on this explicit high word. -/
theorem prime_counterexample :
    let t := 16384*8197+(16384-1)
    (primeGaps t.sqrt).card+(primeGaps (PrimeFactors.ceilSqrt t)).card <
      (primeGaps (PrimeFactors.ceilSqrt t+1)).card := by
  let t := 16384*8197+(16384-1)
  change (primeGaps t.sqrt).card+(primeGaps (PrimeFactors.ceilSqrt t)).card <
    (primeGaps (PrimeFactors.ceilSqrt t+1)).card
  have floor : t.sqrt=11589 := by
    apply Nat.le_antisymm
    · exact Nat.lt_succ_iff.mp (Nat.sqrt_lt'.mpr (by decide : t<11590^2))
    · exact Nat.le_sqrt'.mpr (by decide : 11589^2≤t)
  have ceil : PrimeFactors.ceilSqrt t=11590 := by
    have high := PrimeFactors.ceilSqrt_le_iff.mpr (by decide : t≤11590^2)
    have low : ¬PrimeFactors.ceilSqrt t≤11589 := fun wrong =>
      (by decide : ¬t≤11589^2) (PrimeFactors.ceilSqrt_le_iff.mp wrong)
    omega
  rw [floor,ceil]
  obtain ⟨a,b,c⟩ := counts
  change _ < (primeGaps 11591).card
  omega

/-- Squaring explicit endpoint witnesses avoids reducing a square root
in the kernel when checking the worked example. -/
private theorem count_from_roots (u a b C : ℕ)
    (ok : 8192≤u ∧ u<16384 ∧ 16384*8197≤u^2)
    (above : u^2-(16384*8197+16383)≤a^2)
    (below : a=0 ∨ (a-1)^2<u^2-(16384*8197+16383))
    (floorLo : b^2≤u^2-16384*8197) (floorHi : u^2-16384*8197<(b+1)^2)
    (answer : let lo := max 1 a
              let hi := min b (min (u-8192) (16384-1-u))
              let f := lo+(if lo%2=(u+1)%2 then 0 else 1)
              (if hi<f then 0 else (hi-f)/2+1)=C) :
    rowCount 8192 16384 (16384*8197) 16383 u=C := by
  have floor : (u^2-16384*8197).sqrt=b :=
    le_antisymm (Nat.lt_succ_iff.mp (Nat.sqrt_lt'.mpr floorHi)) (Nat.le_sqrt'.mpr floorLo)
  have ceiling : PrimeFactors.ceilSqrt (u^2-(16384*8197+16383))=a := by
    apply le_antisymm (PrimeFactors.ceilSqrt_le_iff.mpr above)
    by_contra! small
    have upper := PrimeFactors.ceilSqrt_le_iff.mp
      (show PrimeFactors.ceilSqrt (u^2-(16384*8197+16383))≤a-1 by omega)
    omega
  simpa only [rowCount,if_pos ok,floor,ceiling] using answer

/-- Counts before primality filtering in the three example rows. -/
theorem integer_counts :
    rowCount 8192 16384 (16384*8197) 16383 11589=36 ∧
    rowCount 8192 16384 (16384*8197) 16383 11590=29 ∧
    rowCount 8192 16384 (16384*8197) 16383 11591=20 := by
  refine ⟨count_from_roots 11589 0 72 36 ?_ ?_ ?_ ?_ ?_ ?_,
    count_from_roots 11590 110 168 29 ?_ ?_ ?_ ?_ ?_ ?_,
    count_from_roots 11591 188 227 20 ?_ ?_ ?_ ?_ ?_ ?_⟩ <;> decide +kernel

end PrimeExample

end PrimeFactors.HighWordSumRanking
