import PrimeFactors.HighWordSuffixRanking

/-! Square-root costs for scoring midpoint rows on one product. The local
predicate may depend on the public remainder. Both searches use the same
predicate. Each score is computed from scratch for this input. -/

namespace PrimeFactors.HighWordSuffixCost
open Finset

/-- The scoring loop visits floor(sqrt(T)) through floor(sqrt(T))+P inclusive.
Each locally accepted midpoint with a feasible physical lower bound costs
one root to compute the upper endpoint of its gap interval. -/
noncomputable def scored (B h P : ℕ) (pass : ℕ → Bool) : Finset ℕ :=
  let lower := B*h
  let floor := (lower+(B-1)).sqrt
  (Icc floor (floor+P)).filter fun m => pass m ∧ B/2≤m ∧ m<B ∧ lower≤m^2

/-- A local Fermat scan takes one exact square root for each accepted
midpoint up to and including the proposed answer. -/
noncomputable def direct (N u : ℕ) (pass : ℕ → Bool) : Finset ℕ :=
  (Icc (ceilSqrt N) u).filter fun m => pass m

/-- The ranking setup takes the word-endpoint root and the upper gap root
for every scored row. Rows strictly above the word also need a lower gap root. -/
noncomputable def scoringRoots (B h P : ℕ) (pass : ℕ → Bool) : ℕ :=
  let rows := scored B h P pass
  1 + rows.card + (rows.filter fun m => B*h+(B-1)<m^2).card

/-- The first Fermat midpoint never precedes the first scored midpoint.
Every direct square test through an in-block physical target is paid for
by its corresponding ranking setup root. -/
theorem direct_subset {b h P N u : ℕ} (pass : ℕ → Bool) (size : 14≤b)
    (lo : 2^b/2≤h) (hi : h<2^b) (word : N/2^b=h)
    (inBlock : u≤(2^b*h+(2^b-1)).sqrt+P) (physical : u<2^b) :
    direct N u pass ⊆ scored (2^b) h P pass := by
  let B := 2^b
  let n := B*h
  let T := n+(B-1)
  have lower : n≤N := by
    change 2^b*h≤N
    rw [←word]
    exact Nat.mul_div_le N (2^b)
  have square : N≤(ceilSqrt N)^2 := ceilSqrt_le_iff.mp le_rfl
  have prev : (T.sqrt-1)^2<n :=
    (HighWordSumRankingBounds.endpoints size lo hi).prev
  have start : T.sqrt≤ceilSqrt N := by
    by_contra! bad
    have := Nat.pow_le_pow_left (by omega : ceilSqrt N≤T.sqrt-1) 2
    omega
  have factorWidth : B/2≤ceilSqrt N := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    have small := Nat.mul_le_mul (Nat.div_le_self B 2) lo
    exact (show (B/2)^2≤n by simpa only [n,pow_two,B] using small).trans
      (lower.trans square)
  intro m hm
  obtain ⟨bounds,accepted⟩ := mem_filter.mp hm
  obtain ⟨ml,mu⟩ := mem_Icc.mp bounds
  have gain := Nat.pow_le_pow_left ml 2
  change m ∈ (Icc T.sqrt (T.sqrt+P)).filter _
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨start.trans ml,mu.trans inBlock⟩,
    accepted,factorWidth.trans ml,mu.trans_lt physical,lower.trans (square.trans gain)⟩

/-- A genuine in-block split appears in the direct scan with the same
factors. Including the initial square root on both sides and the final
ranked square test, the direct scan uses strictly fewer square roots. -/
theorem covers_hit {b h P N u p q : ℕ} (pass : ℕ → Bool) (size : 14≤b)
    (lo : 2^b/2≤h) (hi : h<2^b) (word : N/2^b=h)
    (scoredHit : u∈scored (2^b) h P pass) (nontrivial : 1<p) (order : p<q)
    (product : p*q=N) (sum : p+q=2*u) :
    u∈direct N u pass ∧
    let gap := (u^2-N).sqrt
    1<u-gap ∧ u-gap=p ∧ u+gap=q ∧
      1+(direct N u pass).card < scoringRoots (2^b) h P pass+1 := by
  have info := mem_filter.mp scoredHit
  obtain ⟨accepted,_,physical,_⟩ := info.2
  have included := direct_subset pass size lo hi word (mem_Icc.mp info.1).2 physical
  let d := q-u
  have mid : u=p+d := by dsimp [d]; omega
  have large : q=p+2*d := by dsimp [d]; omega
  have sq : u^2=N+d^2 := by rw [←product,mid,large]; ring
  have trueRoot : (u^2-N).sqrt=d := by rw [sq,Nat.add_sub_cancel_left,Nat.sqrt_eq']
  refine ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨ceilSqrt_le_iff.mpr (by omega),le_rfl⟩,accepted⟩,?_⟩
  dsimp only
  rw [trueRoot]
  have cost := card_le_card included
  dsimp only [scoringRoots]
  exact ⟨by omega,by omega,by omega,by omega⟩

/-- The experiment's midpoint filter looks for a residue of the right parity
in one period that passes the public product test. -/
def localPass (P : ℕ) (accept : ℕ → ℕ → Bool) (u : ℕ) : Bool :=
  (List.range P).any fun r => decide (r%2=(u+1)%2) && accept (u%P) r

/-- A row in the scoring block with even one suffix-compatible half-gap
is included in the root charge. For the experimental suffix predicate,
take accept = HighWordSuffixRanking.productSuffix m (N % m). -/
theorem scored_of_option {B h P u v : ℕ} (accept : ℕ → ℕ → Bool) (pp : 0<P)
    (evenP : 2∣P) (inBlock : u∈Icc (B*h+(B-1)).sqrt ((B*h+(B-1)).sqrt+P))
    (hit : v∈HighWordSuffixRanking.options (B/2) B (B*h) (B-1) P accept u) :
    u∈scored B h P (localPass P accept) := by
  obtain ⟨physical,suffix⟩ := mem_filter.mp hit
  obtain ⟨_,lo,hi,square,_,parity⟩ := HighWordSumRanking.mem_gaps.mp physical
  have reduced : v%P%2=(u+1)%2 := (Nat.mod_mod_of_dvd v evenP).trans parity
  have pass : localPass P accept u=true := by
    apply List.any_eq_true.mpr
    exact ⟨v%P,List.mem_range.mpr (Nat.mod_lt _ pp),by simp [reduced,suffix]⟩
  exact mem_filter.mpr ⟨inBlock,pass,by omega,by omega,by omega⟩

/-- For the actual product remainder every true factor midpoint in the scanned
block passes exactly the enabled parity and square-residue test. Thus callers
may apply covers_hit using the public remainder and physical pair hypotheses. -/
theorem scored_true {B h P m N u p q : ℕ} (bp : 0<B) (pp : 0<P) (evenP : 2∣P)
    (part : m∣P) (word : N/B=h) (lo : B/2≤p) (hi : q<B) (order : p<q)
    (odd : p%2=1) (product : p*q=N) (sum : p+q=2*u)
    (inBlock : u∈Icc (B*h+(B-1)).sqrt ((B*h+(B-1)).sqrt+P)) :
    u∈scored B h P (localPass P (HighWordSuffixRanking.productSuffix m (N%m))) := by
  let d := q-u
  have mid : u=p+d := by dsimp [d]; omega
  have large : q=p+2*d := by dsimp [d]; omega
  have sq : u^2=N+d^2 := by rw [←product,mid,large]; ring
  have pl : u-d=p := by omega
  have qr : u+d=q := by omega
  have dn : B*h≤N := by rw [←word]; exact Nat.mul_div_le N B
  have top := Nat.lt_mul_div_succ N bp
  rw [word,Nat.mul_add,Nat.mul_one] at top
  apply scored_of_option _ pp evenP inBlock (v:=d)
  apply (HighWordSuffixRanking.mem_suffix part).mpr
  refine ⟨HighWordSumRanking.mem_gaps.mpr
    ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩,?_⟩
  rw [pl,qr,product,Nat.mod_mod]

end PrimeFactors.HighWordSuffixCost
