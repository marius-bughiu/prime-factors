import PrimeFactors.UniversalPackingBudget
import PrimeFactors.ChebyshevPrimeSample

/-! Count products meeting a necessary length condition for uniform factor-sum
packing. The sample consists of sorted pairs of distinct 1024-bit primes with
a 2048-bit product. The condition concerns the entire public interval. -/
namespace PrimeFactors.SmallRadixPackingPopulation

open CyclotomicRadixLift ProductDeficitBand MixedPrefixSample Finset
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

/-- The necessary list-length inequality at a given upper limit on the radix. -/
def possible (M N : ℕ) : Prop :=
  choices N (stride N) (lower N X) (upper N X) ≤ (20160/stride N)*M

/-- Meeting the length condition with a smaller radix implies meeting it at the cap. -/
theorem possible_mono {M cap N : ℕ} (le : M ≤ cap) (h : possible M N) : possible cap N :=
  h.trans (Nat.mul_le_mul_left _ le)

/-- A product admits a uniformly unique largest digit bin for some positive
modulus and some positive radix within the cap. Both may depend on the product. -/
def hasUniformWindow (cap N : ℕ) : Prop :=
  ∃ M m : ℕ, 0 < M ∧ M ≤ cap ∧ 0 < m ∧
    UniversalPackingBudget.UniformWindow N m
      (stride N * UniversalPackingBudget.period (weight N) M)
      (UniversalPackingBudget.ceilDiv (UniversalPackingBudget.positions N X)
        (UniversalPackingBudget.period (weight N) M))

theorem possible_of_uniform {cap N : ℕ} (h : hasUniformWindow cap N) : possible cap N := by
  obtain ⟨M,m,radix,limit,modulus,unique⟩ := h
  have positive : 0 < 20160/stride N := by
    unfold stride
    rcases weights N with w|w|w|w <;> rw [w] <;> decide
  have need := UniversalPackingBudget.radix_needed modulus radix unique
  have room := (UniversalPackingBudget.ceil_iff positive).mp need
  exact room.trans (Nat.mul_le_mul_left _ ((Nat.div_le_self M _).trans limit))

/-- Losing the endpoints when counting one residue costs less than a stride. -/
private theorem fromChoices {N W L H : ℕ} (wp : 0<W) (hn : H≤N) :
    H-L ≤ W*choices N W L H+W := by
  have top := Nat.lt_mul_div_succ (N-L) wp
  have base := Nat.div_mul_le_self (N+W-H) W
  have compare : (N-L)/W+1 ≤ choices N W L H+bottom N W H := by unfold choices; omega
  have product := Nat.mul_le_mul_left W compare
  rw [Nat.mul_add W (choices ..)] at product
  change (N+W-H)/W*W≤_ at base
  rw [Nat.mul_comm _ W] at base
  change W*((N-L)/W+1)≤W*choices N W L H+W*((N+W-H)/W) at product
  omega

/-- For products in the upper half of the width square the upper endpoint
comes from the largest allowed factor. The distance of the square root to
that endpoint is controlled by the actual rounded interval length. -/
theorem endpoint {A B N : ℕ} (apos : 2≤A) (bdef : B=2*A-1)
    (big : 2*A^2≤N) (high : N≤B^2) :
    (B-ceilSqrt N)^2 ≤ B*(upper N A-lower N A+4) := by
  have ap : 0<A := by omega
  have bp : 0<B := by omega
  have ab : A≤B := by omega
  have cmp : A*B≤N := by
    exact (Nat.mul_le_mul_left A (show B≤2*A by omega)).trans (by nlinarith only [big])
  obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le cmp
  have quotient : B+N/B≤A+N/A := by
    rw [hz,Nat.mul_comm A B,add_comm (B*A) z,Nat.add_mul_div_right _ _ ap,
      Nat.mul_comm B A,Nat.add_mul_div_right _ _ bp]
    have bound := Nat.div_le_div_left (a:=z) ab ap
    omega
  have cap : sumCap N A=B+N/B := by
    unfold sumCap
    rw [←bdef,min_eq_right quotient]
  have upperBound : N/B≤B := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul bp).mpr
    nlinarith only [high,bp]
  have hUpper : upper N A=2*((B+N/B)/2) := by
    rw [upper,cap,min_eq_right (by omega)]
  let r := ceilSqrt N
  have rb : r≤B := ceilSqrt_le_iff.mpr high
  have ar : A<r := by
    apply lt_of_not_ge
    intro small
    have sq : N≤A^2 := ceilSqrt_le_iff.mp small
    nlinarith only [big,sq,Nat.mul_self_lt_mul_self (show 1<A by omega)]
  have hLower : lower N A=2*r-1 := by unfold lower; change max _ (2*r-1)=_; omega
  have before : (r-1)^2<N := by
    apply lt_of_not_ge
    intro large
    have : r≤r-1 := ceilSqrt_le_iff.mpr large
    omega
  have rpos : r-1+1=r := by omega
  have expand := congrArg (fun n : ℕ => n^2) rpos
  have sr : r^2≤N+2*B := by nlinarith only [expand,before,rb,rpos]
  have ceiling := Nat.lt_mul_div_succ N bp
  have room : B+N/B ≤ (upper N A-lower N A)+2*r+1 := by
    rw [hUpper,hLower]
    omega
  have bound := Nat.mul_le_mul_left B room
  have diff : B-r+r=B := Nat.sub_add_cancel rb
  have de := congrArg (fun n : ℕ => n^2) diff
  have dr := congrArg (fun n : ℕ => n*r) diff
  change (B-r)^2 ≤ _
  nlinarith only [bound,sr,ceiling,de,dr]

private theorem close {p q A B d : ℕ} (ap : 2≤A) (be : B=2*A-1)
    (ph : p≤B) (qh : q≤B) (big : 2*A^2≤p*q)
    (room : B*(upper (p*q) A-lower (p*q) A+4)<d^2) : B<p+2*d := by
  have top : p*q≤B^2 := by simpa only [pow_two] using Nat.mul_le_mul ph qh
  have small := (endpoint ap be big top).trans_lt room
  by_contra! away
  have db : d≤B := by omega
  have restore := Nat.sub_add_cancel db
  have rb : p*q≤(B-d)^2 := by
    have prod := Nat.mul_le_mul_left p qh
    have range := Nat.mul_le_mul_right B away
    have square := congrArg (fun n : ℕ => n^2) restore
    have cross := congrArg (fun n : ℕ => n*d) restore
    nlinarith only [prod,range,square,cross,sq_nonneg (d:ℤ)]
  have r := ceilSqrt_le_iff.mpr rb
  exact (Nat.not_le_of_lt small) (Nat.pow_le_pow_left (by omega : d≤B-ceilSqrt (p*q)) 2)

/-- Each factor must lie within twice the given radius of the largest width endpoint. -/
theorem near_endpoint {p q M d : ℕ} (ph : p<2*X) (qh : q<2*X) (big : 2*X^2≤p*q)
    (h : possible M (p*q)) (threshold : (2*X-1)*(20160*M+28)<d^2) :
    2*X-1<p+2*d := by
  let N := p*q
  let W := stride N
  have ws : 0<W ∧ W≤24 := by
    dsimp [W,stride]
    rcases weights N with e|e|e|e <;> omega
  have high : upper N X ≤ N :=
    (min_le_left ..).trans ((by decide +kernel : 4*X≤2*X^2).trans big)
  have scaled := Nat.mul_le_mul_left W h
  have cap : W*((20160/W)*M) ≤ 20160*M := by
    rw [←Nat.mul_assoc,Nat.mul_comm W]
    exact Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
  have room := fromChoices (L:=lower N X) ws.1 high
  have sf : W*choices N W (lower N X) (upper N X) ≤ 20160*M := scaled.trans cap
  have bound : upper N X-lower N X+4 ≤ 20160*M+28 := by omega
  exact close (A:=X) (by decide +kernel) rfl (by omega) (by omega) big
    ((Nat.mul_le_mul_left (2*X-1) bound).trans_lt threshold)

private def odds (d : ℕ) : Finset ℕ := (range d).image fun i => 2*X-1-2*i

private theorem inOdds {p d : ℕ} (odd : Odd p) (ph : p<2*X) (close : 2*X-1<p+2*d) :
    p∈odds d := by
  obtain ⟨i,hi⟩ := odd
  apply mem_image.mpr
  refine ⟨(2*X-1-p)/2,mem_range.mpr (by omega),?_⟩
  have xp : 0<X := by decide +kernel
  omega

attribute [local irreducible] possible ordered sample primes eligible odds

/-- Even counting every odd integer near the endpoint as a potential prime,
at most d² ordered pairs can meet the necessary condition. -/
theorem count {M d : ℕ} (threshold : (2*X-1)*(20160*M+28)<d^2) :
    2*(sample (possible M)).card ≤ d^2 := by
  classical
  have sub : ordered (possible M) ⊆ (odds d) ×ˢ (odds d) := by
    intro z hz
    obtain ⟨pm,qm,_,big,h⟩ := (mem_ordered (E:=possible M) (z:=z)).mp hz
    simp only [primes,mem_filter,mem_Ico] at pm qm
    have pl := pm.1
    have ql := qm.1
    have size : 2<X := by decide +kernel
    have p := near_endpoint pl.2 ql.2 big h threshold
    have q := near_endpoint ql.2 pl.2 (by simpa only [Nat.mul_comm z.2 z.1] using big)
      (by simpa only [Nat.mul_comm z.2 z.1] using h) threshold
    exact mem_product.mpr ⟨inOdds (pm.2.odd_of_ne_two (by omega)) pl.2 p,
      inOdds (qm.2.odd_of_ne_two (by omega)) ql.2 q⟩
  have size : (odds d).card ≤ d := by unfold odds; exact card_image_le.trans (card_range d).le
  have bound := card_le_card sub
  rw [two_orders,card_product] at bound
  simpa only [pow_two] using bound.trans (Nat.mul_le_mul size size)

private theorem frequency {M d e : ℕ} (th : (2*X-1)*(20160*M+28)<d^2)
    (num : 21000000*2^e*d^2≤2*2^2046) :
    2^e*(sample (possible M)).card < eligible.card := by
  have base := ChebyshevPrimeSample.eligible_count
  have cap := Nat.mul_le_mul_left (21000000*2^e) (count th)
  nlinarith only [cap,num,base]

theorem radix64 : 2^920*(sample (possible (2^64))).card < eligible.card :=
  frequency (d:=142*2^544) (by decide +kernel) (by decide +kernel)

theorem radix128 : 2^856*(sample (possible (2^128))).card < eligible.card :=
  frequency (d:=142*2^576) (by decide +kernel) (by decide +kernel)

/-- The uniform-window event is a subset of the necessary size event on the same
sorted prime-pair sample, even when each input chooses its own modulus and radix. -/
theorem uniform_subset (cap : ℕ) : sample (hasUniformWindow cap) ⊆ sample (possible cap) := by
  intro z hz
  simp only [sample,mem_filter,mem_ordered] at hz ⊢
  obtain ⟨⟨p,q,ne,size,window⟩,lt⟩ := hz
  exact ⟨⟨p,q,ne,size,possible_of_uniform window⟩,lt⟩

theorem uniform64 : 2^920*(sample (hasUniformWindow (2^64))).card < eligible.card :=
  (Nat.mul_le_mul_left _ (card_le_card (uniform_subset _))).trans_lt radix64

theorem uniform128 : 2^856*(sample (hasUniformWindow (2^128))).card < eligible.card :=
  (Nat.mul_le_mul_left _ (card_le_card (uniform_subset _))).trans_lt radix128

end PrimeFactors.SmallRadixPackingPopulation
