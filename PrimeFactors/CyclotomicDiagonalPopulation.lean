import PrimeFactors.CyclotomicDiagonalSufficiency
import PrimeFactors.FiniteBinCollisionPopulation

/-! Unconditional coverage of the equal-coordinate approximation and of
real factor coordinates with one of the first J even sums. The population
consists of all sorted, distinct 1024-bit prime pairs with 2048-bit product. -/
namespace PrimeFactors.CyclotomicDiagonalPopulation

open Finset MixedPrefixSample CyclotomicProductCurve CyclotomicDiagonalEstimate
open FiniteBinCollisionPopulation (upperBand mem_band upper_subset band_pair_eligible)
open FirstSumMenuPopulation (menu event)
open private PrimeFactors.MixedPrefixSample.mem_primes PrimeFactors.MixedPrefixSample.mem_sample
  from PrimeFactors.MixedPrefixSample
open private PrimeFactors.FiniteBinCollisionPopulation.collision_bound
  PrimeFactors.FiniteBinCollisionPopulation.band_price PrimeFactors.FiniteBinCollisionPopulation.eligible_incidence
  from PrimeFactors.FiniteBinCollisionPopulation
open private PrimeFactors.FirstSumMenuPopulation.collision_count from PrimeFactors.FirstSumMenuPopulation
open private PrimeFactors.MonotoneClosePrimeLower.prime_ratio from PrimeFactors.MonotoneClosePrimeLower
open scoped Classical
set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

attribute [local irreducible] primes upperPrimes eligible ordered sample upperBand

noncomputable def diagonalHits := eligible.filter fun z =>
  |diagonal (z.1*z.2 : ℕ) X - reading (z.1*z.2) X| ≤ 1/(8192*(X:ℝ))

/-- At least one candidate has an integral menu sum and lies in the real
factor band, and a single reading is within tolerance of both responses. -/
def Compatible (J N : ℕ) : Prop := ∃ s∈menu J N, ∃ a b y : ℝ,
  (X:ℝ)≤a ∧ a≤b ∧ b≤2*X ∧ a*b=(N:ℝ) ∧ a+b=(s:ℝ) ∧
  |y-reading N X|≤1/(8192*(X:ℝ)) ∧ |y-trial X a b|≤1/(8192*(X:ℝ))

private theorem info {p q : ℕ} (ok : (p,q)∈eligible) :
    p∈primes ∧ q∈upperBand ∧ p<q ∧ X≤p ∧ q<2*X ∧ p.Prime ∧ q.Prime := by
  rw [eligible] at ok
  obtain ⟨base,order⟩ := PrimeFactors.MixedPrefixSample.mem_sample.mp ok
  obtain ⟨pm,qm,_,size,_⟩ := mem_ordered.mp base
  obtain ⟨⟨pl,_⟩,pp⟩ := PrimeFactors.MixedPrefixSample.mem_primes.mp pm
  obtain ⟨⟨_,qh⟩,qp⟩ := PrimeFactors.MixedPrefixSample.mem_primes.mp qm
  exact ⟨pm,mem_band.mpr ⟨qm,size.trans (Nat.mul_le_mul_right q order.le)⟩,order,pl,qh,pp,qp⟩

attribute [local irreducible] diagonalHits

/-- Each prime band member has every other band member as an eligible
partner. This gives a marginal estimate just for the larger endpoint. -/
theorem upper_marginal : 11*X*upperBand.card < 71000*eligible.card := by
  have count := ChebyshevPrimeSample.prime_count
  change 11*X<35500*(upperPrimes.card-1) at count
  have supply := count.trans_le (Nat.mul_le_mul_left 35500
    (Nat.sub_le_sub_right (card_le_card upper_subset) 1))
  have full := PrimeFactors.FiniteBinCollisionPopulation.collision_bound
    (upperBand ×ˢ upperBand) eligible upperBand (fun _ => 0) (by simp)
    (fun _ hp _ hq lt _ => band_pair_eligible hp hq lt)
  rw [card_product] at full
  have arithmetic {b t : ℕ} (large : 11*X<35500*(b-1)) (pairs : b*b≤2*t+b) :
      11*X*b<71000*t := by
    have pos : 0<b := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at large
    have times := Nat.mul_lt_mul_of_pos_right large pos
    have sub : b-1+1=b := by omega
    have expand := congrArg (· * b) sub
    nlinarith only [times,pairs,expand]
  exact arithmetic supply full

private abbrev W := 2310

private theorem tot : W.totient=480 := by
  rw [show W=2*(3*(5*(7*11))) by decide]
  norm_num [Nat.totient_mul (by decide : Nat.Coprime 2 (3*(5*(7*11)))),
    Nat.totient_mul (by decide : Nat.Coprime 3 (5*(7*11))),
    Nat.totient_mul (by decide : Nat.Coprime 5 (7*11)),
    Nat.totient_mul (by decide : Nat.Coprime 7 11),Nat.totient_prime]

/-- Count a short factor gap by recording the larger prime, the block of
2310 consecutive gaps, and the smaller prime's reduced residue. -/
theorem gap_count (A : Finset (ℕ×ℕ)) (G : ℕ) (sub : A⊆eligible)
    (small : ∀ z∈A, z.2-z.1≤G) : A.card≤upperBand.card*((G/W+1)*480) := by
  let units := (range W).filter (fun c => W.Coprime c)
  let code (z : ℕ×ℕ) := (z.2,((z.2-z.1)/W,z.1%W))
  have into : ∀ z∈A, code z∈upperBand ×ˢ (range (G/W+1) ×ˢ units) := by
    rintro ⟨p,q⟩ h
    obtain ⟨_,member,_,pl,_,pp,_⟩ := info (sub h)
    have cop := pp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt
      (by decide : 0<W) ((by decide +kernel : W<X).trans_le pl))
    refine mem_product.mpr ⟨member,mem_product.mpr ⟨mem_range.mpr
      (Nat.lt_succ_of_le (Nat.div_le_div_right (small _ h))),mem_filter.mpr
      ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),?_⟩⟩⟩
    change Nat.gcd W (p%W)=1
    rw [Nat.gcd_comm,←Nat.gcd_rec]
    exact cop.symm
  have inj : ∀ z∈A, ∀ t∈A, code z=code t → z=t := by
    rintro ⟨p,q⟩ h ⟨a,b⟩ k equal
    have qb : q=b := congrArg Prod.fst equal
    subst b
    have q1 := (info (sub h)).2.2.1.le
    have q2 := (info (sub k)).2.2.1.le
    have quot : (q-p)/W=(q-a)/W := congrArg (fun z => z.2.1) equal
    have res : p ≡ a [MOD W] := show p%W=a%W from congrArg (fun z => z.2.2) equal
    have gaps : q-p ≡ q-a [MOD W] := by
      apply Nat.ModEq.add_left_cancel res
      simpa only [Nat.add_sub_of_le q1,Nat.add_sub_of_le q2] using (Nat.ModEq.refl q (n:=W))
    have ident := congrArg₂ (fun i j : ℕ => W*i+j) quot gaps
    simp only [Nat.div_add_mod] at ident
    exact Prod.ext (by omega) rfl
  simpa only [card_product,card_range,units,←Nat.totient_eq_card_coprime,tot] using
    card_le_card_of_injOn code into inj

private theorem cost {A U T D m : ℕ} (count : A≤U*D) (rate : 11*X*U<71000*T)
    (fits : 71000*m*D≤11*X) : m*A<T := by
  apply Nat.lt_of_mul_lt_mul_left (a:=71000)
  calc 71000*(m*A) ≤ 71000*(m*(U*D)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ count)
       _ = (71000*m*D)*U := by ring
       _ ≤ 11*X*U := Nat.mul_le_mul_right _ fits
       _ < _ := rate

private theorem square_gap {p q B E : ℝ} (p0 : 0≤p) (sort : p≤q) (top : q≤2*B)
    (en : 0≤E) (near : p+q-2*Real.sqrt (p*q)≤E) : (q-p)^2≤E*(8*B) := by
  have q0 := p0.trans sort
  have root := Real.sq_sqrt (mul_nonneg p0 q0)
  have bound : Real.sqrt (p*q)≤q := (Real.sqrt_le_left q0).mpr (by
    simpa only [sq] using mul_le_mul_of_nonneg_right sort q0)
  calc (q-p)^2 = (p+q-2*Real.sqrt (p*q))*(p+q+2*Real.sqrt (p*q)) := by nlinarith only [root]
       _ ≤ E*(8*B) := mul_le_mul near (by linarith only [bound,sort,top]) (by positivity) en

/-- Less than one in 2^500 eligible products has an equal-coordinate
response within the proven rounding tolerance of the actual polynomial. -/
theorem diagonal_fraction : 2^500*diagonalHits.card<eligible.card := by
  apply cost (gap_count diagonalHits (18*2^508) (by unfold diagonalHits; exact filter_subset ..) ?_) upper_marginal (by decide +kernel)
  rintro ⟨p,q⟩ mem
  rw [diagonalHits] at mem
  obtain ⟨el,acc⟩ := mem_filter.mp mem
  obtain ⟨_,_,lt,pl,qh,pp,qp⟩ := info el
  have deficit := actual_gap pp qp lt (by exact_mod_cast (by decide +kernel : 0<X))
    (by exact_mod_cast pl) (by exact_mod_cast qh.le) acc
  rw [Nat.cast_mul] at deficit
  have square := square_gap (B:=(X:ℝ)) (by positivity : 0≤(p:ℝ))
    (by exact_mod_cast lt.le) (by exact_mod_cast qh.le) (by norm_num) deficit
  have limit : (81/256:ℝ)*(8*(X:ℝ))=((18*2^508:ℕ):ℝ)^2 := by norm_num [X]
  rw [limit,←Nat.cast_sub lt.le] at square
  exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (by exact_mod_cast square)

private theorem mem_population {P : ℕ→Prop} {z : ℕ×ℕ} :
    z∈sample P ↔ z∈eligible ∧ P (z.1*z.2) := by
  simp only [eligible,PrimeFactors.MixedPrefixSample.mem_sample,mem_ordered,and_true]
  tauto

/-- The first-J exact menu and the menu permitting a common rounded
reading have precisely the same full-width products. -/
theorem compatible_eq (J : ℕ) : sample (Compatible J)=sample (event J) := by
  ext ⟨p,q⟩
  rw [mem_population,FirstSumMenuPopulation.mem_sample_iff]
  apply and_congr_right
  intro el
  obtain ⟨_,_,lt,pl,qh,pp,qp⟩ := info el
  have xp : 0<(X:ℝ) := by exact_mod_cast (by decide +kernel : 0<X)
  have low : (X:ℝ)≤p := by exact_mod_cast pl
  have high : (q:ℝ)≤2*X := by exact_mod_cast qh.le
  constructor
  · rintro ⟨s,inside,a,b,y,al,ab,bh,prod,ss,act,test⟩
    rw [Nat.cast_mul] at prod
    have eq := unique_sum pp qp lt xp low high al ab bh prod.symm ss act test
    exact eq ▸ inside
  · intro inside
    refine ⟨p+q,inside,p,q,reading (p*q) X,low,by exact_mod_cast lt.le,high,by simp,by simp,?_,?_⟩
    · simp only [sub_self,abs_zero]; positivity
    · rw [actual_value pp qp lt,sub_self,abs_zero]; positivity

private theorem ceil_lt {n : ℕ} (pos : 0<n) : (ceilSqrt n:ℝ)<Real.sqrt n+1 := by
  let r := ceilSqrt n
  have rpos : 0<r := by
    by_contra! h
    have := ceilSqrt_le_iff.mp (show ceilSqrt n≤0 from h)
    simpa using (not_lt_of_ge this pos)
  have floor : (r-1)^2<n := lt_of_not_ge (fun h => (by omega : ¬r≤r-1) (ceilSqrt_le_iff.mpr h))
  have lower : ((r-1:ℕ):ℝ)<Real.sqrt n := Real.lt_sqrt_of_sq_lt (by exact_mod_cast floor)
  rw [Nat.cast_sub rpos,Nat.cast_one] at lower
  change (r:ℝ)<_
  linarith

/-- For any J, take G at least the square root of 16·2^1023·J. Each
possible larger prime has at most (floor(G/2310)+1)·480 smaller partners. -/
theorem menu_fraction {J G m : ℕ} (width : 16*X*J≤G^2)
    (fits : 71000*m*((G/2310+1)*480)≤11*X) :
    m*(sample (Compatible J)).card<eligible.card := by
  rw [compatible_eq]
  apply cost (gap_count _ G (fun _ h => (FirstSumMenuPopulation.mem_sample_iff.mp h).1) ?_)
    upper_marginal fits
  rintro ⟨p,q⟩ member
  obtain ⟨el,inside⟩ := FirstSumMenuPopulation.mem_sample_iff.mp member
  obtain ⟨_,_,lt,_,qh,pp,qp⟩ := info el
  obtain ⟨i,idx,eq⟩ := mem_image.mp inside
  have ij := mem_range.mp idx
  change 2*(ceilSqrt (p*q)+i)=p+q at eq
  have es : 2*((ceilSqrt (p*q):ℝ)+i)=(p:ℝ)+q := by exact_mod_cast eq
  have ir : (i:ℝ)+1≤J := by exact_mod_cast ij
  have root := ceil_lt (Nat.mul_pos pp.pos qp.pos)
  rw [Nat.cast_mul] at root
  have near : (p:ℝ)+q-2*Real.sqrt (p*q)≤2*J := by linarith only [es,ir,root]
  have sq := square_gap (B:=(X:ℝ)) (by positivity : 0≤(p:ℝ)) (by exact_mod_cast lt.le)
    (by exact_mod_cast qh.le) (by positivity) near
  have cap : 16*(X:ℝ)*J ≤ (G:ℝ)^2 := by exact_mod_cast width
  rw [←Nat.cast_sub lt.le] at sq
  have bound : ((q-p:ℕ):ℝ)^2≤(G:ℝ)^2 := by linarith only [sq,cap]
  exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (by exact_mod_cast bound)

/-- Up to a trillion even midpoint candidates still cover fewer than one
in 2^479 of the eligible prime pairs. -/
theorem menu40 : 2^479*(sample (Compatible (2^40))).card<eligible.card :=
  menu_fraction (G:=3*2^532) (by decide +kernel) (by decide +kernel)

/-- Partition the upper band into intervals of width 2^509. Every pair
of different primes in one such interval is eligible and has a short gap. -/
private theorem lower_of_short_gap (A : Finset (ℕ×ℕ)) (contains : ∀ p q : ℕ,
    (p,q)∈eligible → q-p<2^509 → (p,q)∈A) : eligible.card<2^517*A.card := by
  let lo : ℕ := 11*2^1020
  let D : ℕ := 2^509
  let b : ℕ := 5*2^511
  let index (p : ℕ) := (p-lo)/D
  have dp : 0<D := by decide +kernel
  have endpoints {p : ℕ} (hp : p∈upperBand) : lo≤p ∧ p<lo+b*D := by
    obtain ⟨pm,high⟩ := mem_band.mp hp
    have pl : lo^2≤p^2 := (by decide +kernel : lo^2≤2*X^2).trans (by simpa [sq] using high)
    have top := (PrimeFactors.MixedPrefixSample.mem_primes.mp pm).1.2
    exact ⟨(Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp pl,
      top.trans_le (by decide +kernel)⟩
  have bins (p : ℕ) (hp : p∈upperBand) : index p<b :=
    (Nat.div_lt_iff_lt_mul dp).mpr (by obtain ⟨_,hi⟩ := endpoints hp; omega)
  have energy := PrimeFactors.FirstSumMenuPopulation.collision_count upperBand index b bins
  have remove := PrimeFactors.FiniteBinCollisionPopulation.collision_bound _ A upperBand index rfl (by
    intro p hp q hq lt same
    obtain ⟨pl,_⟩ := endpoints hp
    obtain ⟨ql,_⟩ := endpoints hq
    have before := Nat.mul_div_le (p-lo) D
    have after := Nat.lt_mul_div_succ (q-lo) dp
    change (p-lo)/D=(q-lo)/D at same
    rw [←same,Nat.mul_add,Nat.mul_one] at after
    exact contains p q (band_pair_eligible hp hq lt) (show q-p<D by omega))
  have sub := card_le_card upper_subset
  have large : 1000*b≤upperBand.card := by
    have supply := ChebyshevPrimeSample.prime_count
    change 11*X<35500*(upperPrimes.card-1) at supply
    have room : 35500*(1000*b)≤11*X := by decide +kernel
    omega
  have count := PrimeFactors.FiniteBinCollisionPopulation.band_price
    (energy.trans (Nat.mul_le_mul_left _ remove)) large
    (PrimeFactors.MonotoneClosePrimeLower.prime_ratio.trans_le (Nat.mul_le_mul_left _ sub))
    PrimeFactors.FiniteBinCollisionPopulation.eligible_incidence
  exact count.trans_le (Nat.mul_le_mul_right _ (by decide +kernel))

/-- More than one eligible product in 2^517 has an accurate diagonal
response. No distribution assumption on primes in an individual bin is used. -/
theorem diagonal_lower : eligible.card<2^517*diagonalHits.card := by
  apply lower_of_short_gap
  intro p q member close
  obtain ⟨_,_,lt,pl,qh,pp,qp⟩ := info member
  have sq : ((q-p:ℕ):ℝ)^2 ≤ ((2^509:ℕ):ℝ)^2 := by
    exact_mod_cast Nat.pow_le_pow_left close.le 2
  rw [Nat.cast_sub lt.le] at sq
  have cap : ((2^509:ℕ):ℝ)^2≤(X:ℝ)/16 := by norm_num [X]
  rw [diagonalHits]
  exact mem_filter.mpr ⟨member,CyclotomicDiagonalSufficiency.gap_sufficient (B:=(X:ℝ)) pp qp lt
    (by exact_mod_cast (by decide +kernel : 0<X)) (by exact_mod_cast pl) (by exact_mod_cast qh.le)
    (sq.trans cap)⟩

/-- A two-sided finite frequency estimate for the same rounded diagonal
reading over the entire canonical 2048-bit population. -/
theorem diagonal_sandwich : eligible.card<2^517*diagonalHits.card ∧
    2^500*diagonalHits.card<eligible.card := ⟨diagonal_lower,diagonal_fraction⟩

end PrimeFactors.CyclotomicDiagonalPopulation
