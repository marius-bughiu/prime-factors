import PrimeFactors.ShortPascalRow
import PrimeFactors.MixedPrefixSample
import PrimeFactors.QuantileThetaBounds
import PrimeFactors.Fermat

/-! Inclusive smaller-factor interval lengths and their frequency among the
repository's uniform unordered pairs. The only external population input is
Axler's unconditional bound on the first Chebyshev function at 33 endpoints.
The elementary comparisons and the transfer to finite cardinalities are checked here. -/

namespace PrimeFactors.ShortRowPopulation

open Finset MixedPrefixSample

set_option exponentiation.threshold 8192

/-- Number of integers from ceil(sqrt(n/2)) to floor(sqrt(n)), inclusive. -/
def ratioWidth (n : ℕ) := n.sqrt+1 - ceilSqrt ((n+1)/2)

/-- Number of integers from the lower endpoint implied by the partner's bit length. -/
def partnerWidth (B n : ℕ) := n.sqrt+1 - ShortPascalRow.lower n B

private theorem endpoints {B n : ℕ} (B0 : 0<B) (np : 0<n) :
    n ≤ 2*B*ShortPascalRow.lower n B ∧
    100*ceilSqrt ((n+1)/2) ≤ 71*(n.sqrt+1)+100 := by
  have base : (n-1)/(2*B-1)+1 ≤ ShortPascalRow.lower n B := le_max_right _ _
  have h := Nat.lt_mul_div_succ (n-1) (show 0<2*B-1 by omega)
  have h' := Nat.mul_le_mul (Nat.sub_le (2*B) 1) base
  refine ⟨by omega,?_⟩
  rw [show (n+1)/2=(n-1)/2+1 by omega]
  change 100*(((n-1)/2).sqrt+1) ≤ _
  have u := Nat.sqrt_le' ((n-1)/2)
  have v := Nat.lt_succ_sqrt' n
  have z : 2*((n-1)/2)≤n := by omega
  have cut : 100*((n-1)/2).sqrt≤71*(n.sqrt+1) := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    nlinarith only [u,v,z]
  omega

private theorem sqrt_scale {s B n : ℕ} (Blarge : 1000≤B) (hi : n<(s+1)^2)
    (near : 3*B^2≤n) : 172*B≤100*s := by
  by_contra! bad
  have cut : 100*(s+1) ≤ 173*B := by omega
  have h := Nat.pow_le_pow_left cut 2
  nlinarith only [h,hi,near,sq_nonneg B,Blarge]

private theorem sqrt_scale' {s B n : ℕ} (Blarge : 1000≤B) (hi : n<(s+1)^2)
    (near : 7*B^2≤2*n) : 186*B≤100*s := by
  by_contra! bad
  have cut : 100*(s+1) ≤ 187*B := by omega
  have h := Nat.pow_le_pow_left cut 2
  nlinarith only [h,hi,near,sq_nonneg B,Blarge]

/-- At either indicated public product threshold, even the inclusive integer
count is strictly smaller by the stated factor. The width can be zero for
an arbitrary n; each eligible semiprime does have a divisor in the interval. -/
theorem width_savings {B n : ℕ} (Blarge : 1000≤B) (near : 3*B^2≤n) :
    2*partnerWidth B n < ratioWidth n ∧
      (7*B^2≤2*n → 4*partnerWidth B n < ratioWidth n) := by
  have Blo : 0<B := by omega
  obtain ⟨limit,ratio⟩ := endpoints Blo (show 0<n by nlinarith [Nat.zero_le ((B-1)^2)])
  let s := n.sqrt
  let l := ShortPascalRow.lower n B
  have sq : s^2≤n := Nat.sqrt_le' n
  have hi : n<(s+1)^2 := Nat.lt_succ_sqrt' n
  have scale := sqrt_scale Blarge hi near
  have sBig : 1000≤s := by omega
  have lo : 172*s≤200*l := by
    apply Nat.le_of_mul_le_mul_left (c:=B) _ Blo
    have h := Nat.mul_le_mul_right s scale
    change n≤2*B*l at limit
    nlinarith only [sq,h,limit]
  change 100*ceilSqrt ((n+1)/2) ≤ 71*(s+1)+100 at ratio
  change 2*(s+1-l)<s+1-ceilSqrt ((n+1)/2) ∧ (_ → 4*(s+1-l)<s+1-ceilSqrt ((n+1)/2))
  constructor
  · omega
  · intro close
    have scale' := sqrt_scale' Blarge hi close
    have lo' : 372*s≤400*l := by
      apply Nat.le_of_mul_le_mul_left (c:=B) _ Blo
      have h := Nat.mul_le_mul_right s scale'
      change n≤2*B*l at limit
      nlinarith only [sq,h,limit]
    omega

/-- Each edge is a multiple of 2^1018, so the half-open and closed-endpoint
versions of the Chebyshev theta function agree there. -/
def stepSize : ℕ := 2^1018
def edge (i : ℕ) := (32+i)*stepSize

private theorem step_pos : 0<stepSize := by decide +kernel
private theorem scale : 32*stepSize=X := by decide +kernel
private theorem edge_mono : StrictMono edge := fun _ _ h =>
  Nat.mul_lt_mul_of_pos_right (by omega) step_pos

private noncomputable def below (u : ℕ) := (range u).filter Nat.Prime
noncomputable def bin (i : ℕ) := (Ico (edge i) (edge (i+1))).filter Nat.Prime

/-- The usual first Chebyshev function, summed with strict upper endpoint.
The endpoints used here are even composite integers. -/
noncomputable def thetaLt (u : ℕ) : ℝ := ∑ p∈below u, Real.log p

theorem edge_composite (i : ℕ) : ¬(edge i).Prime := by
  have hp : 1<stepSize := by decide +kernel
  intro prime
  have d : stepSize∣edge i := dvd_mul_left _ _
  rcases prime.eq_one_or_self_of_dvd _ d with o|a
  · omega
  · have large : stepSize < edge i := by
      change stepSize < (32+i)*stepSize
      have := Nat.mul_lt_mul_of_pos_right (show 1<32+i by omega) step_pos
      simpa only [one_mul] using this
    omega

/-- Precisely 33 instances of equation (1.6) in Axler, arXiv:2203.05917.
All endpoints have logarithm greater than 709, above the theorem's threshold 29. -/
def AxlerEndpoints : Prop := ∀ i≤32, |thetaLt (edge i)-(edge i:ℝ)| ≤
  (24334/10^6 : ℝ)*(edge i:ℝ)/(Real.log (edge i))^3

private theorem mem_bin {i p : ℕ} : p∈bin i ↔ (edge i≤p ∧ p<edge (i+1)) ∧ p.Prime := by
  simp [bin]

private theorem bin_sum (i : ℕ) : ∑ p∈bin i, Real.log (p:ℝ) =
    thetaLt (edge (i+1)) - thetaLt (edge i) := by
  have eq : bin i=below (edge (i+1))\below (edge i) := by
    ext x
    by_cases pr : x.Prime
    · simp [mem_bin,below,pr]
      omega
    · simp [mem_bin,below,pr]
  have inc : below (edge i)⊆below (edge (i+1)) := by
    intro p hp
    simp only [below,mem_filter,mem_range] at hp ⊢
    exact ⟨lt_trans hp.1 (edge_mono (Nat.lt_succ_self i)),hp.2⟩
  rw [eq,eq_sub_iff_add_eq]
  exact sum_sdiff inc

private theorem size_edge {i : ℕ} (hi : i≤32) : X≤edge i ∧ edge i≤2*X := by
  rw [←scale]
  exact ⟨Nat.mul_le_mul_right _ (by omega),by
    dsimp [edge]
    rw [←Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (by omega)⟩

private theorem lg {p : ℕ} (lo : X≤p) (hi : p≤2*X) :
    709 < Real.log p ∧ Real.log p < 710 := by
  obtain ⟨l,h,_⟩ := QuantileThetaBounds.target_band
  have a : (0:ℝ)<(X:ℝ) := Nat.cast_pos.mpr (by decide +kernel)
  have z : (2:ℝ)^1023=(X:ℝ) := by norm_num [X]
  have t : (2:ℝ)^1024=((2*X:ℕ):ℝ) := by norm_num [X]
  rw [z] at l
  rw [t] at h
  have e := Real.log_le_log a (show (X:ℝ)≤p by exact_mod_cast lo)
  have f := Real.log_le_log (lt_of_lt_of_le a (by exact_mod_cast lo))
    (show (p:ℝ)≤((2*X:ℕ):ℝ) by exact_mod_cast hi)
  exact ⟨l.trans_le e,f.trans_lt h⟩

private theorem endpoint_error (analytic : AxlerEndpoints) {i : ℕ} (hi : i≤32) :
    |thetaLt (edge i)-(edge i:ℝ)| ≤ (stepSize:ℝ)/1000000 := by
  obtain ⟨lo,up⟩ := size_edge hi
  have loglo := (lg lo up).1
  apply (analytic i hi).trans
  apply (div_le_iff₀ (by positivity : 0<(Real.log (edge i))^3)).mpr
  have power : (709:ℝ)^3 ≤ (Real.log (edge i))^3 := pow_le_pow_left₀ (by norm_num) loglo.le 3
  have x : (0:ℝ)≤stepSize := by positivity
  rw [←scale] at up
  have up' : (edge i:ℝ) ≤ 2*(32*(stepSize:ℝ)) := by exact_mod_cast up
  nlinarith only [up',mul_le_mul_of_nonneg_left power x,x]

/-- Uniform integer bounds for the population of each of the 32 prime bins. -/
theorem bin_count (analytic : AxlerEndpoints) {i : ℕ} (hi : i<32) :
    stepSize/711 ≤ (bin i).card ∧ (bin i).card ≤ stepSize/708 := by
  have ee := abs_le.mp (endpoint_error analytic hi.le)
  have ff := abs_le.mp (endpoint_error analytic (show i+1≤32 by omega))
  have e : (edge (i+1):ℝ)=(edge i:ℝ)+(stepSize:ℝ) := by simp [edge]; ring
  have bounds (p : ℕ) (h : p∈bin i) : 709<Real.log p ∧ Real.log p<710 :=
    lg ((size_edge hi.le).1.trans (mem_bin.mp h).1.1)
      ((mem_bin.mp h).1.2.le.trans (size_edge (by omega : i+1≤32)).2)
  have below' := Finset.card_nsmul_le_sum (bin i) (fun p => Real.log (p:ℝ)) 709
    (fun p hp => (bounds p hp).1.le)
  have above' := Finset.sum_le_card_nsmul (bin i) (fun p => Real.log (p:ℝ)) 710
    (fun p hp => (bounds p hp).2.le)
  simp only [bin_sum,nsmul_eq_mul] at below' above'
  have lo : (stepSize:ℝ)≤(bin i).card*711 := by linarith [ee.1,ee.2,ff.1,ff.2]
  have up : ((bin i).card:ℝ)*708≤stepSize := by linarith [ee.1,ee.2,ff.1,ff.2]
  have a : stepSize≤(bin i).card*711 := by exact_mod_cast lo
  exact ⟨by omega,(Nat.le_div_iff_mul_le (by decide)).mpr (by exact_mod_cast up)⟩

private noncomputable def grid := (range 32) ×ˢ (range 32)
private noncomputable def possible := grid.filter fun ij => 2048 < (33+ij.1)*(33+ij.2)
private noncomputable def certain (a b : ℕ) := grid.filter fun ij => a*1024 ≤ b*((32+ij.1)*(32+ij.2))

private theorem grid_sizes :
    possible.card=661 ∧ (certain 3 1).card=126 ∧ (certain 7 2).card=28 := by
  decide +kernel

private noncomputable def box (ij : ℕ×ℕ) := bin ij.1 ×ˢ bin ij.2

private theorem bin_unique {i j x : ℕ} (h : x∈bin i) (g : x∈bin j) : i=j := by
  obtain ⟨⟨l,r⟩,_⟩ := mem_bin.mp h
  obtain ⟨⟨l',r'⟩,_⟩ := mem_bin.mp g
  rcases lt_trichotomy i j with lt|eq|gt
  · have := edge_mono.monotone (show i+1≤j by omega)
    omega
  · exact eq
  · have := edge_mono.monotone (show j+1 ≤ i by omega)
    omega

private theorem disjoint_boxes (s : Finset (ℕ×ℕ)) : (↑s : Set (ℕ×ℕ)).PairwiseDisjoint box := by
  intro i _ j _ ne
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨p,q⟩ := mem_product.mp hx
  obtain ⟨p',q'⟩ := mem_product.mp hx'
  exact ne (Prod.ext (bin_unique p p') (bin_unique q q'))

private theorem bin_of {p : ℕ} (hp : p∈primes) : ∃ i<32, p∈bin i := by
  change p∈(Ico X (2*X)).filter Nat.Prime at hp
  simp only [mem_filter,mem_Ico] at hp
  obtain ⟨⟨lo,hi⟩,prime⟩ := hp
  rw [←scale] at lo hi
  have p32 : 32≤p/stepSize := (Nat.le_div_iff_mul_le step_pos).mpr lo
  have p64 : p/stepSize<64 := (Nat.div_lt_iff_lt_mul step_pos).mpr (by simpa [←mul_assoc] using hi)
  refine ⟨p/stepSize-32,by omega,mem_bin.mpr ⟨⟨?_,?_⟩,prime⟩⟩
  · simp only [edge,show 32+(p/stepSize-32)=p/stepSize by omega]
    exact Nat.div_mul_le_self _ _
  · simp only [edge,show 32+(p/stepSize-32+1)=p/stepSize+1 by omega]
    rw [Nat.mul_comm]
    exact Nat.lt_mul_div_succ _ step_pos

private theorem bin_in_primes {i p : ℕ} (hi : i<32) (hp : p∈bin i) : p∈primes := by
  obtain ⟨⟨lo,up⟩,pr⟩ := mem_bin.mp hp
  exact mem_filter.mpr ⟨mem_Ico.mpr ⟨(size_edge hi.le).1.trans lo,
    up.trans_le (size_edge (show i+1≤32 by omega)).2⟩,pr⟩

attribute [local irreducible] ordered primes sample eligible bin stepSize X

private theorem upper_cover : ordered (fun _ => True) ⊆ possible.biUnion box := by
  intro z hz
  obtain ⟨pa,qa,_,full,_⟩ := (mem_ordered (E:=fun _ => True) (z:=z)).mp hz
  obtain ⟨i,hi,pi⟩ := bin_of pa
  obtain ⟨j,hj,qj⟩ := bin_of qa
  have prod := Nat.mul_lt_mul_of_lt_of_le (mem_bin.mp pi).1.2 (mem_bin.mp qj).1.2.le
    (Nat.zero_lt_of_lt (mem_bin.mp qj).1.2)
  have cut : 2048<(33+i)*(33+j) := by
    by_contra! small
    have h := Nat.mul_le_mul_right (stepSize^2) small
    rw [←scale] at full
    dsimp only [edge] at prod
    nlinarith only [h,full,prod]
  exact mem_biUnion.mpr ⟨(i,j),mem_filter.mpr
    ⟨mem_product.mpr ⟨mem_range.mpr hi,mem_range.mpr hj⟩,cut⟩,mem_product.mpr ⟨pi,qj⟩⟩

private theorem upper_box (analytic : AxlerEndpoints) {ij : ℕ×ℕ} (h : ij∈possible) :
    (box ij).card ≤ (stepSize/708)^2 := by
  have hi : ij.1<32 := mem_range.mp (mem_product.mp (mem_filter.mp h).1).1
  have hj : ij.2<32 := mem_range.mp (mem_product.mp (mem_filter.mp h).1).2
  rw [box,card_product,sq]
  exact Nat.mul_le_mul (bin_count analytic hi).2 (bin_count analytic hj).2

private theorem upper (analytic : AxlerEndpoints) :
    2*eligible.card ≤ 661*(stepSize/708)^2 := by
  calc
    2*eligible.card = (ordered (fun _ => True)).card := by rw [eligible, two_orders]
    _ ≤ (possible.biUnion box).card := card_le_card upper_cover
    _ ≤ possible.card*(stepSize/708)^2 :=
      card_biUnion_le_card_mul possible box _ (fun _ h => upper_box analytic h)
    _ = 661*(stepSize/708)^2 := congrArg (fun z => z*(stepSize/708)^2) grid_sizes.1

private theorem lower {a b k : ℕ} (analytic : AxlerEndpoints)
    (event : ∀ n, a*X^2 ≤ b*n → 2*X^2≤n ∧ k*partnerWidth X n < ratioWidth n) :
    (certain a b).card*(stepSize/711)^2 ≤
      2*(sample (fun n => k*partnerWidth X n < ratioWidth n)).card + X := by
  let E := fun n => k*partnerWidth X n < ratioWidth n
  have inc : (certain a b).biUnion box ⊆ ordered E ∪ primes.diag := by
    intro z hz
    obtain ⟨ij,h,boxm⟩ := mem_biUnion.mp hz
    obtain ⟨base,threshold⟩ := mem_filter.mp h
    obtain ⟨i,j⟩ := mem_product.mp base
    obtain ⟨p,q⟩ := mem_product.mp boxm
    have ip := bin_in_primes (mem_range.mp i) p
    have jq := bin_in_primes (mem_range.mp j) q
    by_cases same : z.1=z.2
    · exact mem_union_right _ (mem_diag.mpr ⟨ip,same⟩)
    have lim := Nat.mul_le_mul (mem_bin.mp p).1.1 (mem_bin.mp q).1.1
    change a*1024 ≤ b*((32+ij.1)*(32+ij.2)) at threshold
    have h1 := Nat.mul_le_mul_right (stepSize^2) threshold
    have h2 := Nat.mul_le_mul_left b lim
    have enough : a*X^2≤b*(z.1*z.2) := by
      rw [←scale]
      dsimp only [edge] at h2
      nlinarith only [h1,h2]
    obtain ⟨size,ok⟩ := event _ enough
    exact mem_union_left _ (mem_ordered.mpr ⟨ip,jq,same,size,ok⟩)
  have size := card_nsmul_le_sum (certain a b) (fun ij => (box ij).card) ((stepSize/711)^2) (by
    intro ij h
    obtain ⟨i,j⟩ := mem_product.mp (mem_filter.mp h).1
    simp only [box,card_product,sq]
    exact Nat.mul_le_mul (bin_count analytic (mem_range.mp i)).1 (bin_count analytic (mem_range.mp j)).1)
  rw [nsmul_eq_mul,←card_biUnion (disjoint_boxes _)] at size
  have top : primes.card≤X := by
    rw [primes]
    exact (card_filter_le _ _).trans (by rw [Nat.card_Ico]; omega)
  have le := (size.trans (card_le_card inc)).trans (card_union_le ..)
  rw [two_orders,diag_card] at le
  exact le.trans (Nat.add_le_add_left top _)

/-- With distinct 1024-bit primes sampled uniformly among full 2048-bit products,
more than 18.9% have less than half the candidate count and more than 4.2% have
less than one quarter. The only analytic input is the cited unconditional theta
bound at the specified endpoints. The sets here use sorted prime pairs. -/
theorem population (analytic : AxlerEndpoints) :
    189*eligible.card < 1000*(sample (fun n => 2*partnerWidth X n < ratioWidth n)).card ∧
    42*eligible.card < 1000*(sample (fun n => 4*partnerWidth X n < ratioWidth n)).card := by
  have top := upper analytic
  have big : 1000≤X := by decide +kernel
  have first := lower (a:=3) (b:=1) (k:=2) analytic (by
    intro n hn
    rw [one_mul] at hn
    exact ⟨by omega,(width_savings big hn).1⟩)
  have next := lower (a:=7) (b:=2) (k:=4) analytic (by
    intro n hn
    have base : 3*X^2≤n := by omega
    exact ⟨by omega,(width_savings big base).2 hn⟩)
  rw [grid_sizes.2.1] at first
  rw [grid_sizes.2.2] at next
  have a : 189*(661*(stepSize/708)^2)+1000*X < 1000*(126*(stepSize/711)^2) := by decide +kernel
  have b : 42*(661*(stepSize/708)^2)+1000*X < 1000*(28*(stepSize/711)^2) := by decide +kernel
  constructor <;> omega

private def excess (n : ℕ) := n-2*X^2
private def credit (ij : ℕ×ℕ) := (32+ij.1)*(32+ij.2)-2048

/-- Each fully eligible square contributes its lower product corner above the full-size
cutoff, measured in units of (X/32)². -/
private theorem credits : ∑ ij∈certain 2 1, credit ij = 373061 := by decide +kernel

private theorem credit_box {ij z : ℕ×ℕ} (h : z∈box ij) :
    credit ij*stepSize^2 ≤ excess (z.1*z.2) := by
  obtain ⟨p,q⟩ := mem_product.mp h
  have bound := Nat.mul_le_mul (mem_bin.mp p).1.1 (mem_bin.mp q).1.1
  dsimp only [edge] at bound
  simp only [credit,excess]
  by_cases low : (32+ij.1)*(32+ij.2)≤2048
  · simp [Nat.sub_eq_zero_of_le low]
  have eq : ((32+ij.1)*(32+ij.2)-2048)+2048=(32+ij.1)*(32+ij.2) := by omega
  have h' := congrArg (· *stepSize^2) eq
  rw [←scale]
  have : ((32+ij.1)*(32+ij.2)-2048)*stepSize^2 + 2*(32*stepSize)^2 ≤ z.1*z.2 := by
    nlinarith only [h',bound]
  omega

private theorem weighted_cover : (certain 2 1).biUnion box ⊆ ordered (fun _ => True) ∪ primes.diag := by
  intro z hz
  obtain ⟨ij,h,boxm⟩ := mem_biUnion.mp hz
  obtain ⟨base,threshold⟩ := mem_filter.mp h
  obtain ⟨i,j⟩ := mem_product.mp base
  obtain ⟨p,q⟩ := mem_product.mp boxm
  have ip := bin_in_primes (mem_range.mp i) p
  have jq := bin_in_primes (mem_range.mp j) q
  by_cases same : z.1=z.2
  · exact mem_union_right _ (mem_diag.mpr ⟨ip,same⟩)
  have lim := Nat.mul_le_mul (mem_bin.mp p).1.1 (mem_bin.mp q).1.1
  change 2*1024 ≤ 1*((32+ij.1)*(32+ij.2)) at threshold
  have h1 := Nat.mul_le_mul_right (stepSize^2) threshold
  have enough : 2*X^2≤z.1*z.2 := by
    rw [←scale]
    dsimp only [edge] at lim
    nlinarith only [h1,lim]
  exact mem_union_left _ (mem_ordered.mpr ⟨ip,jq,same,enough,trivial⟩)

private theorem price_sum {f : ℕ×ℕ→ℕ} (G : Finset (ℕ×ℕ)) (c : ℕ×ℕ→ℕ)
    {K P : ℕ} (price : ∑ ij∈G,c ij=P)
    (per : ∀ ij∈G, c ij*K ≤ ∑ z∈box ij, f z) :
    P*K ≤ ∑ z∈G.biUnion box, f z := by
  rw [←price,Finset.sum_mul,Finset.sum_biUnion (disjoint_boxes _)]
  exact sum_le_sum per

private theorem union_sum {ι : Type*} [DecidableEq ι] (s t : Finset ι) (f : ι→ℕ) :
    ∑ x∈s∪t, f x ≤ (∑ x∈s,f x)+(∑ x∈t,f x) :=
  le_trans (Nat.le_add_right _ _) (Finset.sum_union_inter (s₁:=s) (s₂:=t) (f:=f)).le

private def score (z : ℕ×ℕ) := excess (z.1*z.2)

private theorem unit_box_credit {ι : Type*} (F : Finset ι) (v : ι→ℕ) {L C H : ℕ}
    (card : L≤F.card) (each : ∀ z∈F, C*H ≤ v z) :
    C*(L*H) ≤ F.sum v := by
  calc
    _ = L*(C*H) := by ring
    _ ≤ F.card*(C*H) := Nat.mul_le_mul_right _ card
    _ = _ := (nsmul_eq_mul ..).symm
    _ ≤ _ := card_nsmul_le_sum F v (C*H) each

private theorem unit_sum_upper {ι : Type*} (F : Finset ι) (v : ι→ℕ) {L B : ℕ}
    (card : F.card≤B) (each : ∀ z∈F, v z≤(2*B)^2) (endp : 4*B^3=L) :
    F.sum v ≤ L := by
  calc
    _ ≤ _ := sum_le_card_nsmul F v ((2*B)^2) each
    _ = F.card*((2*B)^2) := nsmul_eq_mul ..
    _ ≤ B*((2*B)^2) := Nat.mul_le_mul_right _ card
    _ = L := by rw [←endp]; ring

private theorem box_credit (analytic : AxlerEndpoints) (ij : ℕ×ℕ) (hh : ij∈certain 2 1) :
    credit ij*((stepSize/711)^2*stepSize^2) ≤ ∑ z∈box ij, score z := by
  obtain ⟨i,j⟩ := mem_product.mp (mem_filter.mp hh).1
  have lo : (stepSize/711)^2≤(box ij).card := by
    simp only [box,card_product,sq]
    exact Nat.mul_le_mul (bin_count analytic (mem_range.mp i)).1
      (bin_count analytic (mem_range.mp j)).1
  exact unit_box_credit (box ij) score lo (fun _ hz => credit_box hz)

private theorem diagonal_credit : ∑ z∈primes.diag, score z ≤ 4*X^3 := by
  have count : primes.card≤X := by
    rw [primes]
    exact (card_filter_le _ _).trans (by rw [Nat.card_Ico]; omega)
  apply unit_sum_upper primes.diag score (by simpa only [diag_card] using count) _ rfl
  intro z hz
  obtain ⟨p,same⟩ := mem_diag.mp hz
  have pair := mem_Ico.mp (mem_filter.mp (show z.1∈(Ico X (2*X)).filter Nat.Prime by simpa [primes] using p)).1
  dsimp only [score,excess]
  exact (Nat.sub_le _ _).trans (by rw [←same,←sq]; exact Nat.pow_le_pow_left pair.2.le _)

private theorem priced_union {ι : Type*} [DecidableEq ι] (S D T : Finset ι) (v : ι→ℕ)
    {p u h m : ℕ} (tiles : p*(u*h) ≤ T.sum v) (incl : T⊆S∪D) (diag : D.sum v ≤ m) :
    p*u*h ≤ S.sum v + m := by
  calc
    _ = _ := Nat.mul_assoc p u h
    _ ≤ _ := tiles
    _ ≤ _ := sum_le_sum_of_subset (f:=v) incl
    _ ≤ _ := union_sum S D v
    _ ≤ _ := Nat.add_le_add_left diag _

private theorem weighted_boxes (analytic : AxlerEndpoints) :
    373061*(stepSize/711)^2*stepSize^2 ≤ (ordered (fun _ => True)).sum score+4*X^3 :=
  priced_union (ordered (fun _ => True)) primes.diag ((certain 2 1).biUnion box) score
    (price_sum (f:=score) (certain 2 1) credit credits (box_credit analytic))
    weighted_cover diagonal_credit

private theorem two_sums (f : (ℕ×ℕ)→ℕ) (sym : ∀z, f z=f z.swap) : (ordered (fun _ => True)).sum f =
    2*eligible.sum f := by
  let V := ordered (fun _ => True)
  let lowerSide (z : ℕ×ℕ) := z.1<z.2
  have flip {z : ℕ×ℕ} (h : z∈V) : z.swap∈V := by
    obtain ⟨p,q,ne,size,_⟩ := (mem_ordered (E:=fun _ => True) (z:=z)).mp h
    exact mem_ordered.mpr ⟨q,p,ne.symm,by simpa only [Prod.swap,mul_comm] using size,trivial⟩
  have same : ∑ z∈V.filter lowerSide, f z = ∑ z∈V.filter (fun z => ¬lowerSide z), f z := by
    apply sum_nbij' Prod.swap Prod.swap
    · intro z hz
      obtain ⟨h,l⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨flip h,by dsimp only [lowerSide,Prod.swap] at *; omega⟩
    · intro z hz
      obtain ⟨h,l⟩ := mem_filter.mp hz
      have ne := ((mem_ordered (E:=fun _ => True) (z:=z)).mp h).2.2.1
      exact mem_filter.mpr ⟨flip h,by dsimp only [lowerSide,Prod.swap] at *; omega⟩
    · intros; rfl
    · intros; rfl
    · intro z _; exact sym z
  have partition := sum_filter_add_sum_filter_not V lowerSide f
  have matchSets : V.filter lowerSide=eligible := by rw [eligible,sample]
  change ∑ z∈V, f z = 2*∑ z∈eligible, f z
  rw [←matchSets,←partition,←same,two_mul]

/-- The tangent (5s−8B)² ≥ 0 converts the cost of the two inclusive intervals into
a linear inequality in n. The constant term includes both endpoint roundings. -/
private theorem width_envelope {B n : ℕ} (size : 200000≤B) (low : 2*B^2≤n)
    (fits : ShortPascalRow.lower n B ≤ n.sqrt+1) :
    80000*B*partnerWidth B n + 20075*(n-2*B^2) ≤ 56000*B*ratioWidth n + 10859*B^2 := by
  obtain ⟨limit,ratio⟩ := endpoints (by omega : 0<B) (show 0<n by nlinarith [Nat.zero_le ((B-1)^2)])
  let s := n.sqrt
  have sq : s^2≤n := Nat.sqrt_le' n
  have tangent : 80*B*s≤25*n+64*B^2 := by
    zify at sq ⊢
    nlinarith only [sq,sq_nonneg (5*(s:ℤ)-8*B)]
  have a : partnerWidth B n + ShortPascalRow.lower n B=s+1 := Nat.sub_add_cancel fits
  have b : s+1≤ratioWidth n+ceilSqrt ((n+1)/2) := by unfold ratioWidth; dsimp [s]; omega
  change 100*ceilSqrt ((n+1)/2) ≤ 71*(s+1)+100 at ratio
  have m1 := congrArg (B*·) a
  have m2 := Nat.mul_le_mul_left B b
  have m3 := Nat.mul_le_mul_left B ratio
  have padding := Nat.mul_le_mul_right B size
  have sub := Nat.sub_add_cancel low
  nlinarith only [tangent,limit,m1,m2,m3,padding,sub,Nat.zero_le B]

private theorem aggregate_moment (analytic : AxlerEndpoints) :
    10859*X^2*eligible.card < 20075*(eligible.sum score) := by
  have top := upper analytic
  have bottom := weighted_boxes analytic
  rw [two_sums score (by intro z; dsimp only [score,Prod.swap]; rw [mul_comm])] at bottom
  have constant : 10859*X^2*(661*(stepSize/708)^2) + 20075*(4*X^3) <
      20075*(373061*(stepSize/711)^2*stepSize^2) := by decide +kernel
  have u := Nat.mul_le_mul_left (10859*X^2) top
  have v := Nat.mul_le_mul_left 20075 bottom
  nlinarith only [constant,u,v]

/-- The inclusive number of candidates charged to a pair by the bit-width bound. -/
def partnerPrice (z : ℕ×ℕ) := partnerWidth X (z.1*z.2)
/-- The inclusive number charged to the same pair by the ratio-only bound. -/
def ratioPrice (z : ℕ×ℕ) := ratioWidth (z.1*z.2)

private theorem sample_envelope (z : ℕ×ℕ) (hz : z∈eligible) : 80000*X*partnerPrice z +
    20075*score z ≤ 56000*X*ratioPrice z+10859*X^2 := by
  rw [eligible,sample] at hz
  obtain ⟨ord,hlt⟩ := mem_filter.mp hz
  obtain ⟨p,q,_,bounded,_⟩ := (mem_ordered (E:=fun _ => True) (z:=z)).mp ord
  have pm : z.1∈(Ico X (2*X)).filter Nat.Prime := by simpa only [primes] using p
  have qm : z.2∈(Ico X (2*X)).filter Nat.Prime := by simpa only [primes] using q
  obtain ⟨⟨pl,_⟩,pp⟩ := (show (_∧_)∧_ by simpa only [mem_filter,mem_Ico] using pm)
  obtain ⟨⟨_,qh⟩,qp⟩ := (show (_∧_)∧_ by simpa only [mem_filter,mem_Ico] using qm)
  have ps := pp.pos
  have bot := Nat.le_sqrt.mpr (Nat.mul_le_mul_left z.1 hlt.le)
  have den : 0<2*X-1 := by decide +kernel
  have small : (z.1*z.2-1)/(2*X-1)<z.1 := (Nat.div_lt_iff_lt_mul den).mpr (by
    have lim := Nat.mul_le_mul_left z.1 (show z.2≤2*X-1 by omega)
    have pos := Nat.mul_pos ps qp.pos
    omega)
  apply width_envelope (by decide +kernel) bounded
  exact le_trans (max_le pl (by omega)) (Nat.le_succ_of_le bot)

private theorem weighted_conclusion {ι : Type*} (S : Finset ι) {B : ℕ} (pos : 0<B)
    (P R E : ι→ℕ) (mean : 10859*B^2*S.card < 20075*S.sum E)
    (costs : ∀ z∈S, 80000*B*P z+20075*E z ≤ 56000*B*R z+10859*B^2) :
    10*S.sum P < 7*S.sum R := by
  have allCosts := sum_le_sum costs
  simp only [sum_add_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] at allCosts
  have final : 8000*B*(10*∑ z∈S,P z) < 8000*B*(7*∑ z∈S,R z) := by
    nlinarith only [mean,allCosts]
  exact (Nat.mul_lt_mul_left (Nat.mul_pos (by decide) pos)).mp final

/-- Across the same uniform eligible population, summing the inclusive candidate
counts after using both prime bit lengths retains less than 70% of the original
total. This bounds expected interval length, separately from running time. -/
theorem aggregate (analytic : AxlerEndpoints) :
    10*eligible.sum partnerPrice <
    7*eligible.sum ratioPrice := by
  exact weighted_conclusion eligible (by decide +kernel : 0<X)
    partnerPrice ratioPrice score (aggregate_moment analytic) sample_envelope

end PrimeFactors.ShortRowPopulation
