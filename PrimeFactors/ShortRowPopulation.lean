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

end PrimeFactors.ShortRowPopulation
