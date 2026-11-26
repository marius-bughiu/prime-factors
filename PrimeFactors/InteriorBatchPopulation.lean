import PrimeFactors.SharedMultiplierPopulation
import PrimeFactors.WeightedTracePrefix
import Mathlib.Tactic

/-! Finite comparison of one extra ordinary batch and an interior multiplier
batch after the same ordinary prefix. The analytic input is a list of
prime-count bounds on explicit intervals, isolated in Counts. -/
namespace PrimeFactors.InteriorBatchPopulation
open Finset Real

set_option exponentiation.threshold 8192
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

abbrev U : ℕ := 2^1024
abbrev B : ℕ := 2^40
abbrev V : ℕ := 2^532
abbrev m : ℕ := 4096

def bin (p q : ℕ) : Prop := 9*U^2≤16*(p*q) ∧ 8*(p*q)≤5*U^2

/-- All possible ordinary hits after m*B admitted traces and at most B+1 more.
Each complete period has 4, 2 or 1 residue and mean step 6, 12 or 24. -/
def Tail (p q step : ℕ) : Prop :=
  (step*m*B:ℕ) ≤ (sqrt q-sqrt p)^2 ∧
    (sqrt q-sqrt p)^2 ≤ (step*((m+1)*B)+24:ℕ)

def close (p q : ℕ) : Prop := 3*p≤2*q+2*V ∧ 2*q≤3*p+2*V

noncomputable def firstPrimes (lo hi : ℕ) : Finset ℕ := (Icc lo hi).filter Nat.Prime
noncomputable def interior := firstPrimes (79*(U/128)) (82*(U/128))
noncomputable def outer := firstPrimes (47*(U/64)) (51*(U/64))
noncomputable def neighbors (p : ℕ) : Finset ℕ := (Icc ((3*p+1)/2-V) (3*p/2+V)).filter Nat.Prime

attribute [local irreducible] firstPrimes interior outer neighbors

private theorem in_neighbors {p q : ℕ} (hm : q∈neighbors p) : q.Prime ∧ close p q := by
  rw [neighbors] at hm
  obtain ⟨interval,pr⟩ := mem_filter.mp hm
  obtain ⟨lo,hi⟩ := mem_Icc.mp interval
  exact ⟨pr,by unfold close; omega⟩

/-- This entire strip of actual prime partners lies inside the public product
bin, splits at k=6 in the first B integer traces, and misses even the largest
ordinary prefix in the comparison. -/
theorem interior_split {p q : ℕ} (hp : p∈interior) (hq : q∈neighbors p) :
    bin p q ∧ 2^1023≤p ∧ p<q ∧ q<U ∧
    ((3*p+2*q:ℕ):ℝ)<2*sqrt (6*(p:ℝ)*q)+B ∧
    ((24*((m+1)*B)+24:ℕ):ℝ)<(sqrt q-sqrt p)^2 := by
  rw [interior,firstPrimes] at hp
  obtain ⟨range,_⟩ := mem_filter.mp hp
  obtain ⟨pl,ph⟩ := mem_Icc.mp range
  obtain ⟨_,cl,ch⟩ := in_neighbors hq
  have scale : U=128*(U/128) := by decide +kernel
  have tiny : V*128≤U := by decide +kernel
  have pbound : 2^1023≤p := le_trans (by decide +kernel) pl
  have ranges : 117*(U/128)≤q ∧ q≤124*(U/128) := by omega
  have prodlo := Nat.mul_le_mul pl ranges.1
  have prodhi := Nat.mul_le_mul ph ranges.2
  have lo : 9*U^2≤16*(p*q) := (by decide +kernel : 9*U^2≤16*((79*(U/128))*(117*(U/128)))).trans (Nat.mul_le_mul_left 16 prodlo)
  have hi : 8*(p*q)≤5*U^2 := (Nat.mul_le_mul_left 8 prodhi).trans (by decide +kernel)
  have qu : q<U := by omega
  have ordered : p<q := by omega
  have pu : p<U := ordered.trans qu
  have cl' : 3*(p:ℝ)≤2*q+2*V := by exact_mod_cast cl
  have ch' : 2*(q:ℝ)≤3*p+2*V := by exact_mod_cast ch
  have err : |3*(p:ℝ)-2*q|≤2*V := abs_le.mpr ⟨by linarith only [ch'],by linarith only [cl']⟩
  have errsq := sq_le_sq.mpr (err.trans_eq (abs_of_nonneg (by positivity)).symm)
  have BV : (V:ℝ)^2=U*B := by norm_num
  have sump : 3*(U:ℝ) ≤ 3*p+2*q := by exact_mod_cast (show 3*U ≤ 3*p+2*q by omega)
  have root := sq_sqrt (by positivity : (0:ℝ)≤6*(p:ℝ)*q)
  have large : (B:ℝ)<U := by norm_num
  have trace : (3*p+2*q:ℝ)<2*sqrt (6*p*q)+B := by
    apply lt_of_not_ge
    intro wrong
    have high : 2*sqrt (6*(p:ℝ)*q) ≤ 3*p+2*q-B := le_sub_iff_add_le.mpr wrong
    have cmp := pow_le_pow_left₀ (by positivity) high 2
    nlinarith only [cmp,root,errsq,BV,mul_le_mul_of_nonneg_left sump (by positivity : (0:ℝ)≤B),
      mul_lt_mul_of_pos_right large (by norm_num : (0:ℝ)<B)]
  have gap : U/4≤q-p := by omega
  have ir : (U:ℝ)/4 ≤ (q:ℝ)-p := by
    have h : (U:ℝ)+4*p≤4*q := by exact_mod_cast (show U+4*p≤4*q by omega)
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    linarith only [h]
  have qroot : sqrt (q:ℝ) ≤ (2:ℝ)^512 := sqrt_le_iff.mpr ⟨by positivity,by exact_mod_cast qu.le⟩
  have proot : sqrt (p:ℝ) ≤ (2:ℝ)^512 := sqrt_le_iff.mpr ⟨by positivity,by exact_mod_cast pu.le⟩
  have nonneg : 0≤sqrt (q:ℝ)-sqrt p := sub_nonneg.mpr (sqrt_le_sqrt (by exact_mod_cast ordered.le))
  have diff : (q:ℝ)-p=(sqrt q-sqrt p)*(sqrt q+sqrt p) := by nlinarith only [sq_sqrt (Nat.cast_nonneg q),sq_sqrt (Nat.cast_nonneg p)]
  have rad : (2:ℝ)^508 ≤ sqrt q-sqrt p := by
    have mult := mul_le_mul_of_nonneg_left (add_le_add qroot proot) nonneg
    rw [←diff] at mult
    norm_num [U] at ir ⊢
    linarith only [ir,mult]
  refine ⟨⟨lo,hi⟩,pbound,ordered,qu,by exact_mod_cast trace,?_⟩
  exact lt_of_lt_of_le (by norm_num [m,B]) (pow_le_pow_left₀ (by positivity) rad 2)

/-- The product-only integer interval contains a concrete label whose
discriminant is a square and whose positive-root gcd gives one of the primes. -/
theorem interior_witness {p q : ℕ} (hp : p∈interior) (hq : q∈neighbors p) :
    let n := p*q
    let first := ⌈2*sqrt (6*(n:ℝ))⌉₊
    ∃ S∈Ico first (first+B),
      let d := (S^2-24*n).sqrt
      S^2=24*n+d^2 ∧ (n.gcd ((S+d)/2)=p ∨ n.gcd ((S+d)/2)=q) := by
  let S := 3*p+2*q
  have info := interior_split hp hq
  obtain ⟨_,pl,pq,_,trace,_⟩ := info
  have pp : p.Prime := (mem_filter.mp (by simpa only [interior,firstPrimes] using hp)).2
  have qp := (in_neighbors hq).1
  have cop (l : ℕ) (pr : l.Prime) (large : 6<l) : Nat.Coprime 6 l :=
    (pr.coprime_iff_not_dvd.mpr (fun d => (not_le_of_gt large) (Nat.le_of_dvd (by decide) d))).symm
  have coprime : Nat.Coprime 6 (p*q) := Nat.Coprime.mul_right (cop p pp (by omega)) (cop q qp (by omega))
  have identity := multiplier_sum_square p q 3 2
  change S^2=24*(p*q)+(3*p).dist (2*q)^2 at identity
  have low : 2*sqrt (6*((p*q:ℕ):ℝ)) ≤ S := by
    have sq := sq_sqrt (by positivity : (0:ℝ)≤6*((p*q:ℕ):ℝ))
    have diff : (S:ℝ)^2 ≥ 24*((p*q:ℕ):ℝ) := by exact_mod_cast (show 24*(p*q)≤S^2 by omega)
    nlinarith only [sq,diff,show (0:ℝ)≤S by positivity,sqrt_nonneg (6*((p*q:ℕ):ℝ))]
  let f := ⌈2*sqrt (6*((p*q:ℕ):ℝ))⌉₊
  have top : (S:ℝ)<(f:ℝ)+B := by
    apply lt_of_lt_of_le _ (add_le_add_right (Nat.le_ceil _) _)
    change ((3*p+2*q:ℕ):ℝ)<_
    simpa only [Nat.cast_mul,mul_assoc] using trace
  have topNat : S < f+B := by exact_mod_cast top
  refine ⟨S,mem_Ico.mpr ⟨Nat.ceil_le.mpr low,topNat⟩,?_,?_⟩
  · rw [identity,Nat.add_sub_cancel_left,Nat.sqrt_eq']
  · exact WeightedTracePrefix.shared_gcd rfl (a:=3) (b:=2) (by decide) coprime rfl

private theorem sqrt_span {step : ℕ} (hs : step=6 ∨ step=12 ∨ step=24) :
    sqrt ((step*((m+1)*B)+24:ℕ):ℝ)-sqrt ((step*m*B:ℕ):ℝ) ≤ (2:ℝ)^20/24 := by
  rcases hs with rfl|rfl|rfl
  · have lo : (164382474:ℝ)≤sqrt ((6*m*B:ℕ):ℝ) := by apply Real.le_sqrt (by norm_num) (by positivity) |>.mpr; norm_num [m,B]
    have hi : sqrt ((6*((m+1)*B)+24:ℕ):ℝ)≤164402540 := by apply sqrt_le_iff.mpr; norm_num [m,B]
    exact (sub_le_sub hi lo).trans (by norm_num)
  · have lo : (232471924:ℝ)≤sqrt ((12*m*B:ℕ):ℝ) := by apply Real.le_sqrt (by norm_num) (by positivity) |>.mpr; norm_num [m,B]
    have hi : sqrt ((12*((m+1)*B)+24:ℕ):ℝ)≤232500301 := by apply sqrt_le_iff.mpr; norm_num [m,B]
    exact (sub_le_sub hi lo).trans (by norm_num)
  · have lo : (328764948:ℝ)≤sqrt ((24*m*B:ℕ):ℝ) := by apply Real.le_sqrt (by norm_num) (by positivity) |>.mpr; norm_num [m,B]
    have hi : sqrt ((24*((m+1)*B)+24:ℕ):ℝ)≤328805079 := by apply sqrt_le_iff.mpr; norm_num [m,B]
    exact (sub_le_sub hi lo).trans (by norm_num)


private theorem tail_roots {p q s : ℕ} (pq : p≤q) (tail : Tail p q s) :
    sqrt ((s*m*B:ℕ):ℝ) ≤ sqrt q-sqrt p ∧
    sqrt q-sqrt p ≤ sqrt ((s*((m+1)*B)+24:ℕ):ℝ) := by
  have pos : 0≤sqrt (q:ℝ)-sqrt p := sub_nonneg.mpr (sqrt_le_sqrt (by exact_mod_cast pq))
  exact ⟨sqrt_le_iff.mpr ⟨pos,tail.1⟩, (Real.le_sqrt pos (by positivity)).mpr tail.2⟩

/-- The prime partners in any one of the three ordinary shells are this
close, irrespective of the residue of p or the phase of the leading label. -/
theorem tail_width {p q r s : ℕ} (pq : p≤q) (qr : q≤r) (ru : r≤U)
    (hs : s=6 ∨ s=12 ∨ s=24) (left : Tail p q s) (right : Tail p r s) :
    12*(r-q)≤V := by
  have low := (tail_roots pq left).1
  have hi := (tail_roots (pq.trans qr) right).2
  have span := sqrt_span hs
  have pr : sqrt (q:ℝ)≤sqrt r := sqrt_le_sqrt (by exact_mod_cast qr)
  have rmax : sqrt (r:ℝ)≤(2:ℝ)^512 := sqrt_le_iff.mpr ⟨by positivity,by exact_mod_cast ru⟩
  have lens : sqrt (r:ℝ)-sqrt q≤(2:ℝ)^20/24 := by
    have trans := (sub_le_sub hi low).trans span
    simpa only [sub_sub_sub_cancel_right] using trans
  have maxsum : sqrt (r:ℝ)+sqrt q≤2*2^512 := by linarith only [pr,rmax]
  have prod := mul_le_mul lens maxsum (by positivity : 0≤sqrt (r:ℝ)+sqrt q) (by positivity)
  have scale : ((2:ℝ)^20/24)*(2*2^512)=V/12 := by norm_num [V]
  rw [scale] at prod
  rw [mul_comm,←sq_sub_sq,sq_sqrt (Nat.cast_nonneg r),sq_sqrt (Nat.cast_nonneg q)] at prod
  have bound : 12*((r:ℝ)-q)≤V := by simpa only [mul_comm] using (le_div_iff₀ (by norm_num : (0:ℝ)<12)).mp prod
  rw [←Nat.cast_sub qr] at bound
  exact_mod_cast bound

private theorem ordinary_first {p q s : ℕ} (pq : p≤q) (qu : q≤U) (pp : p.Prime)
    (hs : s=6 ∨ s=12 ∨ s=24) (hb : bin p q) (tail : Tail p q s) : p∈outer := by
  have sqhi : sqrt ((s*((m+1)*B)+24:ℕ):ℝ) ≤ (2:ℝ)^29 := by
    apply sqrt_le_iff.mpr; rcases hs with rfl|rfl|rfl <;> norm_num [m,B]
  have rho := (tail_roots pq tail).2.trans sqhi
  have qmax : sqrt (q:ℝ) ≤ (2:ℝ)^512 := sqrt_le_iff.mpr ⟨by positivity,by exact_mod_cast qu⟩
  have pmax := (sqrt_le_sqrt (by exact_mod_cast pq : (p:ℝ)≤q)).trans qmax
  have prod := mul_le_mul rho (add_le_add qmax pmax) (by positivity : 0≤sqrt (q:ℝ)+sqrt p) (by positivity)
  have cap : (2:ℝ)^29*(2^512+2^512) < (U/64:ℕ) := by norm_num [U]
  have gap : (q:ℝ)<p+(U/64:ℕ) := by nlinarith only [prod,cap,sq_sqrt (Nat.cast_nonneg q),sq_sqrt (Nat.cast_nonneg p)]
  have gn : q<p+U/64 := by exact_mod_cast gap
  rw [outer,firstPrimes]
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_,?_⟩,pp⟩
  · by_contra! below
    have qlo : q<48*(U/64) := by omega
    have prodlo := Nat.mul_le_mul below.le qlo.le
    have bad : 16*((47*(U/64))*(48*(U/64))) < 9*U^2 := by decide +kernel
    exact (not_lt_of_ge hb.1) ((Nat.mul_le_mul_left 16 prodlo).trans_lt bad)
  · by_contra! above
    have prodhi := Nat.mul_le_mul above.le (above.le.trans pq)
    have bad : 5*U^2<8*((51*(U/64))^2) := by decide +kernel
    exact (not_lt_of_ge hb.2) (bad.trans_le (by simpa only [sq] using Nat.mul_le_mul_left 8 prodhi))

/-- Rounded consequences of the two-sided prime-counting error under RH.
The proof below assumes these explicit interval counts. -/
structure Counts : Prop where
  lower (lo hi : ℕ) (loBound : U/2≤lo) (order : lo≤hi) (hiBound : hi≤U) :
    hi-lo ≤ 710*((firstPrimes lo hi).card+57*2^512)
  upper (lo hi : ℕ) (loBound : U/2≤lo) (order : lo≤hi) (hiBound : hi≤U) :
    709*(firstPrimes lo hi).card ≤ hi-lo+1+709*(57*2^512)

private theorem first_count (C : Counts) : U<31000*interior.card ∧ 11000*outer.card≤U := by
  have lo := C.lower (79*(U/128)) (82*(U/128)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hi := C.upper (47*(U/64)) (51*(U/64)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [←interior] at lo
  rw [←outer] at hi
  norm_num [U] at lo hi ⊢
  omega

private theorem near_count (C : Counts) {p : ℕ} (hp : p∈interior) : V<365*(neighbors p).card := by
  rw [interior,firstPrimes] at hp
  obtain ⟨h,_⟩ := mem_filter.mp hp
  obtain ⟨pl,pu⟩ := mem_Icc.mp h
  let l := (3*p+1)/2-V
  let u := 3*p/2+V
  norm_num [U] at pl pu
  have large : U/2≤l := by dsimp [l]; norm_num [U,V]; omega
  have room : l≤u := by dsimp [l,u]; norm_num [V]; omega
  have top : u≤U := by dsimp [u]; norm_num [U,V]; omega
  have size : 2*V≤u-l+1 := by dsimp [l,u]; norm_num [V]; omega
  have lo := C.lower l u large room top
  have same : firstPrimes l u = neighbors p := by rw [firstPrimes,neighbors]
  rw [same] at lo
  norm_num [V] at size ⊢
  omega

private theorem shell_count (C : Counts) {p s : ℕ} (hs : s=6 ∨ s=12 ∨ s=24)
    (Q : Finset ℕ) (hit : ∀ q∈Q, U/2≤q ∧ p≤q ∧ q≤U ∧ q.Prime ∧ Tail p q s) :
    5700*Q.card≤V := by
  rcases Q.eq_empty_or_nonempty with rfl|ne
  · simp
  let l := Q.min' ne
  let u := Q.max' ne
  obtain ⟨lb,pl,_,_,tl⟩ := hit l (Q.min'_mem ne)
  obtain ⟨_,_,ub,_,tu⟩ := hit u (Q.max'_mem ne)
  have order : l≤u := Q.min'_le _ (Q.max'_mem ne)
  have span := tail_width pl order ub hs tl tu
  have subset : Q ⊆ firstPrimes l u := by
    rw [firstPrimes]
    exact fun q hq => mem_filter.mpr ⟨mem_Icc.mpr ⟨Q.min'_le _ hq,Q.le_max' _ hq⟩,(hit q hq).2.2.2.1⟩
  have cap := C.upper l u lb order ub
  have cnt := card_le_card subset
  norm_num [V] at span ⊢
  omega

private theorem three_counts {a b c t v : ℕ} (cnt : t≤a+(b+c))
    (ha : 5700*a≤v) (hb : 5700*b≤v) (hc : 5700*c≤v) : 1900*t≤v := by omega

private theorem compare_counts {a b o w u v : ℕ} (lo : u<31000*a)
    (hi : 11000*b≤u) (lower : a*v≤365*w) (upper : 1900*o≤b*v) (vp : 0<v) :
    9*o<5*w := by
  nlinarith only [Nat.mul_lt_mul_of_pos_right lo vp, Nat.mul_le_mul_right v hi,
    Nat.mul_le_mul_left 31000 lower,Nat.mul_le_mul_left 11000 upper,Nat.zero_le o]

private theorem guaranteed_sum (P : Finset ℕ) (Q : ℕ → Finset ℕ) (v : ℕ)
    (each : ∀ p∈P, v < 365*(Q p).card) : P.card*v≤365*(P.sigma Q).card := calc
  _ = ∑ _p∈P, v := by simp
  _ ≤ ∑ p∈P, 365*(Q p).card := sum_le_sum fun p hp => (each p hp).le
  _ = _ := by rw [Finset.card_sigma,mul_sum]

private theorem ordinary_sum (P T : Finset ℕ) (pairs : Finset (ℕ×ℕ)) (row : ℕ → ℕ → Finset ℕ) (v : ℕ)
    (into : ∀ z∈pairs, z.1∈P ∧ ∃ s∈T, z.2∈row z.1 s)
    (size : ∀ p, 1900*(T.biUnion (row p)).card≤v) : 1900*pairs.card≤P.card*v := by
  let partners p := T.biUnion (row p)
  have cover : pairs ⊆ P.biUnion (fun p => (partners p).image (fun q => (p,q))) := by
    rintro ⟨p,q⟩ h
    obtain ⟨hp,s,hs,hq⟩ := into (p,q) h
    exact mem_biUnion.mpr ⟨p,hp,mem_image_of_mem _ (mem_biUnion.mpr ⟨s,hs,hq⟩)⟩
  have work : pairs.card ≤ ∑ p∈P, (partners p).card :=
    (card_le_card cover).trans (card_biUnion_le.trans (sum_le_sum fun _ _ => card_image_le))
  calc
    _ ≤ 1900*(∑ p∈P, (partners p).card) := Nat.mul_le_mul_left _ work
    _ = ∑ p∈P, 1900*(partners p).card := mul_sum _ _ _
    _ ≤ ∑ _p∈P, v := sum_le_sum (fun p _ => size p)
    _ = _ := by simp

theorem gain (C : Counts) (ordinary : Finset (ℕ×ℕ))
    (possible : ∀ z∈ordinary, U/2≤z.1 ∧ z.1≤z.2 ∧ z.2≤U ∧ z.1.Prime ∧ z.2.Prime ∧ bin z.1 z.2 ∧
      ∃ s∈({6,12,24}:Finset ℕ), Tail z.1 z.2 s) :
    9*ordinary.card < 5*(interior.sigma neighbors).card := by
  classical
  let room (p s : ℕ) := (ordinary.image Prod.snd).filter (fun q => (p,q)∈ordinary ∧ Tail p q s)
  let partners (p : ℕ) := ({6,12,24}:Finset ℕ).biUnion (room p)
  have row (p s : ℕ) (hs : s∈({6,12,24}:Finset ℕ)) : 5700*(room p s).card ≤ V := by
    apply shell_count C (by simpa using hs)
    intro q hq
    obtain ⟨_,h,t⟩ := mem_filter.mp hq
    obtain ⟨pl,pq,qu,_,qp,_,_⟩ := possible _ h
    exact ⟨pl.trans pq,pq,qu,qp,t⟩
  have size (p : ℕ) : 1900*(partners p).card≤V := by
    have cnt : (partners p).card ≤ ∑ s∈({6,12,24}:Finset ℕ), (room p s).card := card_biUnion_le
    have sum : (∑ s∈({6,12,24}:Finset ℕ), (room p s).card) = (room p 6).card + ((room p 12).card + (room p 24).card) := by simp
    exact three_counts (cnt.trans_eq sum) (row p 6 (by decide)) (row p 12 (by decide)) (row p 24 (by decide))
  have up : 1900*ordinary.card≤outer.card*V := by
    apply ordinary_sum outer {6,12,24} ordinary room V _ size
    rintro ⟨p,q⟩ h
    obtain ⟨_,pq,qu,pp,_,hb,s,hs,tail⟩ := possible _ h
    exact ⟨ordinary_first pq qu pp (by simpa using hs) hb tail,s,hs,
      mem_filter.mpr ⟨mem_image_of_mem Prod.snd h,h,tail⟩⟩
  exact compare_counts (first_count C).1 (first_count C).2 (guaranteed_sum interior neighbors V (fun p hp => near_count C (p:=p) hp)) up (by decide +kernel)

end PrimeFactors.InteriorBatchPopulation
