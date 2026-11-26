import PrimeFactors.CubicForcedParameters
import PrimeFactors.SquareRootPhasePopulation
import Mathlib.Tactic

/-! One public prediction of the Fermat midpoint. The sufficient error bound
and the population estimate concern ordinary products with no construction
assumption. -/
namespace PrimeFactors.CubicGapWindow
open Finset CubicForcedParameters
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

/-- Prediction of the half-gap between the prime factors. -/
noncomputable def gapGuess (n : ℕ) := ceilCube (4*n)+1

/-- Round the real square root to its nearest integer using an integer square root. -/
def roundSqrt (x : ℕ) := let s:=x.sqrt; if x≤s^2+s then s else s+1

noncomputable def midpoint (n : ℕ) := roundSqrt (n+(gapGuess n)^2)

/-- Candidate pair. A caller verifies its product and nontriviality. -/
noncomputable def readout (n : ℕ) : ℕ×ℕ :=
  let m := midpoint n
  let d := (m^2-n).sqrt
  (m-d,m+d)

def Within (d g E : ℕ) : Prop := d≤g+E ∧ g≤d+E

theorem rounded_band (x : ℕ) :
    (roundSqrt x)^2 ≤ x+roundSqrt x ∧ x≤(roundSqrt x)^2+roundSqrt x := by
  have lo : x.sqrt^2≤x := Nat.le_sqrt'.mp le_rfl
  have hi : x<(x.sqrt+1)^2 := Nat.sqrt_lt'.mp (Nat.lt_succ_self _)
  simp only [roundSqrt]
  split <;> constructor <;> nlinarith

private theorem unique_nearest {x m : ℕ} (lo : m^2<x+m) (hi : x<m^2+m) : roundSqrt x=m := by
  have band := rounded_band x
  rcases lt_trichotomy (roundSqrt x) m with less|same|more
  · obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt less)
    nlinarith only [lo,band.2,hk,Nat.zero_le k,Nat.zero_le (k*m),
      Nat.zero_le (k*roundSqrt x),Nat.zero_le (k^2)]
  · exact same
  · obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt more)
    nlinarith only [hi,band.1,hk,Nat.zero_le k,Nat.zero_le (k*m),
      Nat.zero_le (k*roundSqrt x),Nat.zero_le (k^2)]

private theorem rounded_recovery {p d g E : ℕ} (close : Within d g E)
    (price : E*(2*g+E)<p+d) :
    roundSqrt (p*(p+2*d)+g^2)=p+d := by
  have upper : d^2≤g^2+E*(2*g+E) := by nlinarith only [Nat.pow_le_pow_left close.1 2]
  have lower : g^2≤d^2+E*(2*g+E) := by
    rcases le_total g d with gd|dg
    · exact (Nat.pow_le_pow_left gd 2).trans (Nat.le_add_right ..)
    · nlinarith only [Nat.pow_le_pow_left close.2 2,Nat.mul_le_mul_left E dg]
  apply unique_nearest <;> nlinarith only [upper,lower,price]

theorem readout_iff {p d : ℕ} (pos : 0<p) :
    readout (p*(p+2*d))=(p,p+2*d) ↔ midpoint (p*(p+2*d))=p+d := by
  let n:=p*(p+2*d)
  let m:=midpoint n
  let t:=(m^2-n).sqrt
  change (m-t,m+t)=(p,p+2*d) ↔ m=p+d
  constructor
  · intro pair
    obtain ⟨x,y⟩ := Prod.mk.inj pair
    omega
  · intro mm
    have delta : (p+d)^2=n+d^2 := by dsimp [n]; ring
    have tt : t=d := by dsimp [t]; rw [mm,delta,Nat.add_sub_cancel_left,Nat.sqrt_eq']
    rw [mm,tt]
    exact Prod.ext (by omega) (by omega)

private theorem ceil_le {n k : ℕ} (h:n≤k^3) : ceilCube n≤k := Nat.find_min' _ h
private theorem ceil_hi (n : ℕ) : n ≤ (ceilCube n)^3 := by
  unfold ceilCube
  exact Nat.find_spec (p:=fun t : ℕ => n≤t^3) _

private theorem ceil_prev {n : ℕ} (npos : 0<n) : (ceilCube n-1)^3<n := by
  have pos : 0<ceilCube n := by
    by_contra! h
    have hi:=ceil_hi n
    rw [Nat.eq_zero_of_le_zero h] at hi
    simpa using hi.trans_lt npos
  exact lt_of_not_ge fun fail => (Nat.not_succ_le_self (ceilCube n-1)) (by
    have := ceil_le fail
    omega)

private theorem guess_bounds {n : ℕ} (lo : 2^2047≤n) (hi : n<2^2048) :
    2^683 ≤ ceilCube (4*n) ∧ gapGuess n ≤ 81*2^677+1 := by
  have lower : (2^683:ℕ)^3 ≤ 4*n :=
    (by decide +kernel : (2^683:ℕ)^3 ≤ 4*2^2047).trans (Nat.mul_le_mul_left 4 lo)
  constructor
  · exact (Nat.pow_le_pow_iff_left (by decide : 3≠0)).mp (lower.trans (ceil_hi _))
  · apply Nat.succ_le_succ
    exact ceil_le ((Nat.mul_le_mul_left 4 hi.le).trans
      (by decide +kernel : 4*2^2048 ≤ (81*2^677:ℕ)^3))

/-- At every 2,048-bit input, an error of at most 2^339 in the half-gap still
recovers the ordered factors with one midpoint. -/
theorem recover_2048 {p d : ℕ} (pos : 0<p)
    (lo : 2^2047≤p*(p+2*d)) (hi : p*(p+2*d)<2^2048)
    (close : Within d (gapGuess (p*(p+2*d))) (2^339)) :
    readout (p*(p+2*d))=(p,p+2*d) := by
  apply (readout_iff pos).mpr
  apply rounded_recovery close
  have midbound : 45*2^1018 ≤ p+d := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    calc
      (45*2^1018:ℕ)^2 ≤ 2^2047 := by decide +kernel
      _ ≤ p*(p+2*d) := lo
      _ ≤ (p+d)^2 := by nlinarith only [Nat.zero_le (d^2)]
  have guess := (guess_bounds lo hi).2
  calc
    _ ≤ 2^339*(2*(81*2^677+1)+2^339) := by gcongr
    _ < 45*2^1018 := by decide +kernel
    _ ≤ _ := midbound

/-- Check a supplied integer cube-root bracket and half-gap certificate
without reducing the cube-root specification on the concrete input. -/
theorem recover_certificate {n p q d c : ℕ}
    (product : n=p*(p+2*d)) (partner : q=p+2*d) (pp : 0<p)
    (lo : 2^2047≤n) (hi : n<2^2048) (cubelo : (c-1)^3<4*n) (cubehi : 4*n≤c^3)
    (lower : d≤c+1+2^339) (upper : c+1≤d+2^339) : readout n=(p,q) := by
  have close : Within d (gapGuess n) (2^339) := by
    rw [gapGuess,ceilCube_eq cubelo cubehi]
    exact ⟨lower,upper⟩
  rw [product] at lo hi close ⊢
  rw [partner]
  exact recover_2048 pp lo hi close

/-- Converse at the target scale: any actual correctly rounded midpoint,
including a success outside the guaranteed band, obeys this slightly larger
half-gap tolerance. -/
theorem necessary_2048 {p d : ℕ} (pos : 0<p) (lo : 2^2047≤p*(p+2*d))
    (hi : p+2*d<2^1024) (hit : readout (p*(p+2*d))=(p,p+2*d)) :
    Within d (gapGuess (p*(p+2*d))) (2^340) := by
  let n:=p*(p+2*d)
  let g:=gapGuess n
  have high : n<2^2048 := by
    calc
      _ ≤ (p+2*d)^2 := by dsimp [n]; rw [pow_two]; gcongr; omega
      _ < (2^1024:ℕ)^2 := Nat.pow_lt_pow_left hi (by decide)
      _ = _ := by decide +kernel
  have lowg : 2^683≤g := (guess_bounds lo high).1.trans (Nat.le_succ _)
  have band := rounded_band (n+g^2)
  change (midpoint n)^2≤n+g^2+midpoint n ∧ n+g^2≤(midpoint n)^2+midpoint n at band
  rw [(readout_iff pos).mp hit] at band
  have mlt : p+d<2^1024 := by omega
  have id : (p+d)^2=n+d^2 := by dsimp [n]; ring
  rw [id] at band
  change d≤g+2^340 ∧ g≤d+2^340
  rcases le_total g d with gd|dg
  · obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le gd
    have err : k*(2*g+k)≤p+d := by rw [hk] at band ⊢; nlinarith only [band.1]
    have paid : k*(2*2^683) < 2^1024 := (Nat.mul_le_mul_left k
      ((Nat.mul_le_mul_left 2 lowg).trans (Nat.le_add_right ..))).trans_lt (err.trans_lt mlt)
    have cap : k≤2^340 := by
      by_contra! h
      have ref : 2^1024 ≤ (2^340:ℕ)*(2*2^683) := by decide +kernel
      exact (not_lt_of_ge (ref.trans (Nat.mul_le_mul_right _ h.le))) paid
    omega
  · obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le dg
    have err : k*(g+d)≤p+d := by rw [hk] at band ⊢; nlinarith only [band.2]
    have first : k*2^683 < 2^1024 :=
      (Nat.mul_le_mul_left k (lowg.trans (Nat.le_add_right ..))).trans_lt (err.trans_lt mlt)
    have cheap : k≤2^341 := by
      by_contra! h
      have ref : 2^1024 ≤ (2^341:ℕ)*2^683 := by decide +kernel
      exact (not_lt_of_ge (ref.trans (Nat.mul_le_mul_right _ h.le))) first
    have cost : 2^684-2^341≤g+d := by
      have twice : (2:ℕ)^684=2*2^683 := by decide +kernel
      omega
    have cap : k≤2^340 := by
      by_contra! h
      have floor : 2^1024 ≤ (2^340+1)*(2^684-2^341:ℕ) := by decide +kernel
      exact (not_lt_of_ge (floor.trans (Nat.mul_le_mul h cost))) (err.trans_lt mlt)
    omega

/-- With a common first factor, a change of `k+1` in the ceiling cube root
must cost more than `3·2^339·k` in the half-gap. This counts the motion of
the public prediction even though the two products differ. -/
private theorem change_cost {p d e k : ℕ} (pbound : p≤2^1024)
    (lo : 2^2047≤p*(p+2*d)) (hi : p*(p+2*d)<2^2048) (de : d≤e)
    (move : ceilCube (4*(p*(p+2*e)))=ceilCube (4*(p*(p+2*d)))+1+k) :
    d+3*2^339*k < e := by
  let u := ceilCube (4*(p*(p+2*d)))
  have start : 4*(p*(p+2*d))≤u^3 := ceil_hi _
  have endpos : 0<4*(p*(p+2*e)) := by
    have init : 0<p*(p+2*d) := (by decide +kernel : 0<(2:ℕ)^2047).trans_le lo
    exact Nat.mul_pos (by decide) (init.trans_le (Nat.mul_le_mul_left p (by omega)))
  have finish := ceil_prev endpos
  rw [move,show ceilCube (4*(p*(p+2*d)))+1+k-1=u+k by dsimp [u]; omega] at finish
  have ub : 2^683≤u := (guess_bounds lo hi).1
  have grow : u^3+3*u^2*k ≤ (u+k)^3 := by
    nlinarith only [Nat.zero_le (u*k^2),Nat.zero_le (k^3)]
  have cost := ((Nat.add_le_add start (Nat.mul_le_mul_right k
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left ub 2)))).trans grow).trans_lt finish
  obtain ⟨v,eq⟩ := Nat.exists_eq_add_of_le de
  rw [eq] at cost ⊢
  have delta : 3*(2^683)^2*k < 8*p*v := by nlinarith only [cost]
  have px := Nat.mul_le_mul_right v (Nat.mul_le_mul_left 8 pbound)
  have pay : (8*2^1024)*(3*2^339*k)<(8*2^1024)*v := by
    rw [←mul_assoc,show 8*2^1024*(3*2^339)=3*(2^683:ℕ)^2 by decide +kernel]
    exact delta.trans_le px
  exact Nat.add_lt_add_left (Nat.lt_of_mul_lt_mul_left pay) d

/-- A parameterized diameter estimate. For a tolerance `E`, one can choose any
integer `s` satisfying the displayed finite inequality. -/
theorem gap_diameter {p d e E s : ℕ} (pbound : p≤2^1024) (de : d≤e)
    (lo : 2^2047≤p*(p+2*d)) (hi : p*(p+2*d)<2^2048)
    (dx : Within d (gapGuess (p*(p+2*d))) E) (ex : Within e (gapGuess (p*(p+2*e))) E)
    (budget : 2*E+1 ≤ (3*2^339-1)*s) :
    e≤d+2*E+s := by
  let u:=ceilCube (4*(p*(p+2*d)))
  let v:=ceilCube (4*(p*(p+2*e)))
  change d≤u+1+E ∧ u+1≤d+E at dx
  change e≤v+1+E ∧ v+1≤e+E at ex
  by_cases bound : v≤u+s
  · omega
  push_neg at bound
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show u+1≤v by omega)
  have charged := change_cost pbound lo hi de hk
  have ks : s≤k := by omega
  have large := Nat.mul_le_mul_left (3*2^339-1) ks
  have deep : 2*E+1 ≤ (3*2^339-1)*k := budget.trans large
  have eq : (3*2^339-1)*k+k=3*2^339*k := by
    rw [←Nat.succ_mul]
    exact congrArg (·*k) (by decide +kernel : Nat.succ ((3:ℕ)*2^339-1)=3*2^339)
  omega

private abbrev half (z : ℕ×ℕ) := (z.2-z.1)/2

attribute [local irreducible] MixedPrefixSample.primes MixedPrefixSample.eligible
  MixedPrefixSample.sample MixedPrefixSample.ordered

private theorem eligible_data {z : ℕ×ℕ} (hz : z∈MixedPrefixSample.eligible) :
    z.1∈MixedPrefixSample.primes ∧ 0<z.1 ∧ z.1≤2^1024 ∧ z.2<2^1024 ∧
    z.2=z.1+2*half z ∧ 2^2047≤z.1*z.2 ∧ z.1*z.2<2^2048 := by
  rw [MixedPrefixSample.eligible,MixedPrefixSample.sample,mem_filter] at hz
  obtain ⟨mem,ord⟩ := hz
  obtain ⟨pm,qm,_,nl,_⟩ := MixedPrefixSample.mem_ordered.mp mem
  refine ⟨pm,?_⟩
  rw [MixedPrefixSample.primes,mem_filter,mem_Ico] at pm qm
  have size : 2*MixedPrefixSample.X=2^1024 := by decide +kernel
  have base : 2*MixedPrefixSample.X^2=2^2047 := by decide +kernel
  rw [base] at nl
  obtain ⟨⟨pl,pu⟩,pp⟩ := pm
  obtain ⟨⟨ql,qu⟩,qp⟩ := qm
  rw [size] at pu qu
  have lp : 2<MixedPrefixSample.X := by decide +kernel
  obtain ⟨a,ha⟩ := pp.odd_of_ne_two (by omega)
  obtain ⟨b,hb⟩ := qp.odd_of_ne_two (by omega)
  have big := Nat.mul_lt_mul_of_lt_of_le pu qu.le (by positivity : 0<(2:ℕ)^1024)
  rw [show (2:ℕ)^1024*2^1024=2^2048 by decide +kernel] at big
  exact ⟨pp.pos,pu.le,qu,by dsimp only [half]; omega,nl,big⟩

/-- All half-gaps in a fiber of the first prime lie in one interval of
`2E+s+1` integer values. The cube root is recomputed on each individual product. -/
theorem population (S : Finset (ℕ×ℕ)) {E s : ℕ}
    (subset : S⊆MixedPrefixSample.eligible)
    (close : ∀ z∈S, Within (half z) (gapGuess (z.1*z.2)) E)
    (budget : 2*E+1≤(3*2^339-1)*s) :
    S.card ≤ MixedPrefixSample.primes.card*(2*E+s+1) := by
  classical
  let cell (p : ℕ) := S.filter (fun z => z.1=p)
  have cover : S⊆MixedPrefixSample.primes.biUnion cell := by
    intro z hz
    exact mem_biUnion.mpr ⟨z.1,(eligible_data (subset hz)).1,mem_filter.mpr ⟨hz,rfl⟩⟩
  refine (card_le_card cover).trans (card_biUnion_le_card_mul _ _ _ ?_)
  intro p _
  let D := (cell p).image half
  have props {d : ℕ} (hd : d∈D) : p≤2^1024 ∧ 2^2047≤p*(p+2*d) ∧ p*(p+2*d)<2^2048 ∧
      Within d (gapGuess (p*(p+2*d))) E := by
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hd
    obtain ⟨sz,hp⟩ := mem_filter.mp hz
    obtain ⟨_,_,pmax,_,eq,lo,hi⟩ := eligible_data (subset sz)
    have rewrite : p*(p+2*half z)=z.1*z.2 := by rw [←hp,←eq]
    rw [rewrite]
    exact ⟨hp ▸ pmax,lo,hi,close z sz⟩
  have same : D.card=(cell p).card := by
    apply card_image_of_injOn
    intro x hx y hy eq
    obtain ⟨xs,xp⟩ := mem_filter.mp hx
    obtain ⟨ys,yp⟩ := mem_filter.mp hy
    have qx := (eligible_data (subset xs)).2.2.2.2.1
    have qy := (eligible_data (subset ys)).2.2.2.2.1
    exact Prod.ext (xp.trans yp.symm) (by rw [qx,qy,eq,xp,yp])
  rw [←same]
  rcases D.eq_empty_or_nonempty with empty | nonempty
  · simp [empty]
  let d := D.min' nonempty
  obtain ⟨pmax,lo,hi,near⟩ := props (D.min'_mem nonempty)
  have span : D⊆Icc d (d+2*E+s) := by
    intro e he
    have de := D.min'_le e he
    exact mem_Icc.mpr ⟨de,gap_diameter pmax de lo hi near (props he).2.2.2 budget⟩
  exact (card_le_card span).trans (by rw [Nat.card_Icc]; omega)

/-- A subset selected by the actual value returned by the product-only readout. -/
noncomputable def successes : Finset (ℕ×ℕ) := by
  classical exact MixedPrefixSample.eligible.filter (fun z => readout (z.1*z.2)=z)

/-- The smaller, guaranteed region stated in `recover_2048`. -/
noncomputable def guaranteed : Finset (ℕ×ℕ) := by
  classical exact MixedPrefixSample.eligible.filter (fun z => Within (half z) (gapGuess (z.1*z.2)) (2^339))

private theorem frac {S P pop k b : ℕ} (count : S≤P*k) (marginal : 2^1023*P<41056*pop)
    (kp : 0<k) (price : 41056*(2^b*k)≤2^1023) : 2^b*S<pop := by
  apply Nat.lt_of_mul_lt_mul_left (a:=2^1023)
  calc
    2^1023*(2^b*S) ≤ 2^1023*(2^b*(P*k)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ count)
    _ = (2^1023*P)*(2^b*k) := by ac_rfl
    _ < (41056*pop)*(2^b*k) :=
      Nat.mul_lt_mul_of_pos_right marginal (by positivity)
    _ = (41056*(2^b*k))*pop := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ price

private theorem in_guaranteed {z : ℕ×ℕ} (hz : z ∈ guaranteed) :
    z ∈ MixedPrefixSample.eligible ∧ Within (half z) (gapGuess (z.1*z.2)) (2^339) := by
  simpa only [guaranteed,mem_filter] using hz

private theorem in_successes {z : ℕ×ℕ} (hz : z ∈ successes) :
    z ∈ MixedPrefixSample.eligible ∧ readout (z.1*z.2)=z := by
  simpa only [successes,mem_filter] using hz

theorem guaranteed_subset : guaranteed ⊆ successes := by
  intro z hz
  obtain ⟨mem,hit⟩ := in_guaranteed hz
  obtain ⟨_,pp,_,_,eq,lo,hi⟩ := eligible_data mem
  have pair : (z.1,z.1+2*half z)=z := Prod.ext rfl eq.symm
  have pq : z.1*(z.1+2*half z)=z.1*z.2 := congrArg (z.1*·) eq.symm
  have recover := recover_2048 pp (pq ▸ lo) (pq ▸ hi) (pq ▸ hit)
  rw [pq,pair] at recover
  simpa only [successes,mem_filter] using And.intro mem recover

private theorem marginal' : 2^1023*MixedPrefixSample.primes.card<41056*MixedPrefixSample.eligible.card := by
  have cut : (2:ℕ)^1023=MixedPrefixSample.X := rfl
  exact lt_of_eq_of_lt (congrArg (fun x : ℕ => x*MixedPrefixSample.primes.card) cut)
    SquareRootPhasePopulation.marginal

private theorem guaranteed_count :
    guaranteed.card≤MixedPrefixSample.primes.card*(2*2^339+1+1) :=
  population guaranteed (fun _ hz => (in_guaranteed hz).1) (fun _ hz => (in_guaranteed hz).2)
    (by decide +kernel)

theorem guaranteed_fraction :
    2^667*guaranteed.card < MixedPrefixSample.eligible.card :=
  frac guaranteed_count marginal' (by decide +kernel) (by decide +kernel)

/-- All actual successes, including successes outside the sufficient tolerance.
The population is the uniform set of distinct equally wide prime pairs whose
product has exactly 2,048 bits. -/
theorem successes_fraction :
    2^666*successes.card < MixedPrefixSample.eligible.card := by
  classical
  have near (z : ℕ×ℕ) (hz : z∈successes) :
      Within (half z) (gapGuess (z.1*z.2)) (2^340) := by
    obtain ⟨mem,hit⟩ := in_successes hz
    obtain ⟨_,pp,_,qu,eq,lo,_⟩ := eligible_data mem
    have pair : (z.1,z.1+2*half z)=z := Prod.ext rfl eq.symm
    have pq : z.1*(z.1+2*half z)=z.1*z.2 := congrArg (z.1*·) eq.symm
    rw [←pq]
    apply necessary_2048 pp (pq ▸ lo) (eq ▸ qu)
    rw [pq,pair]
    exact hit
  have cnt := population successes (s:=2) (fun _ hz => (in_successes hz).1) near
    (by decide +kernel : 2*2^340+1≤(3*2^339-1)*2)
  exact frac cnt marginal' (by decide +kernel) (by decide +kernel)

end PrimeFactors.CubicGapWindow
