import PrimeFactors.SquareRootPhasePopulation
import PrimeFactors.FactorSum
import PrimeFactors.Fermat
import Mathlib.Algebra.Order.Chebyshev

/-! A constructive lower bound on the frequency of the first J even sums
starting at twice the ceiling square root. Upper-band primes in the same
short interval guarantee a success, without a distributional assumption in
any individual short interval. -/
namespace PrimeFactors.FirstSumMenuPopulation

open Finset MixedPrefixSample
set_option maxRecDepth 8192
set_option exponentiation.threshold 4096

/-- The guesses use just the product, in increasing order. -/
noncomputable def menu (J N : ℕ) := (range J).image fun i => 2*(ceilSqrt N+i)

theorem menu_card (J N : ℕ) : (menu J N).card=J := by
  rw [menu,card_image_of_injective _ (by intro a b h; change 2*(_+a)=2*(_+b) at h; omega),card_range]

/-- A message selecting one of A blocks lets a list of size K cover any
one of the first A*K positions, provided the appropriate message is supplied. -/
theorem advised_iff {A K N S : ℕ} (kp : 0<K) : S∈menu (A*K) N ↔
    ∃ a<A, ∃ i<K, 2*(ceilSqrt N+(a*K+i))=S := by
  constructor
  · rintro mem
    obtain ⟨j,hj,eq⟩ := mem_image.mp mem
    have bound := mem_range.mp hj
    refine ⟨j/K,(Nat.div_lt_iff_lt_mul kp).mpr bound,j%K,Nat.mod_lt j kp,?_⟩
    have split : j/K*K+j%K=j := by
      simpa only [Nat.mul_comm K (j/K),Nat.add_comm (j%K)] using Nat.mod_add_div j K
    rw [split]
    exact eq
  · rintro ⟨a,ha,i,hi,eq⟩
    refine mem_image.mpr ⟨a*K+i,mem_range.mpr ?_,eq⟩
    have bound := Nat.mul_le_mul_right K (Nat.succ_le_of_lt ha)
    rw [Nat.succ_mul] at bound
    omega

def event (J N : ℕ) : Prop :=
  ∃ p q : ℕ, 1<p ∧ p≤q ∧ p*q=N ∧ p+q∈menu J N

attribute [local irreducible] primes upperPrimes ordered sample eligible

private theorem prime_of_mem {p : ℕ} (hp : p∈primes) : p.Prime := by
  simp only [primes,mem_filter] at hp
  exact hp.2

/-- On the sorted eligible pairs, the event says exactly that the true sum is guessed. -/
theorem mem_sample_iff {J : ℕ} {z : ℕ×ℕ} : z∈sample (event J) ↔
    z∈eligible ∧ z.1+z.2∈menu J (z.1*z.2) := by
  simp only [eligible,sample,mem_filter,mem_ordered]
  constructor
  · rintro ⟨⟨a,b,ne,size,p,q,nontrivial,pq,equal,hit⟩,lt⟩
    have pa : z.1.Prime := prime_of_mem a
    have pb : z.2.Prime := prime_of_mem b
    obtain ⟨rfl,rfl⟩ := ordered_semiprime_pair_unique pa pb lt.le pq nontrivial equal
    exact ⟨⟨⟨a,b,ne,size,trivial⟩,lt⟩,hit⟩
  · rintro ⟨⟨⟨a,b,ne,size,_⟩,lt⟩,hit⟩
    have pa : z.1.Prime := prime_of_mem a
    exact ⟨⟨a,b,ne,size,_,_,pa.one_lt,lt.le,rfl,hit⟩,lt⟩

/-- A pair closer than D fits whenever D² ≤ 8xJ and both factors are at least x. -/
theorem close_hit {x p q D J : ℕ} (xp : x≤p) (pq : p≤q) (dist : q<p+D)
    (po : Odd p) (qo : Odd q) (width : D^2≤8*x*J) : p+q∈menu J (p*q) := by
  obtain ⟨a,ha⟩ := po
  obtain ⟨b,hb⟩ := qo
  let t := b-a
  have qrep : q=p+2*t := by dsimp [t]; omega
  let r := ceilSqrt (p*q)
  have gap : 2*t<D := by omega
  have tsq := Nat.pow_lt_pow_left gap (by decide : 2≠0)
  have base : p*q≤r^2 := ceilSqrt_le_iff.mp le_rfl
  have xr : x≤r := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    ((show x^2 ≤ p*q by simpa only [pow_two] using Nat.mul_le_mul xp (xp.trans pq)).trans base)
  have square : (p+t)^2=p*q+t^2 := by rw [qrep]; ring
  have low : r≤p+t := ceilSqrt_le_iff.mpr (by omega)
  have high : p+t<r+J := by
    apply lt_of_not_ge
    intro large
    have sq := Nat.pow_le_pow_left large 2
    have cross := Nat.mul_le_mul_right J xr
    nlinarith only [sq,cross,base,square,tsq,width,Nat.zero_le (J^2)]
  exact mem_image.mpr ⟨p+t-r,mem_range.mpr (by omega),by omega⟩

private theorem upper_data {p : ℕ} (hp : p∈upperPrimes) :
    p∈primes ∧ X≤p ∧ p<2*X ∧ p.Prime ∧ Odd p ∧ 283*X≤200*p := by
  have mem := (show p∈primes ∧ 283*X≤200*p from (by simpa only [upperPrimes,mem_filter] using hp))
  have inP := mem.1
  simp only [primes,mem_filter,mem_Ico] at inP
  have limit : 2<X := by decide +kernel
  exact ⟨mem.1,inP.1.1,inP.1.2,inP.2,inP.2.odd_of_ne_two (by have := inP.1.1; omega),mem.2⟩

/-- For b buckets containing H primes, Cauchy's inequality counts at least
H²/b ordered collisions, including exactly H diagonal pairs. -/
private theorem collision_count (s : Finset ℕ) (key : ℕ→ℕ) (b : ℕ)
    (maps : ∀ p∈s, key p<b) :
    s.card^2≤b*((s ×ˢ s).filter (fun z => key z.1=key z.2)).card := by
  classical
  let pairs := (s ×ˢ s).filter fun z => key z.1=key z.2
  let bucket i := s.filter fun p => key p=i
  let tag := fun z : ℕ×ℕ => key z.1
  have pm : Set.MapsTo tag (pairs : Set (ℕ×ℕ)) (range b) := by
    intro z hz
    exact mem_range.mpr (maps _ (mem_product.mp (mem_filter.mp hz).1).1)
  have sm : Set.MapsTo key s (range b) := fun p hp => mem_range.mpr (maps p hp)
  have fibers (i : ℕ) : pairs.filter (fun z => tag z=i) = bucket i ×ˢ bucket i := by
    ext z
    simp only [pairs,bucket,tag,mem_filter,mem_product]
    aesop
  have counts := card_eq_sum_card_fiberwise pm
  simp_rw [fibers,card_product,←sq] at counts
  change s.card^2≤b*pairs.card
  rw [card_eq_sum_card_fiberwise sm,counts]
  simpa only [card_range,Nat.cast_id] using (sq_sum_le_card_mul_sum_sq (s:=range b) (f:=fun i => (bucket i).card))

/-- If b consecutive width-D intervals cover [X,2X), the exact diagonals
are the only equal-prime pairs in the collision count. -/
theorem finite_bound {b D J : ℕ} (dp : 0<D) (cover : X≤b*D) (width : D^2≤8*X*J) :
    upperPrimes.card^2≤b*(2*(sample (event J)).card+upperPrimes.card) := by
  classical
  let key (p : ℕ) := (p-X)/D
  let pairs := (upperPrimes ×ˢ upperPrimes).filter fun z => key z.1=key z.2
  have maps (p : ℕ) (hp : p∈upperPrimes) : key p<b := by
    have info := upper_data hp
    exact (Nat.div_lt_iff_lt_mul dp).mpr (by obtain ⟨_,_,lt,_⟩ := info; omega)
  have energy := collision_count upperPrimes key b maps
  have sub : pairs⊆ordered (event J) ∪ upperPrimes.diag := by
    rintro ⟨p,q⟩ hpq
    obtain ⟨mem,e⟩ := mem_filter.mp hpq
    obtain ⟨pm,qm⟩ := mem_product.mp mem
    by_cases eq : p=q
    · exact mem_union_right _ (mem_diag.mpr ⟨pm,eq⟩)
    obtain ⟨pIn,pl,_,pp,po,pHi⟩ := upper_data pm
    obtain ⟨qIn,ql,_,qp,qo,qHi⟩ := upper_data qm
    have big : 2*X^2≤p*q := by
      have scaled := Nat.mul_le_mul pHi qHi
      nlinarith only [scaled,Nat.zero_le (X*X)]
    have close {u v : ℕ} (ul : X≤u) (vl : X≤v) (same : key u=key v) : v<u+D := by
      have low := Nat.mul_div_le (u-X) D
      have high := Nat.lt_mul_div_succ (v-X) dp
      change (u-X)/D=(v-X)/D at same
      rw [←same,Nat.mul_add,Nat.mul_one] at high
      omega
    apply mem_union_left
    apply (mem_ordered (E:=event J)).mpr
    refine ⟨pIn,qIn,eq,big,?_⟩
    rcases le_total p q with pq|qp'
    · exact ⟨p,q,pp.one_lt,pq,rfl,close_hit pl pq (close pl ql e) po qo width⟩
    · have hit := close_hit ql qp' (close ql pl e.symm) qo po width
      exact ⟨q,p,qp.one_lt,qp',Nat.mul_comm ..,by simpa only [Nat.mul_comm q p] using hit⟩
  have count := (card_le_card sub).trans (card_union_le ..)
  rw [two_orders,diag_card] at count
  exact energy.trans (Nat.mul_le_mul_left b count)

private theorem marginal : primes.card < 7*upperPrimes.card := by
  have xp : 2<X := by decide +kernel
  have composite : ¬X.Prime := Nat.not_prime_of_dvd_of_lt
    (show 2∣X from dvd_pow_self _ (by decide : 1023≠0)) le_rfl xp
  have upper := SquareRootPhasePopulation.prime_upper (x:=X) (k:=1023) rfl (by omega) primes (by
    intro p hp
    simp only [primes,mem_filter,mem_Ico] at hp
    exact ⟨lt_of_le_of_ne hp.1.1 (fun eq => composite (eq ▸ hp.2)),hp.1.2,hp.2⟩)
  have lower := ChebyshevPrimeSample.prime_count
  change 11*X<35500*(upperPrimes.card-1) at lower
  omega

private theorem prime_pairs : 2*eligible.card≤primes.card^2 := by
  have sub : ordered (fun _ => True)⊆primes ×ˢ primes := by
    intro z hz
    have data := mem_ordered.mp hz
    exact mem_product.mpr ⟨data.1,data.2.1⟩
  have count := card_le_card sub
  rw [two_orders,card_product,←eligible,←sq] at count
  exact count

/-- The first J guesses succeed on a fraction greater than 1/(100b)
when the upper prime set has at least twice as many members as buckets. -/
theorem frequency {b D J : ℕ} (dp : 0<D) (cover : X≤b*D) (width : D^2≤8*X*J)
    (many : 2*b≤upperPrimes.card) : eligible.card < (100*b)*(sample (event J)).card := by
  have combine (H P C S B : ℕ) (bounds : H^2≤B*(2*S+H)) (many' : 2*B≤H)
      (marg : P<7*H) (count : 2*C≤P^2) : C<(100*B)*S := by
    have diagonal := Nat.mul_le_mul_right H many'
    have cap : H^2≤4*B*S := by nlinarith only [bounds,diagonal]
    have upper := Nat.pow_lt_pow_left marg (by decide : 2≠0)
    nlinarith only [count,upper,cap,Nat.zero_le (B*S)]
  exact combine _ _ _ _ _ (finite_bound dp cover width) many marginal prime_pairs

private theorem buckets : 2*2^510≤upperPrimes.card := by
  have lower := ChebyshevPrimeSample.prime_count
  change 11*X<35500*(upperPrimes.card-1) at lower
  have number : 35500*(2*2^510) ≤ 11*X := by decide +kernel
  omega

theorem single : eligible.card < 2^517*(sample (event 1)).card := by
  have f := frequency (b:=2^510) (D:=2^513) (J:=1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) buckets
  exact f.trans_le (Nat.mul_le_mul_right _ (by decide +kernel))

theorem list168 : eligible.card < 2^433*(sample (event (2^168))).card := by
  have f := frequency (b:=2^426) (D:=2^597) (J:=2^168)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ((by decide +kernel : 2*2^426 ≤ 2*2^510).trans buckets)
  exact f.trans_le (Nat.mul_le_mul_right _ (by decide +kernel))

theorem list552 : eligible.card < 2^241*(sample (event (2^552))).card := by
  have f := frequency (b:=2^234) (D:=2^789) (J:=2^552)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ((by decide +kernel : 2*2^234 ≤ 2*2^510).trans buckets)
  exact f.trans_le (Nat.mul_le_mul_right _ (by decide +kernel))

end PrimeFactors.FirstSumMenuPopulation
