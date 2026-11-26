import PrimeFactors.QuotientBudget
import PrimeFactors.SumSignatureProbability
import PrimeFactors.GeometricIndexReadout
import PrimeFactors.Fermat
import PrimeFactors.PowerSignature

/-! A lower bound for the fraction of useful first-order geometric readings
for each fixed balanced product, with the base uniform among its units. -/

namespace PrimeFactors.GeometricGeneratorFraction
open Finset GeometricIndexReadout
set_option exponentiation.threshold 4096

/-- Elements whose order divides m and exceeds the whole exponent interval. -/
noncomputable def pool (G : Type*) [Group G] [Fintype G] (W m : ℕ) : Finset G := by
  classical exact univ.filter (fun g : G => orderOf g ∣ m ∧ W < orderOf g)

@[simp] theorem mem_pool {G : Type*} [Group G] [Fintype G] {W m : ℕ} {g : G} :
    g ∈ pool G W m ↔ orderOf g ∣ m ∧ W < orderOf g := by classical simp [pool]

private theorem pool_mono {G : Type*} [Group G] [Fintype G] {W u m : ℕ} (h : u ∣ m) :
    pool G W u ⊆ pool G W m := by
  classical
  intro x hx
  exact mem_pool.mpr ⟨(mem_pool.mp hx).1.trans h, (mem_pool.mp hx).2⟩

private theorem full_order_le (G : Type*) [Group G] [Fintype G] [IsCyclic G] {m W : ℕ}
    (hm : m ∣ Fintype.card G) (w : W<m) : m.totient ≤ (pool G W m).card := by
  classical
  rw [← IsCyclic.card_orderOf_eq_totient (α:=G) hm]
  apply card_le_card
  intro x hx
  have ox := (mem_filter.mp hx).2
  exact mem_pool.mpr (by rw [ox]; exact ⟨dvd_rfl,w⟩)

private theorem add_half (G : Type*) [Group G] [Fintype G] [IsCyclic G] {u W : ℕ}
    (upos : 0<u) (hm : 2*u ∣ Fintype.card G) (w : W<2*u) :
    (2*u).totient + (pool G W u).card ≤ (pool G W (2*u)).card := by
  classical
  let A := univ.filter (fun x : G => orderOf x=2*u)
  have nA : A.card=(2*u).totient := IsCyclic.card_orderOf_eq_totient hm
  have dis : Disjoint A (pool G W u) := by
    apply disjoint_left.mpr
    intro x hx hy
    have div := (mem_filter.mp hy).2.1
    rw [(mem_filter.mp hx).2] at div
    have := Nat.le_of_dvd upos div
    omega
  rw [← nA, ← card_union_of_disjoint dis]
  apply card_le_card
  apply union_subset
  · intro x hx
    have ox : orderOf x=2*u := (mem_filter.mp hx).2
    exact mem_pool.mpr (by rw [ox]; exact ⟨dvd_rfl,w⟩)
  · exact pool_mono (dvd_mul_left _ _)

/-- Count the disjoint order classes m, m/2, ..., m/2^k while the quotients
are integral. When m is odd, the totient of 2m pays for the missing classes. -/
theorem long_periods (G : Type*) [Group G] [Fintype G] [IsCyclic G] (k : ℕ) {m W : ℕ}
    (mp : 0<m) (cap : m≤2^1024) (div : m∣Fintype.card G) (room : 2^k*W<m) :
    2*2^k*m < 13*2^k*(pool G W m).card + m := by
  have cm : m≤2^1366 := cap.trans (by decide +kernel)
  have phi := quotientBudget_wheel_ratio mp cm
  have short : W<m := (Nat.le_mul_of_pos_left W (by positivity : 0<2^k)).trans_lt room
  have full := full_order_le G div short
  induction k generalizing m with
  | zero => simp only [pow_zero, mul_one] at *; omega
  | succ k ih =>
    by_cases even : 2∣m
    · obtain ⟨u,rfl⟩ := even
      have up : 0<u := by omega
      have uc : u≤2^1024 := by omega
      have ur : 2^k*W<u := by
        rw [pow_succ] at room
        exact (Nat.mul_lt_mul_left (by decide : 0<2)).mp (by convert room using 1; ring)
      have sub := ih up uc ((dvd_mul_left u 2).trans div) ur
      have u_short := (Nat.le_mul_of_pos_left W (by positivity : 0<2^k)).trans_lt ur
      specialize sub (by omega) (quotientBudget_wheel_ratio up (by omega)) u_short
        (full_order_le G ((dvd_mul_left u 2).trans div) u_short)
      have add := add_half G up div short
      have e := Nat.mul_lt_mul_of_pos_left phi (by positivity : 0<2^(k+1))
      have d := Nat.mul_le_mul_left (13*2^(k+1)) add
      rw [pow_succ] at e d ⊢
      nlinarith only [e,d,sub]
    · have wide : 2*m ≤ 2^1366 := (Nat.mul_le_mul_left 2 cap).trans (by decide +kernel)
      have odd := quotientBudget_wheel_ratio (Nat.mul_pos (by decide) mp) wide
      rw [Nat.totient_mul_of_prime_of_not_dvd Nat.prime_two even] at odd
      simp only [Nat.reduceSub, one_mul] at odd
      have cost := Nat.mul_lt_mul_of_pos_left odd (by positivity : 0<2^(k+1))
      have count := Nat.mul_le_mul_left (13*2^(k+1)) full
      nlinarith only [cost,count,mp]

/-- The normalized first derivative, computed from the public target y. -/
noncomputable def denominator {R : Type*} [CommRing R] (W : ℕ) (y g : R) : R :=
  y * targetDerivative (range (W+1)) y g

/-- Units that produce a nonzero first-order denominator at the designated
true index. The index specifies the event being counted. -/
noncomputable def useful (n W j : ℕ) [NeZero n] : Finset (ZMod n)ˣ :=
  univ.filter (fun g => denominator W ((g:ZMod n)^j) g ≠ 0)

private theorem long_projection {n p W j : ℕ} [NeZero n] [Fact p.Prime]
    (f : ZMod n →+* ZMod p) (g : (ZMod n)ˣ) (sj : j≤W)
    (long : W < orderOf (Units.map f.toMonoidHom g)) : g ∈ useful n W j := by
  let b := Units.map f.toMonoidHom g
  have non := field_simple (K:=ZMod p) (S:=range (W+1)) (j:=j) (g:=(b:ZMod p))
    (mem_range.mpr (by omega)) rfl (pow_ne_zero _ b.ne_zero) (by
      intro i hi eq
      have both : b^i=b^j := Units.ext (by simpa only [Units.val_pow_eq_pow_val] using eq.symm)
      have rem := pow_eq_pow_iff_modEq.mp both
      change i % orderOf b = j % orderOf b at rem
      have lim := mem_range.mp hi
      have over : W < orderOf b := long
      simpa only [Nat.mod_eq_of_lt (by omega : i<orderOf b), Nat.mod_eq_of_lt (by omega : j<orderOf b)] using rem)
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  intro zero
  apply non.ne_zero
  have eq := congrArg f zero
  simpa only [denominator, targetDerivative, omitted, map_mul, map_sum, map_prod, map_sub,
    map_pow, map_zero] using eq

/-- A useful base returns either a proper gcd or the exact integer index by
one modular inversion. The actual search supplies y and tests this public gcd. -/
theorem decode {n W j : ℕ} [NeZero n] (g : (ZMod n)ˣ) (y : ZMod n)
    (hit : (g:ZMod n)^j=y) (sj : j≤W) (jn : j<n) (works : g∈useful n W j) :
    let z := denominator W y (g:ZMod n)
    (1<z.val.gcd n ∧ z.val.gcd n<n) ∨
    (z.val.gcd n=1 ∧ (-baseTangent (range (W+1)) y (g:ZMod n)*z⁻¹).val=j) := by
  subst y
  intro z
  have nz : z≠0 := (mem_filter.mp works).2
  by_cases one : z.val.gcd n=1
  · right
    have unit : IsUnit z := ZMod.natCast_zmod_val z ▸ (ZMod.isUnit_iff_coprime z.val n).mpr one
    exact ⟨one, index_nat jn (mem_range.mpr (by omega)) rfl (ZMod.mul_inv_of_unit z unit)⟩
  · left
    have pos := Nat.gcd_pos_of_pos_right z.val (NeZero.pos n)
    have zp : 0<z.val := Nat.pos_of_ne_zero (fun h => nz ((ZMod.val_eq_zero z).mp h))
    exact ⟨by omega, (Nat.le_of_dvd zp (Nat.gcd_dvd_left ..)).trans_lt (ZMod.val_lt z)⟩

/-- More than 1403/5408 of all units give a first-order readout or proper gcd,
for each fixed input and each designated index in an interval with these widths.
The two coordinates of a uniform unit are independent under CRT. -/
theorem per_input {p q W j : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (cop : p.Coprime q) (pcap : p≤2^1024) (qcap : q≤2^1024)
    (pw : 4*W < p-1) (qw : 8*W < q-1) (sj : j≤W) :
    1403*Fintype.card (ZMod (p*q))ˣ < 5408*(useful (p*q) W j).card := by
  classical
  let e := (Units.mapEquiv (ZMod.chineseRemainder cop).toMulEquiv).trans MulEquiv.prodUnits
  let f := (RingHom.fst (ZMod p) (ZMod q)).comp (ZMod.chineseRemainder cop).toRingHom
  let h := (RingHom.snd (ZMod p) (ZMod q)).comp (ZMod.chineseRemainder cop).toRingHom
  let P := pool (ZMod p)ˣ W (p-1)
  let Q := pool (ZMod q)ˣ W (q-1)
  let U := useful (p*q) W j
  have cp := (Nat.prime_iff_card_units p).mp hp.out
  have cq := (Nat.prime_iff_card_units q).mp hq.out
  have pp := long_periods (ZMod p)ˣ 2 (m:=p-1) (W:=W) (by omega) (by omega)
    (cp ▸ dvd_rfl) pw
  have qq := long_periods (ZMod q)ˣ 3 (m:=q-1) (W:=W) (by omega) (by omega)
    (cq ▸ dvd_rfl) qw
  have pcount := card_add_card_compl P
  have qcount := card_add_card_compl Q
  change 2*2^2*(p-1) < 13*2^2*P.card + (p-1) at pp
  change 2*2^3*(q-1) < 13*2^3*Q.card + (q-1) at qq
  have a : 52*Pᶜ.card < 45*Fintype.card (ZMod p)ˣ := by omega
  have b : 104*Qᶜ.card < 89*Fintype.card (ZMod q)ˣ := by omega
  have sub : Uᶜ.image e ⊆ Pᶜ ×ˢ Qᶜ := by
    intro w hw
    obtain ⟨g, hg, rfl⟩ := mem_image.mp hw
    apply mem_product.mpr
    constructor
    · apply mem_compl.mpr
      intro good
      apply (mem_compl.mp hg)
      exact long_projection f g sj (mem_pool.mp good).2
    · apply mem_compl.mpr
      intro good
      apply (mem_compl.mp hg)
      exact long_projection h g sj (mem_pool.mp good).2
  have bound := card_le_card sub
  rw [card_image_of_injective _ e.injective, card_product] at bound
  have rate := (Nat.mul_le_mul_right _ a.le).trans_lt
    (Nat.mul_lt_mul_of_pos_left b (Nat.mul_pos (by decide : 0<45) Fintype.card_pos))
  have units := (Fintype.card_congr e.toEquiv).trans (Fintype.card_prod _ _)
  have missing := Nat.mul_le_mul_left 5408 bound
  have result : 5408*Uᶜ.card < 4005*Fintype.card (ZMod (p*q))ˣ := by
    rw [units]; nlinarith only [rate, missing]
  have total := card_add_card_compl U
  change 1403*Fintype.card (ZMod (p*q))ˣ < 5408*U.card
  omega

/-- Specialization to the actual product-defined, rounded balanced interval. -/
theorem balanced {p q j : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (large : 64≤p) (pq : p≤q) (bal : q≤2*p) (qcap : q≤2^1024) :
    let W := (9*(p*q)/2).sqrt-ceilSqrt (4*(p*q))
    j≤W → 1403*Fintype.card (ZMod (p*q))ˣ < 5408*(useful (p*q) W j).card := by
  let L := ceilSqrt (4*(p*q))
  let U := (9*(p*q)/2).sqrt
  intro W sj
  apply per_input cop (pq.trans qcap) qcap _ _ sj
  all_goals
    by_cases nonempty : L ≤ U
    · have lower : 4*(p*q)≤L^2 := ceilSqrt_le_iff.mp le_rfl
      have upper : 2*U^2≤9*(p*q) := (Nat.mul_le_mul_left 2 (Nat.sqrt_le' _)).trans (Nat.mul_div_le ..)
      obtain ⟨pbound,qbound⟩ := SumSignatureProbability.diameter large pq bal lower upper nonempty
      change _*(U-L) < _; omega
    · change _*(U-L) < _; omega

/-- The test defining this set and its sum target use only the input integer. -/
noncomputable def publicBases (n : ℕ) [NeZero n] : Finset (ZMod n)ˣ :=
  let L := ceilSqrt (4*n)
  let W := (9*n/2).sqrt-L
  univ.filter fun g => denominator W ((g:ZMod n)^(n+1-L)) (g:ZMod n) ≠ 0

/-- For this explicit product-only set of bases the measured first derivative
returns a proper gcd or gives p+q itself. The bound on its size is per input. -/
theorem public_run {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (large : 64≤p) (pq : p<q) (balance : q≤2*p) (qcap : q≤2^1024) :
    let n := p*q
    let L := ceilSqrt (4*n)
    let W := (9*n/2).sqrt-L
    1403*Fintype.card (ZMod n)ˣ < 5408*(publicBases n).card ∧
    ∀ g ∈ publicBases n, let y := (g:ZMod n)^(n+1-L)
                         let z := denominator W y (g:ZMod n)
                         (1<z.val.gcd n ∧ z.val.gcd n<n) ∨
                           (z.val.gcd n=1 ∧ L+(-baseTangent (range (W+1)) y (g:ZMod n)*z⁻¹).val=p+q) := by
  intro n L W
  let j := p+q-L
  obtain ⟨lo,hi⟩ := balanced_factorSum_bounds pq.le balance
  have low : L ≤ p+q := ceilSqrt_le_iff.mpr lo
  have upper : p+q ≤ (9*n/2).sqrt := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
    (by simpa only [mul_comm 2] using hi))
  have sj : j≤W := Nat.sub_le_sub_right upper _
  have under : p+q < n := by
    dsimp [n]
    have := Nat.mul_le_mul_right q (by omega : 3≤p)
    omega
  have jn : j<n := (Nat.sub_le ..).trans_lt under
  have hits (g : (ZMod n)ˣ) : (g:ZMod n)^j=(g:ZMod n)^(n+1-L) := by
    have group : g^j=g^(n+1-L) := by
      apply mul_left_cancel (a:=g^L)
      rw [← pow_add, ← pow_add, show L+j=p+q by dsimp [j]; omega,
        show L+(n+1-L)=n+1 by omega]
      exact unit_pow_factorSum hp.out hq.out pq.ne g
    simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val group
  have eq : useful n W j=publicBases n := by
    ext g
    simp only [useful, publicBases, mem_filter, mem_univ, true_and]
    rw [hits]
  constructor
  · rw [← eq]
    exact balanced ((Nat.coprime_primes hp.out hq.out).mpr pq.ne) large pq.le balance qcap sj
  · intro g hg y z
    obtain ok|⟨gcd,idx⟩ := decode g y (hits g) sj jn (eq ▸ hg)
    · exact Or.inl ok
    · exact Or.inr ⟨gcd, idx ▸ (show L+j=p+q by dsimp [j]; omega)⟩

end PrimeFactors.GeometricGeneratorFraction
