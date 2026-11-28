import PrimeFactors.EqualityPatternSeparation
import PrimeFactors.SphereCircleIdentity
import PrimeFactors.SumGridPopulation
import PrimeFactors.UniformDivisorCount
import PrimeFactors.ChebyshevPrimeSample

/-! Two genuine balanced prime products with close, distinct modular circle orders.
The moduli differ and can be distinguished if they are revealed. -/
namespace PrimeFactors.CircleOrderNeighbors

open Finset MixedPrefixSample SphereCircleIdentity
open scoped Classical

attribute [local irreducible] eligible
set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

/-- Cardinality of the actual norm-one circle. Nat.card avoids a special convention for modulus zero. -/
noncomputable def size (N : ℕ) : ℕ := Nat.card {z : ZMod N×ZMod N // z.1^2+z.2^2=1}

def localSize (p : ℕ) : ℕ := if p%4=1 then p-1 else p+1

def order (z : ℕ×ℕ) : ℕ := localSize z.1*localSize z.2

private theorem data {p q : ℕ} (ok : (p,q)∈eligible) :
    2^1023≤p ∧ p<q ∧ q<2^1024 ∧ p.Prime ∧ q.Prime := by
  obtain ⟨lo,ord,hi,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp ok
  exact ⟨lo,ord,hi,pp,qp⟩

private theorem factor_int {p : ℕ} (pos : 0<p) :
    (localSize p:ℤ)=(p:ℤ)-ThreeSquareRadiusCounts.sign p := by
  unfold localSize ThreeSquareRadiusCounts.sign
  split <;> push_cast [show 1≤p by omega] <;> ring

/-- Identification with the actual finite circle uses the elementary field
count and CRT. It assumes no classical integer-sphere formula. -/
theorem size_eq_order {p q : ℕ} (ok : (p,q)∈eligible) : size (p*q)=order (p,q) := by
  obtain ⟨lo,lt,_,pp,qp⟩ := data ok
  letI : Fact p.Prime := ⟨pp⟩
  letI : Fact q.Prime := ⟨qp⟩
  let C := circle (ZMod (p*q)) 1
  have eqn : size (p*q)=C.card := by
    let e : {z : ZMod (p*q)×ZMod (p*q) // z.1^2+z.2^2=1} ≃ {z // z∈C} :=
      Equiv.subtypeEquivRight (fun z => (mem_circle (t:=(1:ZMod (p*q))) (w:=z)).symm)
    exact (Nat.card_congr e).trans (by simp)
  rw [eqn]
  have gt2 : 2<2^1023 := by decide +kernel
  have formula := semiprime lt.ne (by omega) (by omega) (isUnit_one : IsUnit (1:ZMod (p*q)))
  rw [←factor_int pp.pos,←factor_int qp.pos] at formula
  exact_mod_cast formula

private theorem local_bounds {p : ℕ} (lo : 2^1023≤p) (hi : p<2^1024) (pp : p.Prime) :
    2^1023≤localSize p ∧ localSize p≤2^1024 := by
  have gt2 : 2<2^1023 := by decide +kernel
  have odd := Nat.odd_iff.mp (pp.odd_of_ne_two (by omega))
  have notLower : (2^1023:ℕ)%2=0 := by decide +kernel
  unfold localSize
  split <;> omega

theorem bounds {z : ℕ×ℕ} (ok : z∈eligible) : 2^2046≤order z ∧ order z≤2^2048 := by
  obtain ⟨lo,lt,hi,pp,qp⟩ := data ok
  obtain ⟨p0,p1⟩ := local_bounds lo (lt.trans hi) pp
  obtain ⟨q0,q1⟩ := local_bounds (lo.trans lt.le) hi qp
  constructor
  · exact (show (2:ℕ)^2046=2^1023*2^1023 by rw [←pow_add]).le.trans (Nat.mul_le_mul p0 q0)
  · exact (Nat.mul_le_mul p1 q1).trans (show (2:ℕ)^1024*2^1024=2^2048 by rw [←pow_add]).le

private noncomputable def alternatives (a : ℕ) : Finset ℕ := {a-1,a+1}

private theorem source {p : ℕ} (pos : 0<p) : p∈alternatives (localSize p) := by
  simp only [localSize,alternatives,mem_insert,mem_singleton]
  split <;> omega

private theorem alternatives_card (a : ℕ) : (alternatives a).card≤2 :=
  (card_insert_le ..).trans (by simp)

/-- Each divisor chosen as the first local order fixes its partner. Each of
those two orders permits at most two possible primes. -/
theorem fiber (M : ℕ) (small : M<2^2049) :
    (eligible.filter fun z => order z=M).card≤2^242 := by
  by_cases zero : M=0
  · have emp : (eligible.filter fun z => order z=M)=∅ := eq_empty_of_forall_not_mem (fun z hz => by
      obtain ⟨ok,eq⟩ := mem_filter.mp hz
      have lower := (bounds ok).1
      have pos : 0<(2:ℕ)^2046 := by positivity
      omega)
    simp [emp]
  let box (a : ℕ) := alternatives a ×ˢ alternatives (M/a)
  have cover : (eligible.filter fun z => order z=M) ⊆ M.divisors.biUnion box := by
    intro z hz
    obtain ⟨ok,prod⟩ := mem_filter.mp hz
    obtain ⟨lo,lt,_,pp,qp⟩ := data ok
    change localSize z.1*localSize z.2=M at prod
    have gt : 1<(2:ℕ)^1023 := by decide +kernel
    have first : 0<localSize z.1 := by unfold localSize; split <;> omega
    have second : M/localSize z.1=localSize z.2 := by rw [←prod,Nat.mul_div_cancel_left _ first]
    exact mem_biUnion.mpr ⟨localSize z.1,Nat.mem_divisors.mpr ⟨prod ▸ dvd_mul_right ..,zero⟩,
      mem_product.mpr ⟨source pp.pos,second ▸ source qp.pos⟩⟩
  have cards (a : ℕ) (_ : a∈M.divisors) : (box a).card≤4 := by
    dsimp only [box]
    rw [card_product]
    exact Nat.mul_le_mul (alternatives_card _) (alternatives_card _)
  have count := (card_le_card cover).trans (card_biUnion_le_card_mul _ _ 4 cards)
  have cap := UniformDivisorCount.below_2049 (Nat.pos_of_ne_zero zero) small
  exact count.trans ((Nat.mul_le_mul_right 4 cap.le).trans (by decide +kernel))


private theorem count_image (A : Finset (ℕ×ℕ)) (f : ℕ×ℕ→ℕ)
    (fiberBound : ∀ z∈A,(A.filter fun w => f w=f z).card≤2^242) :
    A.card≤2^242*(A.image f).card := by
  apply card_le_mul_card_image_of_maps_to (f:=f) (fun z h => mem_image_of_mem f h)
  intro M hm
  obtain ⟨z,h,rfl⟩ := mem_image.mp hm
  exact fiberBound z h

private theorem prices {n v : ℕ} (pop : 2^2046<21000000*n) (price : n≤2^242*v) :
    2^1779+1<v := by
  by_contra! few
  have restrict := Nat.mul_le_mul_left 21000000 (price.trans (Nat.mul_le_mul_left _ few))
  have small : 21000000*((2^242)*(2^1779+1):ℕ)<2^2046 := by decide +kernel
  exact (pop.trans (restrict.trans_lt small)).false

private theorem bounded_fiber (z : ℕ×ℕ) (hz : z∈eligible) :
    (eligible.filter fun w => order w=order z).card≤2^242 :=
  fiber (order z) ((bounds hz).2.trans_lt (by decide +kernel : (2:ℕ)^2048<2^2049))

private theorem capacity : eligible.card≤2^242*(eligible.image order).card :=
  count_image eligible order bounded_fiber

private theorem many : 2^1779+1<(eligible.image order).card :=
  prices (n:=eligible.card) (v:=(eligible.image order).card) ChebyshevPrimeSample.eligible_count capacity

private theorem same_bin {a b w : ℕ} (wp : 0<w) (same : a/w=b/w) : b-a<w := by
  have lo := Nat.mod_add_div a w
  have hi := Nat.mod_add_div b w
  have gap := Nat.mod_lt b wp
  rw [same] at lo
  omega

/-- Two different eligible public products have distinct actual circle counts
less than 2^269 apart. The smaller count already has size at least 2^2046. -/
theorem neighbors : ∃ x∈eligible, ∃ y∈eligible, x.1*x.2≠y.1*y.2 ∧
    2^2046≤size (x.1*x.2) ∧ size (x.1*x.2)<size (y.1*y.2) ∧
    size (y.1*y.2)-size (x.1*x.2)<2^269 := by
  let bins := range (2^1779+1)
  have room : bins.card<(eligible.image order).card := by simpa [bins] using many
  have maps (M : ℕ) (h : M∈eligible.image order) : M/2^269∈bins := by
    obtain ⟨z,ok,rfl⟩ := mem_image.mp h
    apply mem_range.mpr
    have le := Nat.div_le_div_right (c:=(2:ℕ)^269) (bounds ok).2
    have endpt : (2^2048:ℕ)/2^269=2^1779 := by decide +kernel
    omega
  obtain ⟨a,ha,b,hb,diff,same⟩ := exists_ne_map_eq_of_card_lt_of_maps_to room maps
  have finish {a b : ℕ} (ha : a∈eligible.image order) (hb : b∈eligible.image order) (lt : a<b) (same : a/2^269=b/2^269) :
      ∃ x∈eligible, ∃ y∈eligible, x.1*x.2≠y.1*y.2 ∧
        2^2046≤size (x.1*x.2) ∧ size (x.1*x.2)<size (y.1*y.2) ∧
        size (y.1*y.2)-size (x.1*x.2)<2^269 := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hb
    have a := size_eq_order hx
    have b := size_eq_order hy
    refine ⟨x,hx,y,hy,?_,a ▸ (bounds hx).1,?_,?_⟩
    · intro eq
      exact lt.ne (a.symm.trans ((congrArg size eq).trans b))
    · simpa only [a,b] using lt
    · rw [a,b]
      exact same_bin (by positivity) same
  obtain ab|ba := lt_or_gt_of_ne diff
  · exact finish ha hb ab same
  · exact finish hb ha ba same.symm

/-- Average of a transcript test over actual words of t circle points. A choice
of enumeration names the points, but the test sees only pairwise equalities. -/
private noncomputable def mean (P : Type*) [Fintype P] (t : ℕ) (f : List ℕ→ℝ) : ℝ :=
  (∑ w : Fin t→P, f (EqualityPatternSampling.transcript ((Fintype.equivFin P) ∘ w))) /
    (Fintype.card P:ℝ)^t

private theorem mean_eq (P : Type*) [Fintype P] (t : ℕ) (f : List ℕ→ℝ) (pos : 0<Nat.card P) :
    mean P t f=EqualityPatternSampling.expect (Nat.card P) t 0 f := by
  rw [Nat.card_eq_fintype_card] at pos ⊢
  let e := Equiv.arrowCongr (Equiv.refl (Fin t)) (Fintype.equivFin P)
  have eqn := e.sum_comp (fun w => f (EqualityPatternSampling.transcript w))
  unfold mean
  rw [show (∑ w : Fin t→P, f (EqualityPatternSampling.transcript ((Fintype.equivFin P) ∘ w)))=
    ∑ w : Fin t→Fin (Fintype.card P), f (EqualityPatternSampling.transcript w) from eqn]
  exact EqualityPatternSampling.uniform pos f

/-- With a positive modulus, draw uniformly with replacement from its actual
circle and report the test's average acceptance probability. -/
noncomputable def acceptance (N t : ℕ) (f : List ℕ→ℝ) : ℝ :=
  if h : 0<N then
    letI : NeZero N := ⟨h.ne'⟩
    mean {z : ZMod N×ZMod N // z.1^2+z.2^2=1} t f
  else 0

private theorem acceptance_eq {N t : ℕ} (np : 0<N) (sp : 0<size N) (f : List ℕ→ℝ) :
    acceptance N t f=EqualityPatternSampling.expect (size N) t 0 f := by
  letI : NeZero N := ⟨np.ne'⟩
  rw [acceptance,dif_pos np]
  exact mean_eq _ t f sp

private theorem margin {m M t : ℕ} (cap : 2^2046≤m) (ord : m<M)
    (near : M-m<2^269) (sample : 2*t≤m) {A : ℝ}
    (bound : A^2≤(t:ℝ)^2*((M:ℝ)-m)^2/(m:ℝ)^3) : |A|<1/(2:ℝ)^755 := by
  have pos : 0<m := (Nat.two_pow_pos _).trans_le cap
  have dg : ((M-m)*2^754)^2<2^2046 := by
    have gap : (M-m)*2^754<2^1023 := (Nat.mul_lt_mul_of_pos_right near (Nat.two_pow_pos 754)).trans_eq
      (by rw [←pow_add])
    exact (Nat.pow_lt_pow_left gap (by decide : 2≠0)).trans_eq (by rw [←pow_mul])
  have nearM := dg.trans_le cap
  have norm : t^2*(M-m)^2*(2^755)^2<m^3 := calc
    _ = (2*t)^2*((M-m)*2^754)^2 := by
      rw [show (2:ℕ)^755=2^754*2 by rw [←pow_succ]]; ring
    _ ≤ m^2*((M-m)*2^754)^2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left sample 2)
    _ < m^2*m := Nat.mul_lt_mul_of_pos_left nearM (pow_pos pos _)
    _ = m^3 := by ring
  have cast : (t:ℝ)^2*((M:ℝ)-m)^2*((2:ℝ)^755)^2<(m:ℝ)^3 := by
    rw [←Nat.cast_sub ord.le]
    exact_mod_cast norm
  have mp : 0<(m:ℝ) := by exact_mod_cast pos
  apply (sq_lt_sq₀ (abs_nonneg _) (by positivity : 0≤1/(2:ℝ)^755)).mp
  rw [sq_abs]
  apply bound.trans_lt
  rw [div_pow,one_pow]
  exact (div_lt_div_iff₀ (pow_pos mp _) (by positivity)).mpr (by simpa only [one_mul] using cast)

/-- On one and the same pair of different genuine products, every anonymous
test has acceptance probabilities differing by less than 2^(-755), for all
draw counts through half the smaller circle. The product itself and the point
coordinates are excluded from the observer's input. -/
theorem blinded : ∃ x∈eligible, ∃ y∈eligible, x.1*x.2≠y.1*y.2 ∧
    2^2046≤size (x.1*x.2) ∧ size (x.1*x.2)<size (y.1*y.2) ∧
    size (y.1*y.2)-size (x.1*x.2)<2^269 ∧
    ∀ t, 2*t≤size (x.1*x.2) → ∀ f : List ℕ→ℝ, (∀ h,0≤f h ∧ f h≤1) →
      |acceptance (x.1*x.2) t f-acceptance (y.1*y.2) t f|<1/(2:ℝ)^755 := by
  obtain ⟨x,hx,y,hy,ne,cap,lt,gap⟩ := neighbors
  refine ⟨x,hx,y,hy,ne,cap,lt,gap,?_⟩
  intro t h f value
  have xp : 0<size (x.1*x.2) := (Nat.two_pow_pos _).trans_le cap
  obtain ⟨_,_,_,px,qx⟩ := data hx
  obtain ⟨_,_,_,py,qy⟩ := data hy
  rw [acceptance_eq (Nat.mul_pos px.pos qx.pos) xp, acceptance_eq (Nat.mul_pos py.pos qy.pos) (xp.trans lt)]
  exact margin cap lt gap h (EqualityPatternSeparation.test_gap xp lt.le h f value)

end PrimeFactors.CircleOrderNeighbors
