import PrimeFactors.Fermat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

/-! The constant-excess side of an affine pair reduces to an ordinary square
above a multiple of the product. A proper gcd assigns the unknown primes to
opposite halves of that square. -/
namespace PrimeFactors.AffineExcessSingle
open Finset

/-- Remove a constant square from the mixed square equality, including a
zero value of the other excess. -/
theorem remove_square {c z h : ℕ} (cp : 0<c) (square : z^2=c^2*h) :
    ∃ w, z=c*w ∧ w^2=h := by
  obtain ⟨w,hw⟩ := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp (show c^2 ∣ z^2 from ⟨h,square⟩)
  refine ⟨w,hw,?_⟩
  rw [hw,mul_pow] at square
  exact mul_left_cancel₀ (pow_ne_zero 2 cp.ne') square

private theorem square_parity (x : ℕ) : x^2%2=x%2 := by
  rw [pow_two]
  calc
    _ = (x%2*(x%2))%2 := Nat.mul_mod _ _ _
    _ = x%2 := by rcases Nat.mod_two_eq_zero_or_one x with h|h <;> rw [h]

/-- Both half-sums are integral; the smaller is exactly (w−d)/2. -/
theorem halves {w d H : ℕ} (square : w^2=4*H+d^2) :
    ∃ a, w=2*a+d ∧ a*(a+d)=H := by
  have below : d≤w := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (by omega)
  have same : w%2=d%2 := by
    rw [←square_parity w,square,←square_parity d]
    omega
  let a := (w-d)/2
  have split : w=2*a+d := by unfold a; omega
  refine ⟨a,split,?_⟩
  rw [split] at square
  nlinarith only [square]

private theorem prime_gcd (n : ℕ) {p : ℕ} (hp : p.Prime) :
    n.gcd p = if p∣n then p else 1 := by
  split
  · exact Nat.gcd_eq_right (by assumption)
  · exact (hp.coprime_iff_not_dvd.mpr (by assumption)).symm.gcd_eq_one

private theorem other_side {p a d H : ℕ} (hp : p.Prime) (pd : ¬p∣d)
    (factors : a*(a+d)=H) (div : p∣H) : p∣a+d ↔ ¬p∣a := by
  rw [←factors] at div
  refine ⟨fun had ha => pd ((Nat.dvd_add_iff_right ha).mpr had),?_⟩
  exact fun no => (hp.dvd_mul.mp div).resolve_left no

private theorem times_two_gcd {p q c : ℕ} (hp : p.Prime) (hq : q.Prime)
    (pq : p≠q) (cop : (2*c).Coprime (p*q)) (z : ℕ) :
    (c*(2*z)).gcd (p*q)=z.gcd p*z.gcd q := by
  rw [show c*(2*z)=(2*c)*z by ring,cop.gcd_mul_left_cancel,
    ((Nat.coprime_primes hp hq).mpr pq).gcd_mul]

/-- Both signs recover opposite primes on every proper split. If neither
splits, their gcds are one and the whole input in one order or the other. -/
theorem sign_gcds {p q c d v w : ℕ} (hp : p.Prime) (hq : q.Prime)
    (pq : p≠q) (cop : (2*c).Coprime (p*q)) (pd : ¬p∣d) (qd : ¬q∣d)
    (square : w^2=4*(v*(p*q))+d^2) :
    let m := (c*(w-d)).gcd (p*q)
    let h := (c*(w+d)).gcd (p*q)
    (m=p ∧ h=q) ∨ (m=q ∧ h=p) ∨ (m=1 ∧ h=p*q) ∨ (m=p*q ∧ h=1) := by
  obtain ⟨a,wa,fac⟩ := halves square
  have flipP := other_side hp pd fac ((dvd_mul_right p q).trans (dvd_mul_left (p*q) v))
  have flipQ := other_side hq qd fac ((dvd_mul_left q p).trans (dvd_mul_left (p*q) v))
  have cancel := times_two_gcd hp hq pq cop
  have minus : w-d=2*a := by omega
  have plus : w+d=2*(a+d) := by omega
  dsimp only
  rw [minus,plus,cancel,cancel,prime_gcd _ hp,prime_gcd _ hq,prime_gcd _ hp,prime_gcd _ hq]
  by_cases pa : p∣a <;> by_cases qa : q∣a <;> simp [pa,qa,flipP,flipQ]

/-- Under these hypotheses either sign of the gcd splits the semiprime
exactly when the other one does. -/
theorem signs_iff {p q c d v w : ℕ} (hp : p.Prime) (hq : q.Prime)
    (pq : p≠q) (cop : (2*c).Coprime (p*q)) (pd : ¬p∣d) (qd : ¬q∣d)
    (square : w^2=4*(v*(p*q))+d^2) :
    (1<(c*(w-d)).gcd (p*q) ∧ (c*(w-d)).gcd (p*q)<p*q) ↔
    (1<(c*(w+d)).gcd (p*q) ∧ (c*(w+d)).gcd (p*q)<p*q) := by
  have pl : p<p*q := by simpa using Nat.mul_lt_mul_of_pos_left hq.one_lt hp.pos
  have ql : q<p*q := by simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt hq.pos
  have po := hp.one_lt
  have qo := hq.one_lt
  rcases sign_gcds hp hq pq cop pd qd square with ⟨x,y⟩|⟨x,y⟩|⟨x,y⟩|⟨x,y⟩ <;>
    simp only [x,y] <;> omega

/-- With both slopes zero, w=d and the two gcds are N and one. -/
theorem zero_both {n c d w : ℕ} (square : w^2=d^2) (cop : (2*c*d).Coprime n) :
    (c*(w-d)).gcd n=n ∧ (c*(w+d)).gcd n=1 := by
  have eq : w=d := (Nat.pow_left_inj (by decide : 2≠0)).mp square
  rw [eq,Nat.sub_self,Nat.mul_zero,Nat.gcd_zero_left,show c*(d+d)=2*c*d by ring]
  exact ⟨rfl,cop.gcd_eq_one⟩

/-- A proper split in either sign yields a multiplier on each prime, with
their two multiples differing by the public integer d. -/
theorem split_factors {p q c d v w : ℕ} (hp : p.Prime) (hq : q.Prime)
    (pq : p≠q) (cop : (2*c).Coprime (p*q)) (pd : ¬p∣d) (qd : ¬q∣d) (vp : 0<v)
    (square : w^2=4*(v*(p*q))+d^2)
    (hit : (1<(c*(w-d)).gcd (p*q) ∧ (c*(w-d)).gcd (p*q)<p*q) ∨
      (1<(c*(w+d)).gcd (p*q) ∧ (c*(w+d)).gcd (p*q)<p*q)) :
    ∃ s t, 0<s ∧ 0<t ∧ s*t=v ∧ (s*p+d=t*q ∨ t*q+d=s*p) := by
  obtain ⟨a,wa,fac⟩ := halves square
  have pqp := Nat.mul_pos hp.pos hq.pos
  have flipP := other_side hp pd fac ((dvd_mul_right p q).trans (dvd_mul_left (p*q) v))
  have flipQ := other_side hq qd fac ((dvd_mul_left q p).trans (dvd_mul_left (p*q) v))
  have cancel := times_two_gcd hp hq pq cop
  have minus : w-d=2*a := by omega
  have plus : w+d=2*(a+d) := by omega
  rw [minus,plus,cancel,cancel,prime_gcd _ hp,prime_gcd _ hq,prime_gcd _ hp,prime_gcd _ hq] at hit
  have mixed : (p∣a ∧ q∣a+d) ∨ (q∣a ∧ p∣a+d) := by
    by_cases pa : p∣a <;> by_cases qa : q∣a <;> simp_all [flipP,flipQ]
  rcases mixed with ⟨⟨s,hs⟩,⟨t,ht⟩⟩|⟨⟨t,ht⟩,⟨s,hs⟩⟩
  · have prod : s*t=v := by
      apply mul_right_cancel₀ pqp.ne'
      calc s*t*(p*q)=(p*s)*(q*t) := by ring
           _ = _ := by rw [←hs,←ht,fac]
    exact ⟨s,t,by nlinarith,by nlinarith,prod,Or.inl (by simpa [Nat.mul_comm] using hs ▸ ht)⟩
  · have prod : s*t=v := by
      apply mul_right_cancel₀ pqp.ne'
      calc s*t*(p*q)=(q*t)*(p*s) := by ring
           _ = _ := by rw [←ht,←hs,fac]
    exact ⟨s,t,by nlinarith,by nlinarith,prod,Or.inr (by simpa [Nat.mul_comm] using ht ▸ hs)⟩

/-- The proper split is equivalent to the existence of an assignment with
the exact difference d. The sign-equivalence theorem gives the same assertion
for the plus gcd. -/
theorem assignment_iff {p q c d v w : ℕ} (hp : p.Prime) (hq : q.Prime)
    (pq : p≠q) (cop : (2*c).Coprime (p*q)) (pd : ¬p∣d) (qd : ¬q∣d) (vp : 0<v)
    (square : w^2=4*(v*(p*q))+d^2) :
    (1<(c*(w-d)).gcd (p*q) ∧ (c*(w-d)).gcd (p*q)<p*q) ↔
    ∃ s t, 0<s ∧ 0<t ∧ s*t=v ∧ (s*p+d=t*q ∨ t*q+d=s*p) := by
  refine ⟨fun h => split_factors hp hq pq cop pd qd vp square (Or.inl h),?_⟩
  rintro ⟨s,t,_,_,st,close⟩
  have prod : (s*p)*(t*q)=v*(p*q) := by rw [←st]; ring
  have sum : w=s*p+t*q := by
    apply (Nat.pow_left_inj (by decide : 2≠0)).mp
    rw [square,←prod]
    rcases close with gap|gap
    · rw [←gap]; ring
    · rw [←gap]; ring
  rcases close with gap|gap
  · have yes : p∣s*p := dvd_mul_left ..
    have no : ¬q∣s*p := by
      intro bad
      apply qd
      exact (Nat.dvd_add_iff_right bad).mpr (gap ▸ dvd_mul_left q t)
    rw [show w-d=2*(s*p) by omega,times_two_gcd hp hq pq cop,
      prime_gcd _ hp,prime_gcd _ hq,if_pos yes,if_neg no,mul_one]
    exact ⟨hp.one_lt,by simpa using Nat.mul_lt_mul_of_pos_left hq.one_lt hp.pos⟩
  · have yes : q∣t*q := dvd_mul_left ..
    have no : ¬p∣t*q := by
      intro bad
      apply pd
      exact (Nat.dvd_add_iff_right bad).mpr (gap ▸ dvd_mul_left p s)
    rw [show w-d=2*(t*q) by omega,times_two_gcd hp hq pq cop,
      prime_gcd _ hp,prime_gcd _ hq,if_neg no,if_pos yes,one_mul]
    exact ⟨hq.one_lt,by simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt hq.pos⟩

/-- Multipliers below V attached to balanced primes fall in a thin interval
at each denominator t. Both possible assignments of the two halves are allowed. -/
theorem position {p q X D d s t v V : ℕ} (px : X≤p) (ordered : p<q) (qx : q<2*X)
    (dD : d<D) (DX : D<X) (st : s*t=v) (under : v<V)
    (close : s*p+d=t*q ∨ t*q+d=s*p) :
    t≤s ∧ s≤2*t ∧ t≤(V-1).sqrt ∧ s*p<t*q+D ∧ t*q<s*p+D := by
  have near : s*p<t*q+D ∧ t*q<s*p+D := by rcases close with h|h <;> omega
  have ts : t≤s := by
    by_cases ok : t≤s
    · exact ok
    · have h := Nat.mul_le_mul (show s+1≤t by omega) ordered.le
      rw [Nat.add_mul, one_mul] at h
      omega
  have upper : s≤2*t := by
    by_cases ok : s≤2*t
    · exact ok
    · have lo := Nat.mul_le_mul_right p (show 2*t+1≤s by omega)
      have hi := Nat.mul_le_mul_left t (show q≤2*p by omega)
      rw [Nat.add_mul,one_mul] at lo
      rw [show t*(2*p)=2*t*p by ring] at hi
      omega
  refine ⟨ts,upper,Nat.le_sqrt'.mpr ?_,near⟩
  have h := Nat.mul_le_mul_right t ts
  rw [st, ←sq] at h
  omega

/-- A small d² gives the first square with root at or above sqrt(4vn). -/
theorem first_square {H X w d : ℕ} (size : X^2≤H) (short : d^2<4*X)
    (square : w^2=4*H+d^2) : w=ceilSqrt (4*H) := by
  let a := ceilSqrt (4*H)
  have le : a≤w := ceilSqrt_le_iff.mpr (by omega)
  have cover : 4*H≤a^2 := ceilSqrt_le_iff.mp (show ceilSqrt (4*H)≤a from le_rfl)
  have base : 2*X≤a := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (by
    nlinarith only [size,cover])
  change w=a
  by_cases eq : w=a
  · exact eq
  · have succ : a+1≤w := by omega
    have h := Nat.pow_le_pow_left succ 2
    nlinarith only [h,square,base,short,cover]

/-- At the eligible scale D²<4X the ordinary test starting at ceil(sqrt(4vn))
already examines this square, including d=0. -/
theorem first_square_balanced {p q X D v w d : ℕ} (px : X≤p) (qx : X≤q)
    (vp : 0<v) (small : d≤D) (room : D^2<4*X) (square : w^2=4*(v*(p*q))+d^2) :
    w=ceilSqrt (4*(v*(p*q))) := by
  apply first_square (X:=X) _ ((Nat.pow_le_pow_left small 2).trans_lt room) square
  rw [sq]
  exact (Nat.mul_le_mul px qx).trans (Nat.le_mul_of_pos_left _ vp)

private theorem cell_card {T : Finset ℕ} {p s t D : ℕ} (tp : 0<t)
    (close : ∀ q∈T, s*p<t*q+D ∧ t*q<s*p+D) : T.card≤(2*D)/t+1 := by
  rcases T.eq_empty_or_nonempty with zero|nonempty
  · simp [zero]
  let lo := T.min' nonempty
  let hi := T.max' nonempty
  have low := close lo (T.min'_mem _)
  have high := close hi (T.max'_mem _)
  have sub : T ⊆ Icc lo hi := fun q h => mem_Icc.mpr ⟨T.min'_le _ h,T.le_max' _ h⟩
  have size : T.card ≤ hi+1-lo := by simpa only [Nat.card_Icc] using card_le_card sub
  have order : lo≤hi := T.le_max' _ (T.min'_mem _)
  have width : hi-lo≤2*D/t := by
    apply (Nat.le_div_iff_mul_le tp).mpr
    rw [mul_comm, Nat.mul_sub_left_distrib]
    omega
  omega

private theorem budget_sum (D T : ℕ) :
    ∑ i∈range T, (4*D+2*(i+1)) = 4*D*T+T*(T+1) := by
  induction T with
  | zero => simp
  | succ T ih => rw [sum_range_succ,ih]; ring

/-- Count all possible partners at one fixed prime, without assuming
independence of the slopes selected for different products. -/
theorem partner_count (Q : Finset ℕ) {p D T : ℕ}
    (cover : ∀ q∈Q, ∃ s t : ℕ, 0<t ∧ t≤T ∧ t≤s ∧ s≤2*t ∧
      s*p<t*q+D ∧ t*q<s*p+D) : Q.card≤4*D*T+T*(T+1) := by
  classical
  let row (t s : ℕ) := Q.filter fun q => s*p<t*q+D ∧ t*q<s*p+D
  let layer (i : ℕ) := (Icc (i+1) (2*(i+1))).biUnion (row (i+1))
  have sub : Q⊆(range T).biUnion layer := by
    intro q h
    obtain ⟨s,t,tp,tT,low,high,cl⟩ := cover q h
    have index : t-1+1=t := by omega
    apply mem_biUnion.mpr ⟨t-1,mem_range.mpr (by omega),?_⟩
    dsimp only [layer]
    rw [index]
    exact mem_biUnion.mpr ⟨s,mem_Icc.mpr ⟨low,high⟩,mem_filter.mpr ⟨h,cl⟩⟩
  apply (card_le_card sub).trans
  apply card_biUnion_le.trans
  rw [←budget_sum]
  apply sum_le_sum
  intro i _
  let t := i+1
  have tp : 0<t := Nat.succ_pos _
  have sc : (Icc t (2*t)).card=t+1 := by rw [Nat.card_Icc]; omega
  have count : (layer i).card ≤ (Icc t (2*t)).card*(2*D/t+1) :=
    card_biUnion_le_card_mul _ _ _ (fun s _ => cell_card tp (fun _ h => (mem_filter.mp h).2))
  rw [sc] at count
  apply count.trans
  have flat := Nat.mul_le_mul_right (2*D/t+1) (show t+1≤2*t by omega)
  have per := Nat.div_mul_le_self (2*D) t
  change _ ≤ 4*D+2*t
  nlinarith only [flat,per]

/-- The positive-slope event, allowing either sign in the gcd readout. -/
def SingleHit (p q D V : ℕ) : Prop :=
  ∃ c d v w : ℕ, 0<c ∧ c<D ∧ 0<d ∧ d<D ∧ 0<v ∧ v<V ∧
    w^2=4*(v*(p*q))+d^2 ∧
    ((1<(c*(w-d)).gcd (p*q) ∧ (c*(w-d)).gcd (p*q)<p*q) ∨
     (1<(c*(w+d)).gcd (p*q) ∧ (c*(w+d)).gcd (p*q)<p*q))

/-- An unconditional count for the partners of a fixed smaller prime. The
four search parameters may all depend on the input. -/
theorem prime_partners {p X D V : ℕ} (pp : p.Prime) (px : X≤p) (small : D<X)
    (Q : Finset ℕ) (members : ∀ q∈Q, q.Prime ∧ p<q ∧ q<2*X ∧ SingleHit p q D V) :
    Q.card≤4*D*(V-1).sqrt+(V-1).sqrt*((V-1).sqrt+1) := by
  apply partner_count Q (p:=p)
  intro q hq
  obtain ⟨qp,order,bound,c,d,v,w,cp,cD,dp,dD,vp,vV,square,hit⟩ := members q hq
  have smallcop (r : ℕ) (prime : r.Prime) (big : X≤r) : (2*c).Coprime r := by
    apply (Nat.coprime_mul_iff_left).mpr
    exact ⟨(prime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))).symm,
      (prime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt cp (by omega))).symm⟩
  have cop := Nat.coprime_mul_iff_right.mpr ⟨smallcop p pp px,smallcop q qp (px.trans order.le)⟩
  obtain ⟨s,t,_,tp,st,gap⟩ := split_factors pp qp order.ne cop
    (Nat.not_dvd_of_pos_of_lt dp (by omega)) (Nat.not_dvd_of_pos_of_lt dp (by omega)) vp square hit
  obtain ⟨ts,cap,tt,near⟩ := position px order bound dD small st vV gap
  exact ⟨s,t,tp,tt,ts,cap,near⟩

/-- A finite set of first primes gives a product-level pair count. The
upper bound permits every possible partner at every first prime. -/
theorem prime_pairs {X D V : ℕ} (small : D<X) (first : Finset ℕ) (S : Finset (ℕ×ℕ))
    (starts : ∀ p∈first, p.Prime ∧ X≤p)
    (members : ∀ z∈S, z.1∈first ∧ z.2.Prime ∧ z.1<z.2 ∧ z.2<2*X ∧
      SingleHit z.1 z.2 D V) :
    S.card ≤ first.card*(4*D*(V-1).sqrt+(V-1).sqrt*((V-1).sqrt+1)) := by
  classical
  let partners (p : ℕ) := (S.filter (fun z => z.1=p)).image Prod.snd
  let row (p : ℕ) := (partners p).image (fun q => (p,q))
  have sub : S⊆first.biUnion row := by
    intro z hz
    apply mem_biUnion.mpr ⟨z.1,(members z hz).1,?_⟩
    exact mem_image.mpr ⟨z.2,mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,rfl⟩,rfl⟩,rfl⟩
  apply (card_le_card sub).trans
  apply card_biUnion_le_card_mul
  intro p hp
  apply card_image_le.trans
  apply prime_partners (starts p hp).1 (starts p hp).2 small
  intro q hq
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
  obtain ⟨inside,rz⟩ := mem_filter.mp hz
  rw [←rz]
  exact (members z inside).2

end PrimeFactors.AffineExcessSingle
