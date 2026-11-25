import PrimeFactors.Multiplier
import PrimeFactors.ReducedOffsetMinimum
import Mathlib.RingTheory.Coprime.Lemmas

namespace PrimeFactors.CompleteOffsetSearch

/-- A public candidate in the complete schedule. Its residual T*j-h*k may be negative. -/
def InSchedule (T h j k : ℕ) : Prop :=
  0<j ∧ j≤(4*h).sqrt ∧ 0<k ∧ k≤T*j/h+1 ∧ j.Coprime k

/-- The guard on the weighted square prevents a negative gap from becoming
zero under natural subtraction. Only verified proper divisors are returned. -/
def probe (N T j k : ℕ) : Option ℕ :=
  let S := j+2*T*k
  let target := 4*k^2*N
  let d := (S^2-target).sqrt
  let factor := N.gcd ((S-d)/2)
  if target≤S^2 ∧ d^2=S^2-target ∧ 1<factor ∧ factor<N then some factor else none

theorem probe_sound {N T j k d : ℕ} (hit : probe N T j k=some d) : 1<d ∧ d<N ∧ d ∣ N := by
  unfold probe at hit
  dsimp only at hit
  split at hit
  next good =>
    rw [← Option.some.inj hit]
    exact ⟨good.2.2.1,good.2.2.2,Nat.gcd_dvd_left ..⟩
  next => contradiction

/-- Integer upper endpoint. If k exceeded the quotient by two, the
nonnegative square D would force j²>4h. -/
theorem multiplier_cap {T h k j d : ℕ} (hp : 0<h) (kp : 0<k) (small : j^2≤4*h)
    (eq : j^2+4*k*T*j=4*k^2*h+d^2) : k≤T*j/h+1 := by
  have bound : (k-1)*h ≤ T*j := by
    by_contra! bad
    have full : T*j+h<h*k := by
      nlinarith only [bad,congrArg (fun x => x*h) (Nat.sub_add_cancel kp)]
    have enlarged := Nat.mul_lt_mul_of_pos_left full (Nat.mul_pos (by decide : 0<4) kp)
    have one := Nat.le_mul_of_pos_left h kp
    nlinarith only [enlarged,one,eq,small,Nat.zero_le (d^2)]
  have := (Nat.le_div_iff_mul_le hp).mpr bound
  omega

private theorem coprime_shift {j m r n b : ℕ} (eq : j+m*r=n+b*r) (cop : n.Coprime r) :
    j.Coprime r := by
  apply (Nat.coprime_add_mul_right_left j r m).mp
  rw [eq]
  exact (Nat.coprime_add_mul_right_left n r b).mpr cop

private theorem lower_root (a b : ℕ) : (a+b-Nat.dist a b)/2=min a b := by
  rcases le_total a b with h|h
  · rw [Nat.dist_eq_sub_of_le h,min_eq_left h]; omega
  · rw [Nat.dist_eq_sub_of_le_right h,min_eq_right h]; omega

/-- At a true witness the lower quadratic root is one of the two weighted
prime factors. Its gcd removes the unknown square coefficient. -/
theorem witness_of_small {p q T h s v j : ℕ} (pp : p.Prime) (qp : q.Prime)
    (root : T^2+h=p*q) (hp : 0<h) (sp : 0<s) (vp : 0<v) (sq : s<q) (vp' : v<p)
    (cop : s.Coprime v) (label : j+2*T*(s*v)=p*s^2+q*v^2) (jp : 0<j) (small : j^2≤4*h) :
    InSchedule T h j (s*v) ∧ (probe (p*q) T j (s*v)=some p ∨ probe (p*q) T j (s*v)=some q) := by
  let k := s*v
  let a := p*s^2
  let b := q*v^2
  let d := Nat.dist a b
  have kp : 0<k := Nat.mul_pos sp vp
  have cs : q.Coprime s := qp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt sp sq)
  have cv : p.Coprime v := pp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt vp vp')
  have prim : j.Coprime k := by
    apply Nat.coprime_mul_iff_right.mpr
    constructor
    · apply coprime_shift (r:=s) (m:=2*T*v) (b:=p*s) (n:=q*v^2) (by nlinarith only [label])
      exact Nat.coprime_mul_iff_left.mpr ⟨cs,cop.symm.pow_left 2⟩
    · apply coprime_shift (r:=v) (m:=2*T*s) (b:=q*v) (n:=p*s^2) (by nlinarith only [label])
      exact Nat.coprime_mul_iff_left.mpr ⟨cv,cop.pow_left 2⟩
  have identity : (a+b)^2=4*k^2*(p*q)+d^2 := by
    simpa only [a,b,d,k,mul_pow,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using
      multiplier_sum_square p q (s^2) (v^2)
  change j+2*T*k=a+b at label
  have eq : j^2+4*k*T*j=4*k^2*h+d^2 := by
    nlinarith only [congrArg (fun x => x^2) label,identity,congrArg (fun x => 4*k^2*x) root]
  refine ⟨⟨jp,Nat.le_sqrt'.mpr small,kp,multiplier_cap hp kp small eq,prim⟩,?_⟩
  have positiveGap : 4*k^2*(p*q)≤(a+b)^2 := by omega
  have gap : (a+b)^2-4*k^2*(p*q)=d^2 := by omega
  have ga : (p*q).gcd a=p := by
    simp only [a,Nat.gcd_mul_left,(cs.pow_right 2).gcd_eq_one,mul_one]
  have gb : (p*q).gcd b=q := by
    rw [Nat.mul_comm p q]; simp only [b,Nat.gcd_mul_left,(cv.pow_right 2).gcd_eq_one,mul_one]
  have psmall := lt_mul_of_one_lt_right pp.pos qp.one_lt
  have qsmall : q<p*q := by simpa only [Nat.mul_comm q p] using lt_mul_of_one_lt_right qp.pos pp.one_lt
  unfold probe
  dsimp only
  change (if 4*k^2*(p*q)≤(j+2*T*k)^2 ∧ _ then _ else _) = some p ∨ _
  rw [label, gap, Nat.sqrt_eq',lower_root]
  rcases le_total a b with h|h
  · left
    simp only [min_eq_left h,ga,pp.one_lt,psmall,positiveGap,and_self,if_true]
  · right
    have alt : 4*(s*v)^2*(p*q)≤(a+b)^2 := positiveGap
    simp only [min_eq_right h,gb,qp.one_lt,qsmall,positiveGap,alt,and_self,if_true]

private theorem coord_bound {P h : ℕ} {J x : ℤ} (pp : 0<P) (hp : 0<h) (tight : J<P)
    (mass : (h:ℤ)*x^2≤(P:ℤ)*J) : x.natAbs<P := by
  have hpos : 1≤(h:ℤ) := by exact_mod_cast hp
  have ppos : 0<(P:ℤ) := by exact_mod_cast pp
  have sq : x^2≤(h:ℤ)*x^2 := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hpos (sq_nonneg x)
  have lt := mul_lt_mul_of_pos_left tight ppos
  by_contra! bad
  have big : (P:ℤ)≤(x.natAbs:ℤ) := by exact_mod_cast bad
  have more := pow_le_pow_left₀ ppos.le big 2
  rw [Int.natCast_natAbs,sq_abs] at more
  nlinarith only [more,sq,mass,lt]

/-- A short signed vector necessarily has two nonzero coordinates of the
same sign. Its absolute coordinates satisfy the factor-size bounds. -/
theorem witness_of_signed {p q T h : ℕ} {x y J : ℤ} (pp : p.Prime) (qp : q.Prime)
    (root : T^2+h=p*q) (hp : 0<h) (cop : IsCoprime x y)
    (label : J=(p:ℤ)*x^2-2*(T:ℤ)*x*y+(q:ℤ)*y^2) (pos : 0<J)
    (lowP : J<p) (lowQ : J<q) (small : J^2≤4*(h:ℤ)) :
    ∃ k, InSchedule T h J.toNat k ∧ (probe (p*q) T J.toNat k=some p ∨ probe (p*q) T J.toNat k=some q) := by
  have rootZ : (T:ℤ)^2+(h:ℤ)=(p:ℤ)*q := by exact_mod_cast root
  have up := mul_nonneg (Nat.cast_nonneg (α:=ℤ) p) (sq_nonneg x)
  have vp := mul_nonneg (Nat.cast_nonneg (α:=ℤ) q) (sq_nonneg y)
  have prod : 0<x*y := by
    by_contra! neg
    have cross := mul_nonpos_of_nonneg_of_nonpos (show 0≤2*(T:ℤ) by positivity) neg
    by_cases state : x=0
    · have yn : y≠0 := by rintro rfl; rw [state] at label; nlinarith only [label,pos]
      have one : (1:ℤ)≤y^2 := Int.add_one_le_iff.mpr (sq_pos_of_ne_zero yn)
      nlinarith only [label,cross,up,lowQ,mul_le_mul_of_nonneg_left one (Nat.cast_nonneg (α:=ℤ) q)]
    · have one : (1:ℤ)≤x^2 := Int.add_one_le_iff.mpr (sq_pos_of_ne_zero state)
      nlinarith only [label,cross,vp,lowP,mul_le_mul_of_nonneg_left one (Nat.cast_nonneg (α:=ℤ) p)]
  have bx := coord_bound qp.pos hp lowQ (x:=x) (by
    nlinarith only [congrArg (fun t => (q:ℤ)*t) label,congrArg (fun t => x^2*t) rootZ,
      sq_nonneg ((q:ℤ)*y-T*x)])
  have by' := coord_bound pp.pos hp lowP (x:=y) (by
    nlinarith only [congrArg (fun t => (p:ℤ)*t) label,congrArg (fun t => y^2*t) rootZ,
      sq_nonneg ((p:ℤ)*x-T*y)])
  have xp : 0<x.natAbs := Int.natAbs_pos.mpr (by rintro rfl; simp at prod)
  have yp : 0<y.natAbs := Int.natAbs_pos.mpr (by rintro rfl; simp at prod)
  have cp : x.natAbs.Coprime y.natAbs := (Int.isCoprime_iff_gcd_eq_one.mp cop : x.gcd y=1)
  have val : J.toNat+2*T*(x.natAbs*y.natAbs)=p*x.natAbs^2+q*y.natAbs^2 := by
    apply Int.ofNat_inj.mp
    push_cast
    rw [Int.toNat_of_nonneg pos.le,← abs_mul,
      abs_of_pos prod,sq_abs,sq_abs]
    nlinarith only [label]
  refine ⟨_,witness_of_small pp qp root hp xp yp bx by' cp val (by omega) ?_⟩
  exact_mod_cast (show (J.toNat:ℤ)^2≤4*(h:ℤ) by rwa [Int.toNat_of_nonneg pos.le])

/-- At the product's floor square root the determinant is positive for
distinct primes. For balanced primes above 16, the short vector has value
less than either factor. -/
theorem balanced_parameters {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (ord : p<q) (balance : q≤2*p) (large : 17≤p) :
    let T := (p*q).sqrt
    let h := p*q-T^2
    T^2+h=p*q ∧ 0<h ∧ 4*h<p^2 := by
  let T := (p*q).sqrt
  let h := p*q-T^2
  have floor : T^2≤p*q := by simpa only [T,pow_two] using Nat.sqrt_le (p*q)
  have next : p*q<(T+1)^2 := Nat.lt_succ_sqrt' _
  have root : T^2+h=p*q := Nat.add_sub_of_le floor
  have off : 0<h := by
    by_contra! zero
    have eq : T^2=p*q := by omega
    obtain ⟨v,hv⟩ := pp.dvd_of_dvd_pow (show p ∣ T^2 from eq ▸ dvd_mul_right _ _)
    have rel : p*(p*v^2)=p*q := by rw [← eq,hv]; ring
    have divides : p ∣ q := ⟨v^2,(Nat.eq_of_mul_eq_mul_left pp.pos rel).symm⟩
    exact ord.ne ((Nat.prime_dvd_prime_iff_eq pp qp).mp divides)
  have upper : T≤q := by
    have bound := floor.trans (Nat.mul_le_mul_right q ord.le)
    exact Nat.mul_self_le_mul_self_iff.mp (by simpa only [pow_two] using bound)
  have count : h≤2*T := by nlinarith only [root,next]
  have pSq := Nat.mul_lt_mul_of_pos_right (show 16<p by omega) pp.pos
  exact ⟨root,off,by nlinarith only [count,upper,balance,pSq]⟩

/-- On every balanced product of distinct primes with smaller factor at least
17, a primitive public candidate decodes a prime. The reduced offset bound
and the positive floor-root correction are consequences of the input assumptions. -/
theorem complete_balanced {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (balance : q≤2*p) (large : 17≤p) :
    let N := p*q
    let T := N.sqrt
    let h := N-T^2
    ∃ j k, 3*j^2≤4*h ∧ InSchedule T h j k ∧ (probe N T j k=some p ∨ probe N T j k=some q) := by
  let T := (p*q).sqrt
  let h := p*q-T^2
  obtain ⟨root,off,cut⟩ := balanced_parameters pp qp ord balance large
  change T^2+h=p*q at root
  change 0<h at off
  change 4*h<p^2 at cut
  have rootZ : (p:ℤ)*q-(T:ℤ)^2=(h:ℤ) := by
    have eq : (T:ℤ)^2+h=(p:ℤ)*q := by exact_mod_cast root
    linarith only [eq]
  obtain ⟨x,y,pos,short,cop⟩ := ReducedOffsetMinimum.exists_small (p:=(p:ℤ)) (T:=(T:ℤ))
    (q:=(q:ℤ)) (h:=(h:ℤ)) (by exact_mod_cast pp.pos) (by exact_mod_cast off) rootZ
  let J := ReducedOffsetMinimum.Q p T q x y
  change 0<J at pos
  change 3*J^2≤4*(h:ℤ) at short
  have small : J^2≤4*(h:ℤ) := by nlinarith [sq_nonneg J]
  have narrow : J<(p:ℤ) := by
    have hlt : 4*(h:ℤ)<(p:ℤ)^2 := by exact_mod_cast cut
    by_contra! bad
    have := pow_le_pow_left₀ (Nat.cast_nonneg p) bad 2
    linarith only [small,hlt,this]
  obtain ⟨k,dom,found⟩ := witness_of_signed pp qp root off cop (rfl : J=_) pos narrow
    (narrow.trans (by exact_mod_cast ord)) small
  refine ⟨J.toNat,k,?_,dom,found⟩
  exact_mod_cast (show 3*(J.toNat:ℤ)^2≤4*(h:ℤ) by rwa [Int.toNat_of_nonneg pos.le])

/-- Either ordering of two distinct 1,024-bit primes is covered. The public
search can compute its offset range, multiplier range and gcds from N alone. -/
theorem complete_1024_bit_factors {N p q : ℕ} (pair : p*q=N) (pp : p.Prime) (qp : q.Prime)
    (distinct : p≠q) (pbits : 2^1023≤p ∧ p<2^1024) (qbits : 2^1023≤q ∧ q<2^1024) :
    let T := N.sqrt
    let h := N-T^2
    ∃ j k, 3*j^2≤4*h ∧ InSchedule T h j k ∧ (probe N T j k=some p ∨ probe N T j k=some q) := by
  have large : 17≤(2:ℕ)^1023 := by decide +kernel
  have twice : (2:ℕ)^1024=2*2^1023 := by decide +kernel
  rcases lt_or_gt_of_ne distinct with h|h
  · simpa only [pair] using complete_balanced pp qp h (by omega) (large.trans pbits.1)
  · have rev : q*p=N := (Nat.mul_comm ..).trans pair
    have back := complete_balanced qp pp h (by omega) (large.trans qbits.1)
    dsimp only at back ⊢
    rw [rev] at back
    obtain ⟨j,k,short,dom,found⟩ := back
    exact ⟨j,k,short,dom,found.symm⟩

/-- The extra multiplier is genuine: the residual for this primitive short
witness is negative. The integer discriminant is 49. -/
theorem slack_example : 94*23/181+1=12 ∧ InSchedule 94 181 23 12 ∧ probe 9017 94 23 12=some 71 := by
  refine ⟨by decide,?_,?_⟩
  · unfold InSchedule; decide +kernel
  · unfold probe; decide +kernel

end PrimeFactors.CompleteOffsetSearch
