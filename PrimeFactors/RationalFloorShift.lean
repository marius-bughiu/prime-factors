import PrimeFactors.FloorSquareShiftPopulation

/-! Rational shifts at the unscaled floor square root. A denominator budget
covers a finite population even when the numerator is unconstrained. -/
namespace PrimeFactors.RationalFloorShift
open Finset FloorSquareShift
open private PrimeFactors.FloorSquareShift.floor_bounds from PrimeFactors.FloorSquareShift
open private PrimeFactors.FloorSquareShiftPopulation.square_sum_aux
  PrimeFactors.FloorSquareShiftPopulation.root_sum_aux from PrimeFactors.FloorSquareShiftPopulation
open scoped Classical

/-- This is an equality over the rationals at r=floor(sqrt(p*q)); its
only possible shift solves h times the true sum excess equal to D. -/
theorem rational_shift_iff {p q : ℕ} (lt : p<q) (h : ℚ) :
    ((p:ℚ)-h)*((q:ℚ)-h)=(((p*q).sqrt:ℚ)-h)^2 ↔
      h*(excess p q:ℚ)=(FloorSquareShift.residual (p*q):ℚ) := by
  have sum := (PrimeFactors.FloorSquareShift.floor_bounds lt).2.2.le
  have below := Nat.sqrt_le' (p*q)
  simp only [excess,FloorSquareShift.residual,Nat.cast_sub sum,Nat.cast_sub below,
    Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  constructor <;> intro eqn <;> linear_combination -eqn

/-- A witness may use any common positive divisor g, including gcd(D,J) for the reduced shift. -/
def Witness (p q a b g : ℕ) : Prop :=
  0<a ∧ 0<b ∧ 0<g ∧ residual (p*q)=a*g ∧ excess p q=b*g

/-- The gcd constructs the unique reduced numerator and denominator of D/J. -/
theorem reduced {p q : ℕ} (lt : p<q) (pos : 0<residual (p*q)) :
    let D := residual (p*q)
    let J := excess p q
    let g := D.gcd J
    Witness p q (D/g) (J/g) g ∧ (D/g).Coprime (J/g) := by
  let D := residual (p*q)
  let J := excess p q
  let g := D.gcd J
  have jp : 0<J := Nat.sub_pos_of_lt (PrimeFactors.FloorSquareShift.floor_bounds lt).2.2
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ pos
  have da : g∣D := Nat.gcd_dvd_left ..
  have jb : g∣J := Nat.gcd_dvd_right ..
  exact ⟨⟨Nat.div_pos (Nat.le_of_dvd pos da) gp,Nat.div_pos (Nat.le_of_dvd jp jb) gp,gp,
    (Nat.div_mul_cancel da).symm,(Nat.div_mul_cancel jb).symm⟩,Nat.coprime_div_gcd_div_gcd gp⟩

private theorem product_square {A B t : ℕ} (pa : 0<A) (pb : 0<B) (eqn : A*B=t^2) :
    ∃ u x l : ℕ, 0<u ∧ 0<x ∧ 0<l ∧ A=u*x^2 ∧ B=u*l^2 ∧ t=u*x*l := by
  obtain ⟨u,m,n,x,l,up,mp,np,xp,lp,aa,bb,_,mn,_,_⟩ :=
    SquareScalePairCoordinates.coordinates (t:=1) (L:=1) (y:=t) pa pb zero_lt_one le_rfl
      (by simpa only [one_mul] using eqn)
  have mn1 := Nat.eq_one_of_dvd_one mn
  obtain rfl : m=1 := Nat.eq_one_of_dvd_one (mn1 ▸ dvd_mul_right m n)
  simp only [one_mul] at mn1
  subst n
  simp only [mul_one] at aa bb
  refine ⟨u,x,l,up,xp,lp,aa,bb,?_⟩
  apply (Nat.pow_left_inj (by decide : 2≠0)).mp
  rw [←eqn,aa,bb]; ring

/-- After clearing b, the positive square coordinates are x and x+b*l. -/
theorem coordinates {p q a b g : ℕ} (lt : p<q) (hit : Witness p q a b g)
    (proper : a<b*p) :
    ∃ u x l : ℕ, 0<u ∧ 0<x ∧ 0<l ∧ b*p=a+u*x^2 ∧
      b*q=a+u*(x+b*l)^2 ∧ g=u*l^2 ∧ (p*q).sqrt=p+u*x*l := by
  obtain ⟨ap,bp,gp,d,j⟩ := hit
  have lo := (PrimeFactors.FloorSquareShift.floor_bounds lt).1
  have sum := (PrimeFactors.FloorSquareShift.floor_bounds lt).2.2
  have eqn := excess_identity lt
  rw [d,j] at eqn
  have step : (b*p-a)*g=((p*q).sqrt-p)^2 := by
    have form : b*p*g=a*g+((p*q).sqrt-p)^2 := by rw [eqn]; ring
    rw [Nat.sub_mul,form,Nat.add_sub_cancel_left]
  obtain ⟨u,x,l,up,xp,lp,pp,gg,center⟩ := product_square (Nat.sub_pos_of_lt proper) gp step
  have P : b*p=a+u*x^2 := by omega
  have R : (p*q).sqrt=p+u*x*l := by omega
  have J : p+q=2*(p*q).sqrt+b*g := by unfold excess at j; omega
  refine ⟨u,x,l,up,xp,lp,P,?_,gg,R⟩
  rw [R,gg] at J
  have Q : q=p+2*(u*x*l)+b*(u*l^2) := by omega
  rw [Q,Nat.mul_add,Nat.mul_add,P]; ring

/-- Denominator times the smaller factor bounds the numerator. Equality is a near pair. -/
theorem edge {p q a b g : ℕ} (lt : p<q) (hit : Witness p q a b g) (big : b*p≤a) :
    q≤p+2 := by
  obtain ⟨ap,bp,gp,d,j⟩ := hit
  have ident := excess_identity lt
  rw [d,j] at ident
  have mono := Nat.mul_le_mul_right g big
  have le := (PrimeFactors.FloorSquareShift.floor_bounds lt).1
  have r : (p*q).sqrt=p := by
    by_contra h
    have sq := pow_pos (Nat.sub_pos_of_lt (by omega : p<(p*q).sqrt)) 2
    nlinarith only [mono,ident,sq]
  have upper := Nat.lt_succ_sqrt' (p*q)
  rw [r] at upper
  have pos : 0<p := by
    apply Nat.pos_of_ne_zero
    intro z
    rw [z,zero_mul] at d
    have zD : FloorSquareShift.residual 0=0 := by decide
    exact (Nat.mul_pos ap gp).ne' (zD ▸ d.symm)
  exact Nat.le_of_mul_le_mul_left (by nlinarith only [upper] : p*q≤p*(p+2)) pos


private noncomputable def block (H b u l : ℕ) : Finset (ℕ×ℕ) :=
  ((Icc 1 ((b*H/u).sqrt)) ×ˢ (Icc 1 (3*H/(b*u*l^2)))).image fun w =>
    let p := u*w.1^2/b+w.2
    (p,p+2*(u*w.1*l)+b*(u*l^2))

private noncomputable def cover (H b : ℕ) : Finset (ℕ×ℕ) :=
  (Icc 1 H).biUnion fun u => (Icc 1 H).biUnion fun l => block H b u l

private theorem member {p q a b g H : ℕ} (lt : p<q) (qh : q≤H)
    (hit : Witness p q a b g) (proper : a<b*p) : (p,q)∈cover H b := by
  obtain ⟨u,x,l,up,xp,lp,P,Q,gg,R⟩ := coordinates lt hit proper
  obtain ⟨ap,bp,gp,D,J⟩ := hit
  rw [gg] at D J
  have sum := (PrimeFactors.FloorSquareShift.floor_bounds lt).2.2
  have eqSum : p+q=2*(p*q).sqrt+b*(u*l^2) := by unfold excess at J; omega
  rw [R] at eqSum
  have qeq : q=p+2*(u*x*l)+b*(u*l^2) := by omega
  have bound : b*(u*l^2) ≤ H := by omega
  have us : u≤H := (Nat.le_mul_of_pos_right u (pow_pos lp 2)).trans
    ((Nat.le_mul_of_pos_left _ bp).trans bound)
  have ls : l≤H := (Nat.le_self_pow (by decide : 2≠0) l).trans
    ((Nat.le_mul_of_pos_left _ up).trans ((Nat.le_mul_of_pos_left _ bp).trans bound))
  have xb : x≤(b*H/u).sqrt := by
    apply Nat.le_sqrt'.mpr
    apply (Nat.le_div_iff_mul_le up).mpr
    rw [Nat.mul_comm]
    exact (Nat.le_add_left _ _).trans (P ▸ Nat.mul_le_mul_left b (lt.le.trans qh))
  let i := p-u*x^2/b
  have modsum := Nat.mod_add_div (u*x^2) b
  have ppos : u*x^2/b < p := (Nat.div_lt_iff_lt_mul bp).mpr (by rw [Nat.mul_comm p b,P]; omega)
  have rep : u*x^2/b+i=p := by dsimp [i]; omega
  have bi : b*i=a+(u*x^2)%b := by
    have factored := congrArg (b*·) rep
    dsimp only at factored
    rw [Nat.mul_add,P] at factored
    omega
  have ihi : i ≤ 3*H/(b*u*l^2) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    have rhi := (PrimeFactors.FloorSquareShift.floor_bounds lt).2.1.trans qh
    have excess_bound := Nat.sqrt_le_add (p*q)
    have below := Nat.sqrt_le' (p*q)
    have dcap : residual (p*q) ≤ 2*H := by
      unfold FloorSquareShift.residual
      rw [←sq] at excess_bound
      omega
    have top : (u*x^2)%b*(u*l^2) ≤ H :=
      (Nat.mul_le_mul_right _ (Nat.mod_lt _ bp).le).trans bound
    calc
      i*(b*u*l^2) = (b*i)*(u*l^2) := by ring
      _ = a*(u*l^2)+(u*x^2)%b*(u*l^2) := by rw [bi,Nat.add_mul]
      _ ≤ 3*H := by omega
  apply mem_biUnion.mpr
  refine ⟨u,mem_Icc.mpr ⟨up,us⟩,mem_biUnion.mpr ⟨l,mem_Icc.mpr ⟨lp,ls⟩,?_⟩⟩
  exact mem_image.mpr ⟨(x,i),mem_product.mpr ⟨mem_Icc.mpr ⟨xp,xb⟩,
    mem_Icc.mpr ⟨by dsimp [i]; omega,ihi⟩⟩,by dsimp; rw [rep,qeq]⟩

private theorem block_bound (H b u l : ℕ) (bp : 0<b) :
    ((block H b u l).card : ℝ) ≤
      (3*H*Real.sqrt H/Real.sqrt b)*(1/((u:ℝ)*Real.sqrt u))*(1/(l:ℝ)^2) := by
  have count : (block H b u l).card ≤ (b*H/u).sqrt*(3*H/(b*u*l^2)) :=
    card_image_le.trans_eq (by simp only [card_product,Nat.card_Icc,Nat.add_sub_cancel])
  have xr := (Real.nat_sqrt_le_real_sqrt (a:=b*H/u)).trans
    (Real.sqrt_le_sqrt (Nat.cast_div_le (α:=ℝ) (m:=b*H) (n:=u)))
  rw [Nat.cast_mul,Real.sqrt_div (by positivity),Real.sqrt_mul (by positivity)] at xr
  have ir := (Nat.cast_div_le (α:=ℝ) (m:=3*H) (n:=b*u*l^2))
  push_cast at ir
  have cnt := (Nat.cast_le (α:=ℝ)).mpr count
  push_cast at cnt
  apply cnt.trans ((mul_le_mul xr ir (by positivity) (by positivity)).trans_eq ?_)
  have bs : 0 < Real.sqrt b := Real.sqrt_pos.mpr (by exact_mod_cast bp)
  have b_eq := Real.sq_sqrt (Nat.cast_nonneg b)
  have cancel : Real.sqrt b/(b:ℝ)=1/Real.sqrt b := by
    apply (div_eq_div_iff (by positivity) bs.ne').mpr
    simpa only [←sq,one_mul] using b_eq
  calc
    _ = 3*H*Real.sqrt H*(Real.sqrt b/b)*(1/((u:ℝ)*Real.sqrt u))*(1/(l:ℝ)^2) := by
      simp only [div_eq_mul_inv,mul_inv_rev]; ring
    _ = _ := by rw [cancel]; ring

private theorem cover_bound (H b : ℕ) (hp : 0<H) (bp : 0<b) :
    ((cover H b).card:ℝ) ≤ 18*H*Real.sqrt H/Real.sqrt b := by
  have n : (cover H b).card ≤ ∑ u∈Icc 1 H, ∑ l∈Icc 1 H,(block H b u l).card :=
    card_biUnion_le.trans (sum_le_sum fun _ _ => card_biUnion_le)
  have nr := (Nat.cast_le (α:=ℝ)).mpr n
  push_cast at nr
  apply nr.trans
  let c := 3*H*Real.sqrt H/Real.sqrt b
  let f (u : ℕ) := 1/((u:ℝ)*Real.sqrt u)
  let g (l : ℕ) := 1/(l:ℝ)^2
  have both : (∑ u∈Icc 1 H,f u)*(∑ l∈Icc 1 H,g l) ≤ 3*2 := by
    apply mul_le_mul _ _ (by dsimp [g]; positivity) (by norm_num)
    · exact (PrimeFactors.FloorSquareShiftPopulation.root_sum_aux hp).trans (sub_le_self _ (by positivity))
    · exact (PrimeFactors.FloorSquareShiftPopulation.square_sum_aux hp).trans (sub_le_self _ (by positivity))
  calc
    _ ≤ ∑ u∈Icc 1 H,∑ l∈Icc 1 H,c*f u*g l :=
      sum_le_sum fun u _ => sum_le_sum fun l _ => block_bound H b u l bp
    _ = c*((∑ u∈Icc 1 H,f u)*(∑ l∈Icc 1 H,g l)) := by
      simp_rw [←mul_sum]; rw [←sum_mul,←mul_sum,mul_assoc]
    _ ≤ c*(3*2) := mul_le_mul_of_nonneg_left both (by dsimp [c]; positivity)
    _ = _ := by dsimp [c]; ring

private theorem sqrt_sum (B : ℕ) : ∑ b∈Icc 1 B, 1/Real.sqrt b ≤ 2*Real.sqrt B := by
  induction B with
  | zero => norm_num
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1≤n+1),Nat.cast_succ]
    let a := Real.sqrt n
    let b := Real.sqrt ((n:ℝ)+1)
    have bp : 0<b := Real.sqrt_pos.mpr (by positivity)
    have ab : a≤b := Real.sqrt_le_sqrt (by linarith)
    have sa : a^2=(n:ℝ) := Real.sq_sqrt (by positivity)
    have sb : b^2=(n:ℝ)+1 := Real.sq_sqrt (by positivity)
    have term : 1/b ≤ 2*(b-a) := (div_le_iff₀ bp).mpr (by
      nlinarith only [sa,sb,sq_nonneg (b-a)])
    change _+1/b≤2*b
    change _≤2*a at ih
    linarith only [ih,term]

/-- Height and denominator budget bound all successes before requiring primality. -/
theorem finite_count (H B : ℕ) (hp : 0<H) (A : Finset (ℕ×ℕ))
    (data : ∀ v∈A,v.1<v.2 ∧ v.2≤H ∧ ∃ a b g, b≤B ∧ Witness v.1 v.2 a b g) :
    (A.card:ℝ) ≤ 36*H*Real.sqrt H*Real.sqrt B+2*H := by
  let endPairs := ((Icc 1 H) ×ˢ (Icc 1 2)).image (fun t : ℕ×ℕ => (t.1,t.1+t.2))
  let mid := (Icc 1 B).biUnion (cover H)
  have sub : A ⊆ mid ∪ endPairs := by
    rintro ⟨p,q⟩ h
    obtain ⟨lt,qh,a,b,g,budget,hit⟩ := data _ h
    dsimp only at lt qh hit
    by_cases proper : a<b*p
    · exact mem_union_left _ (mem_biUnion.mpr
        ⟨b,mem_Icc.mpr ⟨hit.2.1,budget⟩,member lt qh hit proper⟩)
    · have gap := edge lt hit (by omega)
      have pp : 0<p := by
        apply Nat.pos_of_ne_zero
        intro z
        obtain ⟨ap,_,gp,d,_⟩ := hit
        rw [z,zero_mul] at d
        have zD : FloorSquareShift.residual 0=0 := by decide
        exact (Nat.mul_pos ap gp).ne' (zD ▸ d.symm)
      exact mem_union_right _ (mem_image.mpr ⟨(p,q-p),mem_product.mpr
        ⟨mem_Icc.mpr ⟨pp,lt.le.trans qh⟩,mem_Icc.mpr ⟨by omega,by omega⟩⟩,
        Prod.ext rfl (by dsimp; omega)⟩)
  have ecard : endPairs.card≤2*H :=
    card_image_le.trans_eq (by simp only [card_product,Nat.card_Icc,Nat.add_sub_cancel,Nat.mul_comm])
  have raw : mid.card≤∑ b∈Icc 1 B,(cover H b).card := card_biUnion_le
  have m := (Nat.cast_le (α:=ℝ)).mpr raw
  push_cast at m
  have m2 := sum_le_sum (s:=Icc 1 B) (fun b hb => cover_bound H b hp (mem_Icc.mp hb).1)
  have combo := (card_le_card sub).trans ((card_union_le _ _).trans (Nat.add_le_add_left ecard _))
  have lhs := (Nat.cast_le (α:=ℝ)).mpr combo
  push_cast at lhs
  apply lhs.trans (add_le_add_right _ _)
  apply (m.trans m2).trans
  have split : (∑ b∈Icc 1 B,(18*H*Real.sqrt H/Real.sqrt b)) =
      (18*H*Real.sqrt H)*(∑ b∈Icc 1 B,1/Real.sqrt b) := by
    rw [mul_sum]; apply sum_congr rfl; intro _ _; ring
  rw [split]
  exact (mul_le_mul_of_nonneg_left (sqrt_sum B) (by positivity)).trans_eq (by ring)

/-- The smallest possible (positive) denominator, including non-reduced presentations. -/
def denominator (p q : ℕ) : ℕ := excess p q/((FloorSquareShift.residual (p*q)).gcd (excess p q))

/-- Bounding the reduced denominator is equivalent to the existence of a bounded witness. -/
theorem menu_iff {p q B : ℕ} (lt : p<q) (pos : 0<FloorSquareShift.residual (p*q)) :
    (∃ a b g, b≤B ∧ Witness p q a b g) ↔ denominator p q ≤ B := by
  constructor
  · rintro ⟨a,b,g,budget,ap,bp,gp,d,j⟩
    have gd := Nat.dvd_gcd (d ▸ dvd_mul_left g a) (j ▸ dvd_mul_left g b)
    have gc := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left (excess p q) pos) gd
    calc
      denominator p q ≤ excess p q/g := Nat.div_le_div_left gc gp
      _ = b := by rw [j,Nat.mul_div_cancel _ gp]
      _ ≤ B := budget
  · intro small
    exact ⟨_,_,_,small,(reduced lt pos).1⟩

/-- Distinct primes rule out a zero remainder, so the canonical reduced
shift exists for every product in the stated population. -/
theorem positive_remainder {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q) :
    0<FloorSquareShift.residual (p*q) := by
  apply Nat.sub_pos_of_lt
  refine lt_of_le_of_ne (Nat.sqrt_le' _) ?_
  intro square
  have div : p∣((p*q).sqrt)^2 := (dvd_mul_right p q).trans (dvd_of_eq square.symm)
  obtain ⟨c,cc⟩ := pp.dvd_of_dvd_pow div
  have eqn : p*(p*c^2)=p*q := by
    calc
      _ = (p*c)^2 := by ring
      _ = p*q := (congrArg (fun z : ℕ => z^2) cc).symm.trans square
  have qeq := Nat.eq_of_mul_eq_mul_left pp.pos eqn
  have pq : p∣q := ⟨c^2,qeq.symm⟩
  exact lt.ne ((Nat.prime_dvd_prime_iff_eq pp qp).mp pq)

open MixedPrefixSample
open private PrimeFactors.MonotoneSumPopulation.data from PrimeFactors.MonotoneSumPopulation
attribute [local irreducible] eligible MixedPrefixSample.primes
set_option exponentiation.threshold 8192

noncomputable def successes (B : ℕ) : Finset (ℕ×ℕ) := by
  classical exact eligible.filter fun z => ∃ a b g, b≤B ∧ Witness z.1 z.2 a b g

/-- With all denominators through 2^128 available, the accepted share
of the full-width prime population is below 2^-416. -/
theorem full_width : 2^416*(successes (2^128)).card < eligible.card := by
  classical
  have pop := finite_count (2^1024) (2^128) (by decide +kernel) (successes (2^128)) (by
    intro v hv
    obtain ⟨el,menu⟩ := mem_filter.mp hv
    obtain ⟨lt,hi⟩ := PrimeFactors.MonotoneSumPopulation.data el
    exact ⟨lt,hi.le,menu⟩)
  have sqrtpow (j : ℕ) : Real.sqrt (((2^(j+j):ℕ):ℝ))=(2:ℝ)^j := by
    rw [pow_add,Nat.cast_mul,←sq,Real.sqrt_sq (Nat.cast_nonneg _),Nat.cast_pow,Nat.cast_ofNat]
  have h := sqrtpow 512
  have b := sqrtpow 64
  change Real.sqrt (((2^1024:ℕ):ℝ))=(2:ℝ)^512 at h
  change Real.sqrt (((2^128:ℕ):ℝ))=(2:ℝ)^64 at b
  rw [h,b] at pop
  push_cast at pop
  have hn : (successes (2^128)).card ≤ 36*(2:ℕ)^1024*2^512*2^64+2*2^1024 := by exact_mod_cast pop
  have room : 21000000*(2^416*(36*(2:ℕ)^1024*2^512*2^64+2*2^1024))≤2^2046 := by decide +kernel
  exact Nat.lt_of_mul_lt_mul_left ((Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left _ hn)).trans_lt
    (room.trans_lt ChebyshevPrimeSample.eligible_count))

private theorem toy_values {p q r a b g : ℕ} (root : (p*q).sqrt=r)
    (n : 0<a ∧ 0<b ∧ 0<g ∧ p*q-r^2=a*g ∧ p+q-2*r=b*g)
    (den : (p+q-2*r)/(p*q-r^2).gcd (p+q-2*r)=b) :
    Witness p q a b g ∧ denominator p q=b := by
  simpa only [Witness,denominator,FloorSquareShift.residual,excess,root] using And.intro n den

/-- A scaled-floor control, followed by two distinct products sharing D and b. -/
theorem toy :
    23*31=713 ∧ Nat.Prime 23 ∧ Nat.Prime 31 ∧ (713:ℕ).sqrt=26 ∧
    Witness 23 31 37 2 1 ∧ denominator 23 31=2 ∧
    (4*713:ℕ).sqrt=53 ∧ 2*26≠53 ∧
    Nat.Prime 67 ∧ Nat.Prime 127 ∧ 67*127=8509 ∧ Nat.Prime 83 ∧ Nat.Prime 107 ∧ 83*107=8881 ∧
    Witness 67 127 9 2 5 ∧ Witness 83 107 45 2 1 ∧
    denominator 67 127=2 ∧ denominator 83 107=2 := by
  have root {p q r : ℕ} (lc : r^2≤p*q) (uc : p*q<(r+1)^2) : (p*q).sqrt=r :=
    (Nat.eq_sqrt'.mpr ⟨lc,uc⟩).symm
  have h := toy_values (p:=23) (q:=31) (r:=26) (a:=37) (b:=2) (g:=1)
    (root (by decide) (by decide)) (by decide) (by decide)
  have g := toy_values (p:=67) (q:=127) (r:=92) (a:=9) (b:=2) (g:=5)
    (root (by decide) (by decide)) (by decide) (by decide)
  have f := toy_values (p:=83) (q:=107) (r:=94) (a:=45) (b:=2) (g:=1)
    (root (by decide) (by decide)) (by decide) (by decide)
  exact ⟨by decide,by decide,by decide,(Nat.eq_sqrt'.mpr (by decide)).symm,h.1,h.2,
    (Nat.eq_sqrt'.mpr (by decide)).symm,by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,g.1,f.1,g.2,f.2⟩

end PrimeFactors.RationalFloorShift
