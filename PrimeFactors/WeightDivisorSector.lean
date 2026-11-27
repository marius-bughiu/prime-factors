import PrimeFactors.RectangularSearchFloor

/-! A certified divisor-free interval removes all oriented weight
assignments in a closed cone, using only its two endpoints. -/
namespace PrimeFactors.WeightDivisorSector

/-- Conditions at the two divisor endpoints suffice. J bounds the
absolute difference of the two weighted factors. -/
def Sector (N J L U A B : ℕ) : Prop :=
  (A*L+J)*L ≤ B*N ∧ B*N+J*U ≤ A*U^2

theorem contains {N J L U A B p q : ℕ} (factor : p*q=N) (ap : 0<A) (bp : 0<B)
    (qp : 0<q) (lp : 0<L)
    (cell : Sector N J L U A B) (one : A*p≤B*q+J) (two : B*q≤A*p+J) :
    L≤p ∧ p≤U := by
  obtain ⟨lo,hi⟩ := cell
  constructor
  · by_contra! outside
    have leq := Nat.mul_le_mul_right p two
    have rising : (A*p+J)*p < (A*L+J)*L :=
      (Nat.mul_le_mul_right p (Nat.add_le_add_right (Nat.mul_le_mul_left A outside.le) J)).trans_lt
        (Nat.mul_lt_mul_of_pos_left outside (by positivity))
    have eq : B*q*p=B*N := by rw [←factor]; ring
    omega
  · by_contra! outside
    have step := Nat.mul_lt_mul_of_pos_right outside (Nat.mul_pos bp qp)
    have atU : (B*q+J)*U < A*U^2 := by
      have eq : p*(B*q)=B*N := by rw [←factor]; ring
      nlinarith only [step,eq,hi]
    have small : B*q+J < A*U := Nat.lt_of_mul_lt_mul_right (by
      simpa only [Nat.pow_two,Nat.mul_assoc] using atU)
    have := Nat.mul_le_mul_left A outside.le
    omega

/-- A constant-width sector is preserved by adding any nonnegative
multiple of a direction which is already inside the zero-width cone. -/
theorem affine {N J L U A B V W : ℕ} (base : Sector N J L U A B)
    (direction : Sector N 0 L U V W) (s : ℕ) : Sector N J L U (A+s*V) (B+s*W) := by
  obtain ⟨bl,bu⟩ := base
  obtain ⟨dl,du⟩ := direction
  constructor
  · nlinarith only [bl,Nat.mul_le_mul_left s dl]
  · nlinarith only [bu,Nat.mul_le_mul_left s du]

/-- An actual assignment may exchange the signs y−x and y+x. Both
orientations require the same bound on the difference of the two
weighted factors. -/
theorem reject {N H L U A B p q t x y : ℕ} (factor : p*q=N) (ap : 0<A) (bp : 0<B)
    (qp : 0<q) (lp : 0<L)
    (empty : ∀ d, L≤d → d≤U → ¬ d∣N) (cell : Sector N (2*H) L U A B)
    (tp : 0<t) (xy : x≤y) (short : x≤H) :
    ¬ MixedUnityCofactors.Located t p q A B x y := by
  intro located
  have minus : y-x+x=y := Nat.sub_add_cancel xy
  have both : t*(A*p)≤t*(B*q)+2*x ∧ t*(B*q)≤t*(A*p)+2*x := by
    rw [Nat.mul_comm A p,Nat.mul_comm B q]
    rcases located with ⟨l,r⟩|⟨l,r⟩ <;> rw [l,r] <;> omega
  have ge : 2*x≤t*(2*H) := (by omega : 2*x≤2*H).trans
    (Nat.le_mul_of_pos_left _ tp)
  have unlock {c d : ℕ} (h : t*c≤t*d+2*x) : c≤d+2*H := by
    apply Nat.le_of_mul_le_mul_left _ tp
    rw [Nat.mul_add]
    omega
  have win := contains factor ap bp qp lp cell (unlock both.1) (unlock both.2)
  exact empty p win.1 win.2 (factor ▸ dvd_mul_right ..)

/-- A direction primitive relative to the starting point keeps every
pair primitive along the progression. -/
theorem coprime_progression {A B V W : ℕ} (det : V*B=W*A+1) (s : ℕ) :
    (A+s*V).Coprime (B+s*W) := by
  refine Nat.coprime_of_dvd fun l prime dvA dvB => ?_
  have lA := Nat.dvd_mul_left_of_dvd dvA W
  have lB := Nat.dvd_mul_left_of_dvd dvB V
  have same : V*(B+s*W)-W*(A+s*V)=1 := by
    have eq : V*(B+s*W)=W*(A+s*V)+1 := by nlinarith only [det]
    omega
  have d1 := Nat.dvd_sub lB lA
  rw [same,Nat.dvd_one] at d1
  exact prime.ne_one d1

structure Family where
  N : ℕ
  H : ℕ
  L : ℕ
  U : ℕ
  K : ℕ
  e : ℕ
  A : ℕ
  B : ℕ
  V : ℕ
  W : ℕ
  count : ℕ

def major (f : Family) (i : ℕ) := f.A+2*i*f.V
def minor (f : Family) (i : ℕ) := f.B+2*i*f.W
def product (f : Family) (i : ℕ) := major f i * minor f i

structure Valid (f : Family) : Prop where
  lp : 0<f.L
  bp : 0<f.B
  wp : 0<f.W
  order : f.B≤f.A
  slopeOrder : f.W≤f.V
  oddBig : f.A%2=1
  oddSmall : f.B%2=1
  determinant : f.V*f.B=f.W*f.A+1
  cap : (major f (f.count-1))^2≤f.K
  ratio : 1024*f.A≤(1024+f.e)*f.B
  slopeRatio : 1024*f.V≤(1024+f.e)*f.W
  center : Sector f.N (2*f.H) f.L f.U f.A f.B
  direction : Sector f.N 0 f.L f.U f.V f.W

/-- Verify rectangle and ratio values with ordinary integer comparisons,
without evaluating the noncomputable ceiling cube root. -/
theorem parameters {N T S Y H' K' e : ℕ}
    (tl : (T-1)^3<N) (tu : N≤T^3) (sl : S^2≤N) (su : N<(S+1)^2)
    (yb : max (N/T) (S+1)=Y) (hb : N/(Y+1)=H') (kb : Y^2/N=K')
    (eb : (1024*RectangularFullWidth.upperPrime^2*(S+H')+N*(S-H')-1)/(N*(S-H'))-1024=e) :
    H'=RectangularFullWidth.H N ∧ K'=RectangularFullWidth.K N ∧
      e=RectangularFullWidth.excess N := by
  have t := CubicForcedParameters.ceilCube_eq tl tu
  have s : N.sqrt=S := le_antisymm (Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr su)) (Nat.le_sqrt'.mpr sl)
  have y : RectangularFullWidth.B N=Y := by rw [RectangularFullWidth.B,t,s,yb]
  have h : RectangularFullWidth.H N=H' := by rw [RectangularFullWidth.H,y,hb]
  exact ⟨h.symm,by rw [RectangularFullWidth.K,y,kb],by
    rw [RectangularFullWidth.excess,RectangularFullWidth.numerator,RectangularFullWidth.denominator,h,s,eb]⟩

private theorem increasing {f : Family} (c : Valid f) : StrictMono (product f) := by
  intro i j h
  have positive : 0<2*f.V := by have := c.wp; have := c.slopeOrder; omega
  have step := Nat.mul_lt_mul_of_pos_right h positive
  have big : major f i<major f j := by dsimp [major]; nlinarith only [step]
  have step' := Nat.mul_le_mul_right (2*f.W) h.le
  have small : minor f i≤minor f j := by dsimp [minor]; nlinarith only [step']
  have pos : 0<minor f i := by dsimp [minor]; have := c.bp; omega
  exact (Nat.mul_lt_mul_of_pos_right big pos).trans_le (Nat.mul_le_mul_left _ small)

/-- Every member passes the exact odd scanner, including the gcd and
ratio. This uses only the final cap and two linear ratio bounds. -/
theorem eligible {f : Family} (c : Valid f) (i : Fin f.count) :
    product f i ∈ RectangularSearchFloor.emitted f.K 1024 f.e := by
  let A := major f i
  let B := minor f i
  have ci : (i:ℕ)≤f.count-1 := by have := i.isLt; omega
  have mp : 0<B := by dsimp [B,minor]; have := c.bp; omega
  have ord : B≤A := add_le_add c.order (Nat.mul_le_mul_left _ c.slopeOrder)
  have ia : A≤major f (f.count-1) :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 ci)) _
  have cap : A^2≤f.K := (Nat.pow_le_pow_left ia 2).trans c.cap
  have sqrt : B≤f.K.sqrt := ord.trans (Nat.le_sqrt.mpr (by simpa [pow_two] using cap))
  have co : B.Coprime A := (coprime_progression c.determinant (2*i)).symm
  have oa : A%2=1 := by
    change (f.A+2*(i:ℕ)*f.V)%2=1
    rw [mul_assoc,Nat.add_mod]; simp [c.oddBig]
  have ob : B%2=1 := by
    change (f.B+2*(i:ℕ)*f.W)%2=1
    rw [mul_assoc,Nat.add_mod]; simp [c.oddSmall]
  have fit : A≤f.K/B := (Nat.le_div_iff_mul_le mp).mpr
    ((Nat.mul_le_mul_left A ord).trans (by simpa [pow_two] using cap))
  have rate : 1024*A≤(1024+f.e)*B := by
    dsimp [A,B,major,minor]
    nlinarith only [c.ratio,Nat.mul_le_mul_left (2*(i:ℕ)) c.slopeRatio]
  apply Finset.mem_union_left
  refine Finset.mem_biUnion.mpr ⟨B,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨mp,sqrt⟩,ob⟩,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨A,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ord,le_min (by simpa using fit) ?_⟩,
    (show (A-B)%2=0 ∧ B.Coprime A from ⟨by omega,co⟩)⟩,?_⟩
  · exact (Nat.le_div_iff_mul_le (by decide)).mpr (by simpa only [Nat.mul_comm A 1024] using rate)
  · change 1*B*A=A*B
    simp [mul_comm]

/-- One divisor-interval certificate rules out every assignment in the
family. Its candidate multipliers are pairwise distinct. Quantification
over each factorization of N also covers exchanging the prime labels. -/
theorem collective {f : Family} (c : Valid f)
    (empty : ∀ d, f.L≤d → d≤f.U → ¬ d∣f.N) :
    Function.Injective (fun i : Fin f.count => product f i) ∧
    ∀ i : Fin f.count, product f i ∈ RectangularSearchFloor.emitted f.K 1024 f.e ∧
      ∀ p q t x y : ℕ, p*q=f.N → 0<q → 0<t → x≤y → x≤f.H →
      ¬ MixedUnityCofactors.Located t p q (major f i) (minor f i) x y := by
  refine ⟨fun _ _ h => Fin.ext ((increasing c).injective h),?_⟩
  intro i
  refine ⟨eligible c i,?_⟩
  intro p q t x y eq qp tp xy sh
  have ap : 0<f.A := c.bp.trans_le c.order
  have a : 0<major f i := by dsimp [major]; omega
  have b : 0<minor f i := by dsimp [minor]; have := c.bp; omega
  exact reject eq a b qp c.lp empty (affine c.center c.direction (2*i)) tp xy sh

set_option maxRecDepth 4096 in
/-- k=2145 has two eligible factorizations. The weights 65 and 33
confine the attached divisor to an empty interval. Nevertheless the
weights 55 and 39 give an actual splitting point at the same k. -/
theorem shared_row :
    Sector 34361588549 (2*3251) 131976 132183 65 33 ∧
    (∀ i : Fin 208, ¬ (131976+(i:ℕ))∣34361588549) ∧
    65*33=2145 ∧ 55*39=2145 ∧ 8585197^2=302^2+2145*34361588549 ∧
    MixedUnityCofactors.Located 1 156089 220141 55 39 302 8585197 ∧
    (8585197-302).gcd 34361588549=156089 ∧ 34361588549=156089*220141 ∧
    Nat.Prime 156089 ∧ Nat.Prime 220141 := by
  have p : Nat.Prime 156089 := by norm_num
  have q : Nat.Prime 220141 := by norm_num
  refine ⟨?_,?_,by decide,by decide,by decide,?_,by decide +kernel,by decide,p,q⟩
  · unfold Sector
    decide +kernel
  · intro i dv
    obtain ⟨r,rp,rd⟩ := Nat.exists_prime_and_dvd (show 131976+(i:ℕ)≠1 by omega)
    have rle := Nat.le_of_dvd (show 0<131976+(i:ℕ) by omega) rd
    have pair : r∣156089*220141 := rd.trans dv
    rcases rp.dvd_mul.mp pair with rl|rr
    · have eq := (Nat.prime_dvd_prime_iff_eq rp p).mp rl
      omega
    · have eq := (Nat.prime_dvd_prime_iff_eq rp q).mp rr
      omega
  · unfold MixedUnityCofactors.Located
    decide +kernel

end PrimeFactors.WeightDivisorSector
