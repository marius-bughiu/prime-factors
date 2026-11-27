import PrimeFactors.MultiplierDivisorReach
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! Coverage of arbitrary translated weighted trace bands, allowing all
multiplier allocations. The midpoint of a band need not be close to the
minimum weighted sum. -/
namespace PrimeFactors.DisplacedTraceCoverage
open Finset Real

noncomputable def value (n a b x : ℝ) := a*x+b*n/x

/-- At fixed product t⁴, the candidate's weighted trace lies in an arbitrary
closed interval of width w. The true smaller factor is at most t². -/
def InBand (t w h a b x : ℝ) : Prop :=
  0<x ∧ x≤t^2 ∧ h≤value (t^4) a b x ∧ value (t^4) a b x≤h+w

private theorem between_weights {a b r : ℝ} (ap : 0≤a) (bp : 0≤b) (ab : a*b=r^4) :
    r^2≤max a b := by
  apply le_of_sq_le_sq _ (ap.trans (le_max_left _ _))
  rw [←pow_mul,show 2*2=4 by decide,←ab,pow_two]
  exact mul_le_mul (le_max_left _ _) (le_max_right _ _) bp (ap.trans (le_max_left _ _))

/-- Two candidate locations on either one of the two monotone branches
cannot be far apart, independently of the trace band's starting height. -/
theorem branch_diameter {t r w h a b x y : ℝ} (tp : 0<t) (ap : 0<a) (bp : 0<b)
    (ab : a*b=r^4) (xy : x≤y) (hx : InBand t w h a b x) (hy : InBand t w h a b y)
    (branch : b*t^4≤a*x^2 ∨ a*y^2≤b*t^4) : r^2*(y-x)^2 ≤ w*t^2 := by
  obtain ⟨xp,xt,xlo,xhi⟩ := hx
  obtain ⟨yp,yt,ylo,yhi⟩ := hy
  have w0 : 0≤w := by linarith only [xlo,xhi]
  have dy := sub_nonneg.mpr xy
  have t4 : 0<t^4 := by positivity
  have ymax : y^2≤t^4 := by simpa only [←pow_mul] using pow_le_pow_left₀ yp.le yt 2
  have xmax : x^2≤t^4 := by simpa only [←pow_mul] using pow_le_pow_left₀ xp.le xt 2
  have weight := between_weights ap.le bp.le ab
  have identity : (value (t^4) a b y-value (t^4) a b x)*(x*y) = (y-x)*(a*x*y-b*t^4) := by
    dsimp only [value]; field_simp; ring
  rcases branch with right|left
  · have ba : b≤a := le_of_mul_le_mul_right (right.trans (mul_le_mul_of_nonneg_left xmax ap.le)) t4
    rw [max_eq_left ba] at weight
    have k : a*x*(y-x)≤a*x*y-b*t^4 := by linarith only [right]
    have product := mul_le_mul_of_nonneg_left k dy
    rw [←identity] at product
    have cmp : a*(y-x)^2 ≤ (value (t^4) a b y-value (t^4) a b x)*y := by
      apply le_of_mul_le_mul_right (a:=x) _ xp
      linarith only [product]
    exact (mul_le_mul_of_nonneg_right weight (sq_nonneg _)).trans
      (cmp.trans (mul_le_mul (by linarith only [yhi,xlo]) yt yp.le w0))
  · have stiff : r^2*y^2 ≤ b*t^4 := by
      rcases le_total a b with h|h
      · rw [max_eq_right h] at weight
        exact mul_le_mul weight ymax (sq_nonneg _) bp.le
      · rw [max_eq_left h] at weight
        exact (mul_le_mul_of_nonneg_right weight (sq_nonneg _)).trans left
    have inner : b*t^4*(y-x) ≤ b*t^4*y-a*x*y^2 := by
      linarith only [mul_le_mul_of_nonneg_left left xp.le]
    have product := mul_le_mul_of_nonneg_left inner dy
    have id' : (value (t^4) a b x-value (t^4) a b y)*x*y^2 = (y-x)*(b*t^4*y-a*x*y^2) := by
      linear_combination -y*identity
    rw [←id'] at product
    have mult := mul_le_mul_of_nonneg_right stiff (sq_nonneg (y-x))
    have cmp : r^2*(y-x)^2 ≤ (value (t^4) a b x-value (t^4) a b y)*x := by
      apply le_of_mul_le_mul_right (a:=y^2) _ (by positivity)
      linarith only [product,mult]
    exact cmp.trans (mul_le_mul (by linarith only [xhi,ylo]) xt xp.le w0)

private theorem count_piece {t r s a b h : ℝ} (tp : 0<t) (rp : 0<r) (sp : 0≤s)
    (ap : 0<a) (bp : 0<b) (ab : a*b=r^4) (xs : Finset ℕ)
    (mem : ∀ x∈xs, InBand t (s^2) h a b x)
    (branch : ∀ x∈xs, ∀ y∈xs, x≤y → b*t^4≤a*(x:ℝ)^2 ∨ a*(y:ℝ)^2≤b*t^4) :
    r*xs.card≤r+s*t := by
  by_cases ne : xs.Nonempty
  · let x := xs.min' ne
    let y := xs.max' ne
    have hx := xs.min'_mem ne
    have hy := xs.max'_mem ne
    have xy : x≤y := xs.min'_le _ hy
    have sq := branch_diameter tp ap bp ab (by exact_mod_cast xy) (mem x hx) (mem y hy) (branch x hx y hy xy)
    have dist : r*((y:ℝ)-x)≤s*t := by
      apply le_of_sq_le_sq _ (mul_nonneg sp tp.le)
      simpa only [mul_pow] using sq
    have within : xs ⊆ Icc x y := fun z hz => mem_Icc.mpr ⟨xs.min'_le z hz,xs.le_max' z hz⟩
    have size := card_le_card within
    rw [Nat.card_Icc] at size
    have num : (xs.card:ℝ)+x ≤ y+1 := by exact_mod_cast (show xs.card+x≤y+1 by omega)
    linarith only [mul_le_mul_of_nonneg_left num rp.le,dist]
  · rw [not_nonempty_iff_eq_empty.mp ne,card_empty,Nat.cast_zero,mul_zero]; positivity

private theorem count_band {t r s a b h : ℝ} (tp : 0<t) (rp : 0<r) (sp : 0≤s)
    (ap : 0<a) (bp : 0<b) (ab : a*b=r^4) (xs : Finset ℕ) (mem : ∀ x∈xs, InBand t (s^2) h a b x) :
    r*xs.card≤2*(r+s*t) := by
  classical
  let low (x:ℕ) := a*(x:ℝ)^2≤b*t^4
  let L := xs.filter low
  let R := xs.filter (fun x => ¬low x)
  have hl := count_piece tp rp sp ap bp ab L (fun _ hx => mem _ (mem_filter.mp hx).1)
    (fun _ _ y hy _ => Or.inr ((mem_filter.mp hy).2 : low y))
  have hr := count_piece tp rp sp ap bp ab R (fun _ hx => mem _ (mem_filter.mp hx).1)
    (fun x hx _ _ _ => Or.inl (le_of_not_ge ((mem_filter.mp hx).2 : ¬low x)))
  have partition : L.card+R.card=xs.card := filter_card_add_filter_neg_card_eq_card _
  have sz : (L.card:ℝ)+R.card=xs.card := by exact_mod_cast partition
  linarith only [hl,hr,congrArg (fun v : ℝ => r*v) sz]

noncomputable def root (n : ℕ) : ℝ := √(√(n:ℝ))

private theorem root_pow (n : ℕ) : root n^4=(n:ℝ) := by
  rw [show root n^4=(root n^2)^2 by ring,show root n^2=√(n:ℝ) from sq_sqrt (sqrt_nonneg _),
    sq_sqrt (Nat.cast_nonneg n)]

/-- A candidate location in at least one factor allocation of multiplier k. -/
def Reaches (n k : ℕ) (h w : ℝ) (x : ℕ) : Prop :=
  ∃ a∈k.divisors, InBand (root n) w h a (k/a:ℕ) x

/-- For one band of arbitrary starting height the fourth root of the
multiplier cancels against the divisor count. The additive term records
rounding at both real branches of each allocation. -/
theorem one_band {n k : ℕ} (np : 0<n) (kp : 0<k) (h s : ℝ) (sp : 0≤s)
    (xs : Finset ℕ) (mem : ∀ x∈xs, Reaches n k h (s^2) x) :
    (xs.card:ℝ) ≤ 2*(k.divisors.card:ℝ) + 18*s*root n := by
  classical
  let t := root n
  let r := root k
  have tp : 0<t := by dsimp [t,root]; positivity
  have rp : 0<r := by dsimp [r,root]; positivity
  let A (a:ℕ) := xs.filter (fun (x:ℕ) => InBand t (s^2) h a (k/a:ℕ) x)
  have cover : xs ⊆ k.divisors.biUnion A := by
    intro x hx
    obtain ⟨a,ha,ok⟩ := mem x hx
    exact mem_biUnion.mpr ⟨a,ha,mem_filter.mpr ⟨hx,ok⟩⟩
  have per (a : ℕ) (ha : a∈k.divisors) : r*(A a).card≤2*(r+s*t) := by
    have aa := Nat.pos_of_mem_divisors ha
    have ab : a*(k/a)=k := Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1
    have bb : 0<k/a := Nat.div_pos (Nat.le_of_dvd kp (Nat.mem_divisors.mp ha).1) aa
    have eq : (a:ℝ)*(k/a:ℕ)=r^4 := by rw [root_pow]; exact_mod_cast ab
    exact count_band tp rp sp (by exact_mod_cast aa) (by exact_mod_cast bb) eq _ (fun _ hx => (mem_filter.mp hx).2)
  have total : r*(xs.card:ℝ) ≤ (k.divisors.card:ℝ)*(2*(r+s*t)) := calc
    _ ≤ r*(∑ a∈k.divisors, ((A a).card:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ rp.le
      exact_mod_cast (card_le_card cover).trans (card_biUnion_le : (k.divisors.biUnion A).card≤_)
    _ = ∑ a∈k.divisors, r*(A a).card := by rw [mul_sum]
    _ ≤ ∑ _a∈k.divisors, 2*(r+s*t) := sum_le_sum per
    _ = _ := by simp
  have raw := MultiplierDivisorReach.fourth_power_bound kp.ne'
  have cast : (k.divisors.card:ℝ)^4 < 9^4*(k:ℝ) := by exact_mod_cast raw
  have cnt : (k.divisors.card:ℝ) ≤ 9*r := by
    apply le_of_not_gt
    intro high
    have bad := pow_le_pow_left₀ (by positivity : 0≤9*r) high.le 4
    rw [mul_pow,root_pow] at bad
    linarith only [bad,cast]
  apply le_of_mul_le_mul_left (a:=r) _ rp
  linarith only [total,mul_le_mul_of_nonneg_right cnt (mul_nonneg sp tp.le)]

/-- A transcript is any finite collection of bands, including a list built
adaptively from N and earlier tests. All orientations and all placements are
allowed; only the multiplier upper bound and each band's raw width enter. -/
theorem transcript {ι : Type*} {n : ℕ} (np : 0<n) (rows : Finset ι) (k : ι→ℕ)
    (h s : ι→ℝ) (cost : ∀ i∈rows, 0<k i ∧ k i≤n ∧ 0≤s i) (xs : Finset ℕ)
    (mem : ∀ x∈xs, ∃ i∈rows, Reaches n (k i) (h i) ((s i)^2) x) :
    (xs.card:ℝ) ≤ 18*root n * ∑ i∈rows, (1+s i) := by
  classical
  let A (i:ι) := xs.filter (Reaches n (k i) (h i) ((s i)^2))
  have cover : xs ⊆ rows.biUnion A := by
    intro x hx
    obtain ⟨i,hi,ok⟩ := mem x hx
    exact mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨hx,ok⟩⟩
  have sum : (xs.card:ℝ) ≤ ∑ i∈rows, ((A i).card:ℝ) := by
    exact_mod_cast (card_le_card cover).trans (card_biUnion_le : (rows.biUnion A).card≤_)
  rw [mul_sum]
  apply sum.trans (sum_le_sum ?_)
  intro i hi
  obtain ⟨kp,kn,sp⟩ := cost i hi
  have bound := one_band np kp (h i) (s i) sp (A i) (fun _ hx => (mem_filter.mp hx).2)
  have raw := MultiplierDivisorReach.fourth_power_bound kp.ne'
  have cast : ((k i).divisors.card:ℝ)^4 < 9^4*(n:ℝ) := by
    exact_mod_cast (raw.trans_le (Nat.mul_le_mul_left _ kn))
  have cnt : ((k i).divisors.card:ℝ) ≤ 9*root n := by
    apply le_of_not_gt
    intro high
    have bad := pow_le_pow_left₀ (by dsimp [root]; positivity : 0≤9*root n) high.le 4
    rw [mul_pow,root_pow] at bad
    linarith only [bad,cast]
  linarith only [bound,cnt]

set_option exponentiation.threshold 8192

/-- Every sparse mod-24 label has at most 24 units of raw trace on either
side before the next admitted label. Grant a band of width 49 per test. -/
theorem isolated_labels {ι : Type*} {n : ℕ} (np : 0<n) (top : n≤2^2048)
    (rows : Finset ι) (k : ι→ℕ) (h : ι→ℝ) (weights : ∀ i∈rows, 0<k i ∧ k i≤n)
    (xs : Finset ℕ) (mem : ∀ x∈xs, ∃ i∈rows, Reaches n (k i) (h i) 49 x) :
    xs.card ≤ 144*2^512*rows.card := by
  have t : root n ≤ (2:ℝ)^512 := by
    apply le_of_not_gt
    intro high
    have bad := pow_lt_pow_left₀ high (by positivity : (0:ℝ)≤2^512) (by decide : (4:ℕ)≠0)
    rw [root_pow,←pow_mul] at bad
    exact (not_lt_of_ge (by exact_mod_cast top)) bad
  have cost (i : ι) (hi : i∈rows) : 0<k i ∧ k i≤n ∧ (0:ℝ)≤7 := ⟨(weights i hi).1,(weights i hi).2,by norm_num⟩
  have bound := transcript np rows k h (fun _ => 7) cost xs (by simpa only [show (7:ℝ)^2=49 by norm_num] using mem)
  simp only [sum_const,nsmul_eq_mul] at bound
  have rem := mul_le_mul_of_nonneg_right t (Nat.cast_nonneg (α:=ℝ) rows.card)
  exact_mod_cast (show (xs.card:ℝ) ≤ 144*2^512*rows.card by linarith only [bound,rem])

/-- The gap on either side of an admissible label is at most one period,
even if the set of permitted residues differs between orientations. -/
def Bracket24 (P : ℤ→Prop) (z l u : ℤ) : Prop :=
  P z ∧ (∀ v, P v ↔ P (v+24)) ∧
    (∀ j, l<j → j<z → ¬P j) ∧ (∀ j, z<j → j<u → ¬P j)

private theorem end_bounds {P : ℤ→Prop} {z l u : ℤ} (ok : Bracket24 P z l u) :
    z-24≤l ∧ u≤z+24 := by
  obtain ⟨hit,period,left,right⟩ := ok
  have prev : P (z-24) := (period _).mpr (by simpa only [sub_add_cancel] using hit)
  exact ⟨le_of_not_gt (fun bad => left _ bad (by omega) prev),
    le_of_not_gt (fun bad => right _ (by omega) bad ((period _).mp hit))⟩

/-- The integer location is in some allocation's continuous exclusion
range between the preceding and following allowed labels of a mod-24 wheel. -/
def Covered24 (n k : ℕ) (z : ℤ) (x : ℕ) : Prop :=
  0<x ∧ x^2≤n ∧ ∃ a∈k.divisors, ∃ (P : ℤ→Prop) (l u : ℤ),
    Bracket24 P z l u ∧ (l:ℝ)≤value n a (k/a:ℕ) x ∧ value n a (k/a:ℕ) x≤u

private theorem to_band {n k x : ℕ} {z : ℤ} (covered : Covered24 n k z x) : Reaches n k ((z:ℝ)-24) 49 x := by
  obtain ⟨xp,x2,a,ha,P,l,u,between,left,right⟩ := covered
  obtain ⟨vlo,vhi⟩ := end_bounds between
  have low : (z:ℝ)-24≤l := by exact_mod_cast vlo
  have high : (u:ℝ)≤z+24 := by exact_mod_cast vhi
  have X : (x:ℝ)≤√(n:ℝ) := (Real.le_sqrt (Nat.cast_nonneg x) (Nat.cast_nonneg n)).mpr (by exact_mod_cast x2)
  refine ⟨a,ha,by exact_mod_cast xp,?_,?_,?_⟩
  · simpa only [root,sq_sqrt (sqrt_nonneg (n:ℝ))] using X
  · rw [root_pow]; exact low.trans left
  · rw [root_pow]; linarith only [right,high]

/-- The balanced bit-width constraints on a candidate for the smaller prime.
These include the upper limit on its partner. -/
def Feasible (n x : ℕ) : Prop := 2^1023≤x ∧ x^2≤n ∧ n≤x*(2^1024-1)

noncomputable def core : Finset ℕ := Icc (5*2^1021+1) (6*2^1021)

private theorem core_size : core.card=2^1021 := by rw [core,Nat.card_Icc]; norm_num

private theorem core_feasible {n x : ℕ} (lo : 9*(2^1024)^2≤16*n) (hi : 8*n≤5*(2^1024)^2)
    (hx : x∈core) : Feasible n x := by
  obtain ⟨xl,xh⟩ := mem_Icc.mp hx
  have high : (6*2^1021)^2 ≤ n := by norm_num at lo ⊢; omega
  have low : n ≤ (5*2^1021+1)*(2^1024-1) := by norm_num at hi ⊢; omega
  exact ⟨le_trans (by norm_num) xl,(Nat.pow_le_pow_left xh 2).trans high,
    low.trans (Nat.mul_le_mul_right _ xl)⟩

/-- The cardinal estimate applies to any prefiltered set of potential
smaller factors, with arbitrary prior constraints on that set. -/
theorem pool_survives {ι : Type*} {n : ℕ} (np : 0<n) (top : n≤2^2048)
    (rows : Finset ι) (k : ι→ℕ) (z : ι→ℤ) (weight : ∀ i∈rows, 0<k i ∧ k i≤n) (pool : Finset ℕ) :
    ∃ left : Finset ℕ, pool.card-144*2^512*rows.card≤left.card ∧
      ∀ x∈left, x∈pool ∧ ∀ i∈rows, ¬Covered24 n (k i) (z i) x := by
  classical
  let hit := pool.filter (fun x => ∃ i∈rows, Covered24 n (k i) (z i) x)
  have bound := isolated_labels np top rows k (fun i => (z i:ℝ)-24) weight hit (by
    intro x hx
    obtain ⟨i,ok,reaches⟩ := (mem_filter.mp hx).2
    exact ⟨i,ok,to_band reaches⟩)
  refine ⟨pool \ hit,(Nat.sub_le_sub_left bound _).trans (le_card_sdiff hit pool),?_⟩
  intro x hx
  obtain ⟨xc,miss⟩ := mem_sdiff.mp hx
  exact ⟨xc, fun i hi covered => miss (mem_filter.mpr ⟨xc,i,hi,covered⟩)⟩

/-- For the public slice, count the feasible locations still outside an
arbitrary collection of translated mod-24 brackets. The estimate does not
require the tests or multipliers to have been fixed before seeing n. -/
theorem survivor_count {ι : Type*} {n : ℕ} (lo : 9*(2^1024)^2≤16*n) (hi : 8*n≤5*(2^1024)^2)
    (rows : Finset ι) (k : ι→ℕ) (z : ι→ℤ) (weight : ∀ i∈rows, 0<k i ∧ k i≤n) :
    ∃ left : Finset ℕ, 2^1021-144*2^512*rows.card≤left.card ∧
      ∀ x∈left, Feasible n x ∧ ∀ i∈rows, ¬Covered24 n (k i) (z i) x := by
  have np : 0<n := by norm_num at lo; omega
  have top : n≤2^2048 := by norm_num at hi ⊢; omega
  obtain ⟨left,count,eligible⟩ := pool_survives np top rows k z weight core
  refine ⟨left,by simpa only [core_size] using count,?_⟩
  intro x hx
  obtain ⟨hc,miss⟩ := eligible x hx
  exact ⟨core_feasible lo hi hc,miss⟩

/-- Over any commutative ring, every invertible candidate x has one partner
that simultaneously agrees with the public product and avoids *every*
weighted label certified nonsquare. In particular this applies to all unit
classes modulo a common modulus, regardless of how many labels were tested. -/
theorem simultaneous_local_survival {R ι : Type*} [CommRing R] (n : R) (a b z : ι→R)
    (bad : ∀ i, ¬IsSquare (z i^2-4*a i*b i*n)) (x : Rˣ) :
    ∃ y : R, (x:R)*y=n ∧ ∀ i, a i*x+b i*y≠z i ∧
      (a i*x+b i*y)^2-4*a i*b i*n=(a i*x-b i*y)^2 := by
  let y : R := (↑(x⁻¹):R)*n
  have xy : (x:R)*y=n := by dsimp [y]; rw [←mul_assoc,Units.mul_inv,one_mul]
  refine ⟨y,xy,?_⟩
  intro i
  have eq : (a i*x+b i*y)^2-4*a i*b i*n=(a i*x-b i*y)^2 := by rw [←xy]; ring
  refine ⟨?_,eq⟩
  intro contrary
  apply bad i
  exact ⟨a i*x-b i*y,by simpa only [←contrary,pow_two] using eq⟩

/-- The natural scale of the uniform diameter estimate is attained even
with a unit-width band and ordinary (unweighted) sums. -/
theorem tangent_reach {t x : ℝ} (big : 2≤t) (lo : t^2-t/2≤x) (hi : x≤t^2) :
    InBand t 1 (2*t^2) 1 1 x := by
  have tpos : 0<t := by linarith only [big]
  have half : t^2/2≤x := by nlinarith only [big,lo,mul_nonneg (sub_nonneg.mpr big) tpos.le]
  have xp : 0<x := lt_of_lt_of_le (by positivity) half
  have gap : (t^2-x)^2≤(t/2)^2 := pow_le_pow_left₀ (sub_nonneg.mpr hi) (by linarith only [lo]) 2
  have eq : (value (t^4) 1 1 x-2*t^2)*x=(t^2-x)^2 := by dsimp only [value]; field_simp; ring
  refine ⟨xp,hi,?_,?_⟩
  · have positive : 0≤(value (t^4) 1 1 x-2*t^2)*x := eq ▸ sq_nonneg _
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_left positive xp)
  · have cap : (value (t^4) 1 1 x-2*t^2)*x≤1*x := by nlinarith only [eq,gap,half,sq_nonneg t]
    linarith only [le_of_mul_le_mul_right cap xp]

noncomputable def primesTo (n : ℕ) : Finset ℕ := (Icc 0 n).filter Nat.Prime

/-- Dusart (2010), equation (6.6), supplies the two finite endpoint
estimates. The deduction to the number of untouched prime locations uses
only those estimates and the placement-independent geometry. -/
theorem prime_survivors {ι : Type*} {n : ℕ} (lo : 9*(2^1024)^2≤16*n) (hi : 8*n≤5*(2^1024)^2)
    (lowCount : 6*2^1021≤710*(primesTo (6*2^1021)).card)
    (highCount : 700*(primesTo (5*2^1021)).card≤5*2^1021)
    (rows : Finset ι) (k : ι→ℕ) (z : ι→ℤ) (weight : ∀ i∈rows, 0<k i ∧ k i≤n) :
    ∃ left : Finset ℕ, 2^1011+1-144*2^512*rows.card≤left.card ∧
      ∀ x∈left, x.Prime ∧ Feasible n x ∧ ∀ i∈rows, ¬Covered24 n (k i) (z i) x := by
  classical
  let pool := core.filter Nat.Prime
  have cover : primesTo (6*2^1021) ⊆ primesTo (5*2^1021) ∪ pool := by
    intro x hx
    obtain ⟨range,pr⟩ := mem_filter.mp hx
    by_cases small : x≤5*2^1021
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,small⟩,pr⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,(mem_Icc.mp range).2⟩,pr⟩)
  have split := (card_le_card cover).trans (card_union_le _ _)
  have size : 2^1011+1≤pool.card := by omega
  have np : 0<n := by norm_num at lo; omega
  have top : n≤2^2048 := by norm_num at hi ⊢; omega
  obtain ⟨left,sz,proof⟩ := pool_survives np top rows k z weight pool
  refine ⟨left,(Nat.sub_le_sub_right size _).trans sz,?_⟩
  intro x hx
  obtain ⟨hp,miss⟩ := proof x hx
  exact ⟨(mem_filter.mp hp).2,core_feasible lo hi (mem_filter.mp hp).1,miss⟩

/-- Round the published unconditional prime-count inequalities at the two
endpoints to the natural-number premises used by `prime_survivors`. -/
theorem dusart_endpoints
    (low : let b : ℕ := 6*2^1021; (b:ℝ)/(log b-1)≤(primesTo b).card)
    (high : let a : ℕ := 5*2^1021; ((primesTo a).card:ℝ)≤(a:ℝ)/(log a-11/10)) :
    6*2^1021 ≤ 710*(primesTo (6*2^1021)).card ∧
      700*(primesTo (5*2^1021)).card ≤ 5*2^1021 := by
  let a : ℕ := 5*2^1021
  let b : ℕ := 6*2^1021
  have loglo (x : ℕ) (hx : 2^1023≤x) : (702:ℝ)≤log x := by
    have bound := log_le_log (by positivity : 0<(2:ℝ)^1023) (by exact_mod_cast hx : (2:ℝ)^1023≤x)
    rw [log_pow] at bound
    norm_num only [Nat.cast_ofNat] at bound
    linarith only [bound,log_two_gt_d9]
  have lA := loglo a (by norm_num [a])
  have lB := loglo b (by norm_num [b])
  have logtop (x : ℕ) (xp : (0:ℝ)<x) (hx : (x:ℝ)≤2^1024) : log x-1≤710 := by
    have bound := log_le_log xp hx
    rw [log_pow] at bound
    norm_num only [Nat.cast_ofNat] at bound
    linarith only [bound,log_two_lt_d9]
  have topB := logtop b (by dsimp [b]; positivity) (by norm_num [b])
  change (b:ℝ)/(log b-1)≤(primesTo b).card at low
  change ((primesTo a).card:ℝ)≤(a:ℝ)/(log a-11/10) at high
  have left := (div_le_iff₀ (sub_pos.mpr ((by norm_num : (1:ℝ)<702).trans_le lB))).mp low
  have right := (le_div_iff₀ (sub_pos.mpr ((by norm_num : (11/10:ℝ)<702).trans_le lA))).mp high
  have cB : (b:ℝ)≤710*(primesTo b).card := by
    rw [mul_comm]
    exact left.trans (mul_le_mul_of_nonneg_left topB (Nat.cast_nonneg _))
  have cA : 700*((primesTo a).card:ℝ)≤a := by
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_left (le_sub_iff_add_le.mpr ((by norm_num : (700:ℝ)+11/10≤702).trans lA))
      (Nat.cast_nonneg _)).trans right
  exact ⟨by exact_mod_cast cB,by exact_mod_cast cA⟩

theorem numerical_budgets : 144*2^512*2^32 < (2:ℕ)^552 ∧
    144*2^512*2^500 < (2:ℕ)^1020 := by decide +kernel

end PrimeFactors.DisplacedTraceCoverage
