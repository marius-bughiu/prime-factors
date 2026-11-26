import PrimeFactors.Multiplier
import Mathlib.Algebra.Order.Ring.Abs

namespace PrimeFactors.WeightedTracePrefix

/-- Discriminant of the weighted trace equation a*x + b*(n/x) = h. -/
def disc (n a b h : ℤ) : ℤ := h^2 - 4*a*b*n

/-- The greatest integer t with t² strictly below a positive discriminant. -/
def radius (n a b h : ℤ) : ℤ := (disc n a b h - 1).toNat.sqrt

def lower (n a b h : ℤ) : ℤ := -((radius n a b h - h)/(2*a))
def upper (n a b h : ℤ) : ℤ := (h + radius n a b h)/(2*a)

/-- The positivity guard gives the empty set at and below the tangent trace. -/
def Inside (n a b h x : ℤ) : Prop :=
  0 < disc n a b h ∧ lower n a b h ≤ x ∧ x ≤ upper n a b h

private theorem square_strip {D y : ℤ} (pos : 0 < D) :
    y^2 < D ↔ -((D-1).toNat.sqrt : ℤ) ≤ y ∧ y ≤ (D-1).toNat.sqrt := by
  have hcast : ((D-1).toNat : ℤ) = D-1 := Int.toNat_of_nonneg (by omega)
  have hsq : ((y.natAbs^2 : ℕ) : ℤ) = y^2 := by
    rw [Nat.cast_pow, Int.natCast_natAbs, sq_abs]
  have hc : y^2 < D ↔ y.natAbs^2 ≤ (D-1).toNat := by omega
  rw [hc, ← Nat.le_sqrt']
  have eq : y.natAbs ≤ (D-1).toNat.sqrt ↔
      (y.natAbs : ℤ) ≤ ((D-1).toNat.sqrt : ℤ) := by exact_mod_cast Iff.rfl
  rw [eq, Int.natCast_natAbs, abs_le]

private theorem rounded_bounds {a h x t : ℤ} (ap : 0<a) :
    -((t-h)/(2*a)) ≤ x ∧ x ≤ (h+t)/(2*a) ↔ -t ≤ 2*a*x-h ∧ 2*a*x-h ≤ t := by
  have wp : 0<2*a := by omega
  have lo : -((t-h)/(2*a)) ≤ x ↔ -x ≤ (t-h)/(2*a) := by omega
  rw [lo,Int.le_ediv_iff_mul_le wp,Int.le_ediv_iff_mul_le wp]
  constructor <;> rintro ⟨hl,hr⟩ <;> constructor <;> linarith only [hl,hr]

private theorem complete_square (n a b h x : ℤ) :
    (2*a*x-h)^2-disc n a b h = 4*a*(a*x^2+b*n-h*x) := by
  unfold disc
  ring

/-- Exact integer sublevel, including negative offsets and square discriminants. -/
theorem inside_iff {n a b h x : ℤ} (ap : 0<a) :
    Inside n a b h x ↔ a*x^2+b*n < h*x := by
  have pos : 0<4*a := by omega
  have eq : (2*a*x-h)^2 < disc n a b h ↔ a*x^2+b*n < h*x := by
    rw [← sub_neg, complete_square, ← mul_zero (4*a), mul_lt_mul_iff_of_pos_left pos, sub_neg]
  unfold Inside lower upper radius
  rw [rounded_bounds ap, ←eq]
  by_cases dp : 0<disc n a b h
  · simp only [dp,true_and,square_strip dp]
  · constructor
    · exact fun hyp => (dp hyp.1).elim
    · exact fun hyp => (dp ((sq_nonneg _).trans_lt hyp)).elim

/-- Closed sublevel. Equality at an untested trace is preserved separately. -/
def AtMost (n a b h x : ℤ) : Prop :=
  let t : ℤ := (disc n a b h).toNat.sqrt
  0 ≤ disc n a b h ∧ -((t-h)/(2*a)) ≤ x ∧ x ≤ (h+t)/(2*a)

theorem atMost_iff {n a b h x : ℤ} (ap : 0<a) :
    AtMost n a b h x ↔ a*x^2+b*n ≤ h*x := by
  have pos : 0<4*a := by omega
  have eq : (2*a*x-h)^2 ≤ disc n a b h ↔ a*x^2+b*n ≤ h*x := by
    rw [← sub_nonpos, complete_square, ← mul_zero (4*a), mul_le_mul_iff_of_pos_left pos, sub_nonpos]
  unfold AtMost
  dsimp only
  rw [rounded_bounds ap, ←eq]
  by_cases dp : 0≤disc n a b h
  · have hs := square_strip (y:=2*a*x-h) (D:=disc n a b h+1) (by omega)
    rw [add_sub_cancel_right] at hs
    simp only [dp,true_and]
    omega
  · constructor
    · exact fun hyp => (dp hyp.1).elim
    · exact fun hyp => (dp ((sq_nonneg _).trans hyp)).elim

/-- Immediate neighbors of the endpoints already fail the strict threshold. -/
theorem neighbors {n a b h : ℤ} (ap : 0<a) :
    (¬ a*(lower n a b h-1)^2+b*n < h*(lower n a b h-1)) ∧
    (¬ a*(upper n a b h+1)^2+b*n < h*(upper n a b h+1)) := by
  constructor <;> intro lt
  · have := ((inside_iff ap).mpr lt).2.1
    omega
  · have := ((inside_iff ap).mpr lt).2.2
    omega

/-- Pull the interval back to an arbitrary arithmetic progression of positions. -/
theorem remap {n a b h origin step j : ℤ} (sp : 0<step) :
    Inside n a b h (origin+step*j) ↔ 0<disc n a b h ∧
      -((origin-lower n a b h)/step) ≤ j ∧ j ≤ (upper n a b h-origin)/step := by
  unfold Inside
  have remapLeft : lower n a b h ≤ origin+step*j ↔
      -j ≤ (origin-lower n a b h)/step := by
    rw [Int.le_ediv_iff_mul_le sp]
    constructor <;> intro hj <;> linarith only [hj]
  have remapRight : origin+step*j ≤ upper n a b h ↔ j ≤ (upper n a b h-origin)/step := by
    rw [Int.le_ediv_iff_mul_le sp, mul_comm j step]
    omega
  rw [remapLeft, remapRight]
  omega

/-- For a genuine pair the open interval measures its actual weighted sum. -/
theorem inside_pair {n a b h x y : ℤ} (ap : 0<a) (xp : 0<x) (prod : x*y=n) :
    Inside n a b h x ↔ a*x+b*y < h := by
  rw [inside_iff ap, ← prod]
  convert (mul_lt_mul_iff_of_pos_left xp : x*(a*x+b*y)<x*h ↔ _) using 2 <;> ring

/-- A newly added shell after one stride can contain divisors only on the old threshold. -/
theorem next_shell {n a b h x y stride : ℤ} (ap : 0<a) (xp : 0<x)
    (prod : x*y=n) (residue : stride ∣ a*x+b*y-h) (sp : 0<stride) :
    (Inside n a b (h+stride) x ∧ ¬ Inside n a b h x) ↔ a*x+b*y=h := by
  rw [inside_pair ap xp prod, inside_pair ap xp prod]
  obtain ⟨j,hj⟩ := residue
  constructor
  · rintro ⟨hi,lo⟩
    have j0 : j=0 := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with neg | pos
      · have := mul_neg_of_pos_of_neg sp neg
        omega
      · have := mul_le_mul_of_nonneg_left (show 1≤j by omega) sp.le
        rw [mul_one] at this
        omega
    simp [j0] at hj
    omega
  · intro eq
    omega

/-- A signed square root records the orientation of the two integral factors. -/
def compatible (n a b h v : ℤ) : Bool :=
  decide (v^2=disc n a b h ∧ 2*a ∣ h+v ∧ 2*b ∣ h-v)

/-- Tests both signs, so a square discriminant with incompatible denominators is skipped. -/
def hit (n a b h : ℤ) : Bool :=
  let r : ℤ := (disc n a b h).toNat.sqrt
  compatible n a b h r || compatible n a b h (-r)

theorem hit_iff {n a b h : ℤ} (ap : 0<a) (bp : 0<b) :
    hit n a b h = true ↔ ∃ x y : ℤ, x*y=n ∧ a*x+b*y=h := by
  have read {v : ℤ} (hv : compatible n a b h v = true) :
      ∃ x y : ℤ, x*y=n ∧ a*x+b*y=h := by
    obtain ⟨sq,⟨x,hx⟩,⟨y,hy⟩⟩ := of_decide_eq_true hv
    refine ⟨x,y,?_,by linarith only [hx,hy]⟩
    have eq : 4*a*b*(x*y-n)=0 := by
      have inv := congrArg₂ (· * ·) hx hy
      dsimp at inv
      unfold disc at sq
      nlinarith only [inv,sq]
    have non : 4*a*b ≠ 0 := by positivity
    exact sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_left non)
  unfold hit
  rw [Bool.or_eq_true]
  constructor
  · rintro (hv|hv) <;> exact read hv
  · rintro ⟨x,y,rfl,rfl⟩
    have sq : disc (x*y) a b (a*x+b*y) = (a*x-b*y)^2 := by unfold disc; ring
    have value : ((disc (x*y) a b (a*x+b*y)).toNat.sqrt : ℤ) = |a*x-b*y| := by
      rw [sq,← sq_abs, ← Int.natCast_natAbs, ← Nat.cast_pow,Int.toNat_natCast,Nat.sqrt_eq',
        Int.natCast_natAbs]
    rw [value]
    have ok : compatible (x*y) a b (a*x+b*y) (a*x-b*y) = true := by
      apply decide_eq_true
      exact ⟨sq.symm,⟨x,by ring⟩,⟨y,by ring⟩⟩
    rcases le_or_gt 0 (a*x-b*y) with pos | neg
    · exact Or.inl (by simpa [abs_of_nonneg pos] using ok)
    · exact Or.inr (by simpa [abs_of_neg neg] using ok)


/-- Trace labels of a given residue, starting at the first label at or above
the AM–GM lower bound. The residue need not be the least residue. -/
def level (n a b : ℕ) (residue stride : ℤ) (i : ℕ) : ℤ :=
  let floor : ℤ := ceilSqrt (4*a*b*n)
  residue + stride * ((i:ℤ) - (residue-floor)/stride)

def prefixMiss (n a b : ℕ) (residue stride : ℤ) (count : ℕ) : Bool :=
  (List.range count).all fun i => !(hit n a b (level n a b residue stride i))

private theorem locate {n a b x y : ℕ} (prod : x*y=n) {residue stride : ℤ}
    (sp : 0<stride) (cong : stride ∣ (a*x+b*y:ℕ)-residue) (k : ℕ)
    (below : (a*x+b*y:ℕ) < level n a b residue stride k) :
    ∃ i : ℕ, i<k ∧ (a*x+b*y:ℕ) = level n a b residue stride i := by
  let floor : ℤ := ceilSqrt (4*a*b*n)
  have least : ceilSqrt (4*a*b*n) ≤ a*x+b*y := by
    apply ceilSqrt_le_iff.mpr
    rw [← prod]
    zify
    nlinarith only [sq_nonneg ((a:ℤ)*x-b*y)]
  have hf : floor ≤ (a*x+b*y:ℕ) := by unfold floor; exact_mod_cast least
  obtain ⟨j,hj⟩ := cong
  have low : -j ≤ (residue-floor)/stride := (Int.le_ediv_iff_mul_le sp).mpr (by
    linarith only [hj,hf])
  let i := j+(residue-floor)/stride
  have nonneg : 0 ≤ i := by dsimp [i]; omega
  have eq : (a*x+b*y:ℕ) = level n a b residue stride i.toNat := by
    unfold level
    rw [Int.toNat_of_nonneg nonneg]
    change _ = residue+stride*(j+(residue-floor)/stride-(residue-floor)/stride)
    rw [add_sub_cancel_right]
    omega
  refine ⟨i.toNat,?_,eq⟩
  rw [eq] at below
  unfold level at below
  have := (mul_lt_mul_iff_of_pos_left sp).mp (lt_of_add_lt_add_left below)
  omega

/-- A prefix checked from the product rules out every divisor in the exact band.
Any known residue stride can replace parity. No primality assumption is needed. -/
theorem prefix_excludes {n a b x y : ℕ} (ap : 0<a) (bp : 0<b) (xp : 0<x)
    {residue stride : ℤ} (sp : 0<stride) (prod : x*y=n)
    (cong : stride ∣ (a*x+b*y:ℕ)-residue) {k : ℕ}
    (miss : prefixMiss n a b residue stride k = true) :
    ¬ Inside n a b (level n a b residue stride k) x := by
  intro mem
  have hp : (x:ℤ)*y=n := by exact_mod_cast prod
  have below := (inside_pair (by exact_mod_cast ap) (by exact_mod_cast xp) hp).mp mem
  obtain ⟨i,lt,eq⟩ := locate prod sp cong k (by exact_mod_cast below)
  have ok := List.all_eq_true.mp miss i (List.mem_range.mpr lt)
  have heq : (a:ℤ)*x+b*y=level n a b residue stride i := by exact_mod_cast eq
  have found := (hit_iff (by exact_mod_cast ap) (by exact_mod_cast bp)).mpr
    ⟨(x:ℤ),(y:ℤ),hp,heq⟩
  simp [found] at ok

/-- Exact preimage of an arbitrary consecutive run. Outside the central
closed interval there can be two disjoint components. -/
def Run (n a b first stride : ℤ) (count : ℕ) (x : ℤ) : Prop :=
  Inside n a b (first+stride*count) x ∧ ¬ AtMost n a b (first-stride) x

/-- An actual divisor in either component corresponds to precisely one of the
tested labels, even when the tested run begins above the minimum trace. -/
theorem run_pair {n a b first stride x y : ℤ} (ap : 0<a) (sp : 0<stride) (xp : 0<x)
    (prod : x*y=n) (residue : stride ∣ a*x+b*y-first) (count : ℕ) :
    Run n a b first stride count x ↔
      ∃ i : ℕ, i<count ∧ a*x+b*y=first+stride*i := by
  have eq : AtMost n a b (first-stride) x ↔ a*x+b*y≤first-stride := by
    rw [atMost_iff ap,←prod]
    convert (mul_le_mul_iff_of_pos_left xp : x*(a*x+b*y)≤x*(first-stride) ↔ _) using 2 <;> ring
  rw [Run,inside_pair ap xp prod,eq,not_le]
  obtain ⟨j,hj⟩ := residue
  have e : a*x+b*y=first+stride*j := by linarith only [hj]
  constructor
  · rintro ⟨hi,lo⟩
    rw [e] at hi lo
    have jl : -1 < j := (mul_lt_mul_iff_of_pos_left sp).mp (by linarith only [lo])
    have ju : j < (count:ℤ) := (mul_lt_mul_iff_of_pos_left sp).mp (by omega)
    exact ⟨j.toNat,by omega,by rwa [Int.toNat_of_nonneg (by omega)]⟩
  · rintro ⟨i,lt,hi⟩
    rw [hi]
    have z : (i:ℤ)<count := by exact_mod_cast lt
    have low := mul_nonneg sp.le (Int.natCast_nonneg i)
    have high := (mul_lt_mul_iff_of_pos_left sp).mpr z
    omega

def runMiss (n a b first stride : ℤ) (count : ℕ) : Bool :=
  (List.range count).all fun i => !(hit n a b (first+stride*i))

theorem run_excludes {n a b first stride x y : ℤ} (ap : 0<a) (bp : 0<b)
    (sp : 0<stride) (xp : 0<x) (prod : x*y=n) (residue : stride ∣ a*x+b*y-first)
    {count : ℕ} (miss : runMiss n a b first stride count = true) :
    ¬ Run n a b first stride count x := by
  intro mem
  obtain ⟨i,lt,row⟩ := (run_pair ap sp xp prod residue count).mp mem
  have hv := (hit_iff ap bp).mpr ⟨x,y,prod,row⟩
  have test := List.all_eq_true.mp miss i (List.mem_range.mpr lt)
  simp [hv] at test

/-- Compute the first and last block indices whose entire closed interval
[origin + step*j - w, origin + step*j + w] fits the reusable prefix. -/
theorem block_indices {n a b h origin step w j : ℤ} (sp : 0<step) (wp : 0≤w) :
    (∀ x, origin+step*j-w≤x → x≤origin+step*j+w → Inside n a b h x) ↔
      0<disc n a b h ∧ -((origin-w-lower n a b h)/step)≤j ∧
      j≤(upper n a b h-origin-w)/step := by
  constructor
  · intro all
    obtain ⟨dp,left,_⟩ := all (origin+step*j-w) le_rfl (by omega)
    obtain ⟨_,_,right⟩ := all (origin+step*j+w) (by omega) le_rfl
    have lb := (Int.le_ediv_iff_mul_le sp).mpr
      (show -j*step≤origin-w-lower n a b h by linarith only [left])
    refine ⟨dp,by omega,(Int.le_ediv_iff_mul_le sp).mpr ?_⟩
    linarith only [right]
  · rintro ⟨dp,lb,ub⟩ x xl xu
    have left := (Int.le_ediv_iff_mul_le sp).mp
      (show -j≤(origin-w-lower n a b h)/step by omega)
    have right := (Int.le_ediv_iff_mul_le sp).mp ub
    refine ⟨dp,?_,?_⟩ <;> linarith only [left,right,xl,xu]

/-- The familiar parity class for all divisors of an odd product. -/
theorem parity {n x y : ℕ} (prod : x*y=n) (odd : n%2=1) (a b : ℕ) :
    (2:ℤ) ∣ (a*x+b*y:ℕ)-((a+b:ℕ):ℤ) := by
  have hx : x%2=1 := by
    rw [← prod,Nat.mul_mod] at odd
    rcases Nat.mod_two_eq_zero_or_one x with hh|hh <;> simp_all
  have hy : y%2=1 := by
    rw [← prod,mul_comm,Nat.mul_mod] at odd
    rcases Nat.mod_two_eq_zero_or_one y with hh|hh <;> simp_all
  have ex : (x:ℤ) = 2*(x/2:ℕ)+1 := by omega
  have ey : (y:ℤ) = 2*(y/2:ℕ)+1 := by omega
  refine ⟨(a:ℤ)*(x/2:ℕ)+b*(y/2:ℕ),?_⟩
  simp only [Nat.cast_add,Nat.cast_mul]
  rw [ex,ey]
  ring

/-- Each integer root supplied for a trace is checked between consecutive squares.
The multiplier enters only through the shared target 4*k*n. -/
def brackets (target first : ℕ) (roots : List ℕ) : Bool :=
  (List.range roots.length).all fun i =>
    let r := roots[i]?.getD 0
    decide (target+r^2 < (first+i)^2 ∧ (first+i)^2 < target+(r+1)^2)

theorem brackets_sound {target first : ℕ} {roots : List ℕ}
    (ok : brackets target first roots = true) {i : ℕ} (index : i<roots.length) (v : ℕ) :
    (first+i)^2 ≠ target+v^2 := by
  obtain ⟨lo,hi⟩ := of_decide_eq_true (List.all_eq_true.mp ok i (List.mem_range.mpr index))
  let r := roots[i]?.getD 0
  change target+r^2<(first+i)^2 at lo
  change (first+i)^2<target+(r+1)^2 at hi
  rcases le_or_gt v r with small|big
  · have := Nat.pow_le_pow_left small 2
    omega
  · have := Nat.pow_le_pow_left (show r+1≤v by omega) 2
    omega

/-- A finite interval certificate reused for any ordered factorization of k.
The shared discriminants appear in one hypothesis independently of both endpoints. -/
theorem shared_excludes {n k first count a b l u : ℕ}
    (checked : ∀ i<count, ∀ v : ℕ, (first+i)^2 ≠ 4*k*n+v^2)
    (start : (first-1)^2 < 4*k*n) (weights : a*b=k) (ap : 0<a) (lp : 0<l)
    (left : a*l^2+b*n < (first+count)*l) (right : a*u^2+b*n < (first+count)*u)
    (x : ℕ) (xl : l≤x) (xu : x≤u) : ¬ x∣n := by
  rintro ⟨y,prod⟩
  have za : (0:ℤ)<a := by exact_mod_cast ap
  let h : ℤ := (first+count:ℕ)
  obtain ⟨dp,ll,_⟩ := (inside_iff za).mpr
    (show (a:ℤ)*(l:ℤ)^2+(b:ℤ)*n<h*l by unfold h; exact_mod_cast left)
  obtain ⟨_,_,uu⟩ := (inside_iff za).mpr
    (show (a:ℤ)*(u:ℤ)^2+(b:ℤ)*n<h*u by unfold h; exact_mod_cast right)
  have pos : 0<x := lp.trans_le xl
  have mem : Inside n a b h x := ⟨dp,ll.trans (by exact_mod_cast xl),
    le_trans (by exact_mod_cast xu) uu⟩
  have top : a*x+b*y<first+count := by
    have below := (inside_pair za (by exact_mod_cast pos)
      (show (x:ℤ)*y=n by exact_mod_cast prod.symm)).mp mem
    unfold h at below
    exact_mod_cast below
  have square := multiplier_sum_square x y a b
  rw [←prod, mul_assoc 4 a b,weights] at square
  have low : first≤a*x+b*y := by
    by_contra small
    have sm : a*x+b*y < first := Nat.lt_of_not_ge small
    have bound := Nat.le_pred_of_lt sm
    have big : 4*k*n ≤ (a*x+b*y)^2 := by rw [square]; exact Nat.le_add_right _ _
    exact (not_le_of_gt start) (big.trans (Nat.pow_le_pow_left bound 2))
  have result := checked (a*x+b*y-first) (by omega) (Nat.dist (a*x) (b*y))
  rw [show first+(a*x+b*y-first)=a*x+b*y by omega] at result
  exact result square

/-- A single gcd per square is enough for all ordered allocations with the
same multiplier coprime to n. The two possible factors need not be prime. -/
theorem shared_gcd {n k a b p q h : ℕ} (prod : p*q=n) (weights : a*b=k)
    (cop : k.Coprime n) (sum : h=a*p+b*q) :
    let r := (h^2-4*k*n).sqrt
    n.gcd ((h+r)/2)=p ∨ n.gcd ((h+r)/2)=q := by
  subst n k h
  have sq := multiplier_sum_square p q a b
  rw [mul_assoc 4 a b] at sq
  dsimp only
  rw [sq,Nat.add_sub_cancel_left,Nat.sqrt_eq']
  rcases le_total (a*p) (b*q) with le|le
  · right
    rw [Nat.dist_eq_sub_of_le le]
    have eq : (a*p+b*q+(b*q-a*p))/2=b*q := by omega
    have ok := ((cop.coprime_dvd_left (dvd_mul_left b a)).coprime_dvd_right (dvd_mul_right p q)).symm
    rw [eq,mul_comm p q,mul_comm b q,Nat.gcd_mul_left,ok.gcd_eq_one,mul_one]
  · left
    rw [Nat.dist_eq_sub_of_le_right le]
    have eq : (a*p+b*q+(a*p-b*q))/2=a*p := by omega
    have ok := ((cop.coprime_dvd_left (dvd_mul_right a b)).coprime_dvd_right (dvd_mul_left q p)).symm
    rw [eq,mul_comm a p,Nat.gcd_mul_left,ok.gcd_eq_one,mul_one]

/-- Join adjoining or overlapping verified pieces of an interval. -/
theorem join {n l u split next : ℕ} (touch : next≤split+1)
    (left : ∀ x, l≤x → x≤split → ¬x∣n) (right : ∀ x, next≤x → x≤u → ¬x∣n)
    (x : ℕ) (xl : l≤x) (xu : x≤u) : ¬x∣n := by
  by_cases h : x≤split
  · exact left x xl h
  · exact right x (by omega) xu

/-- At 319 the checked even labels 36 and 38 cover exactly 12..28.
The first untested label 40 has integral roots at both immediate neighbors. -/
theorem example_adjacent :
    level 319 1 1 2 2 0=36 ∧ level 319 1 1 2 2 2=40 ∧
    prefixMiss 319 1 1 2 2 2=true ∧
    lower 319 1 1 40=12 ∧ upper 319 1 1 40=28 ∧
    hit 319 1 1 40=true ∧ 11*29=(319:ℕ) := by decide +kernel

end PrimeFactors.WeightedTracePrefix
