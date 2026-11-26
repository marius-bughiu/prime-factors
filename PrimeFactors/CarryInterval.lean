import PrimeFactors.ArbitraryDivisorWindow
import PrimeFactors.PredictedTraceCarries
import PrimeFactors.Fermat

/-! For a fixed radix and high carry, group a whole interval of low carries.
Inverting the permissible sum interval gives an integer divisor window on
the auxiliary product M=CN. The window can contain even composite divisors.
A successful public curvature check reduces this window to at most two
auxiliary trace labels and at most four proposed roots. -/

namespace PrimeFactors.CarryInterval
open ArbitraryDivisorWindow

/-- Smallest possible integral value of the smaller root at upper sum H. -/
def lower (M H : ℕ) := (H-(H^2-4*M).sqrt+1)/2

/-- Largest possible integral value of the smaller root at lower sum L,
where callers clip L at the ceiling of twice the square root of M. -/
def upper (M L : ℕ) := (L-ceilSqrt (L^2-4*M))/2

private theorem square_comparison {u x y M : ℕ} (prod : x*y=M) (xp : 0<x)
    (uLarge : 2*x≤u) (floor : 4*M≤u^2) :
    ((u-2*x)^2≤u^2-4*M ↔ x+y≤u) ∧ (u^2-4*M≤(u-2*x)^2 ↔ u≤x+y) := by
  have diff : (((u-2*x)^2:ℕ):ℤ)-((u^2-4*M:ℕ):ℤ)=4*x*((x:ℤ)+y-u) := by
    simp only [Nat.cast_sub floor,Nat.cast_sub uLarge,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat]
    rw [←prod,Nat.cast_mul]; ring
  have pos : 0<4*(x:ℤ) := by positivity
  constructor <;> constructor
  · intro le
    have h : 4*(x:ℤ)*((x:ℤ)+y-u)≤0 := diff ▸ sub_nonpos.mpr (by exact_mod_cast le)
    have small := nonpos_of_mul_nonpos_right h pos
    omega
  · intro le
    have h := mul_nonpos_of_nonneg_of_nonpos pos.le (show (x:ℤ)+y-u≤0 by omega)
    rw [←diff] at h
    exact_mod_cast sub_nonpos.mp h
  · intro le
    have h : 0≤4*(x:ℤ)*((x:ℤ)+y-u) := diff ▸ sub_nonneg.mpr (by exact_mod_cast le)
    have small := nonneg_of_mul_nonneg_right h pos
    omega
  · intro le
    have h := mul_nonneg pos.le (show 0≤(x:ℤ)+y-u by omega)
    rw [←diff] at h
    exact_mod_cast sub_nonneg.mp h

/-- Exact integer inversion of a clipped trace interval. No primality,
parity or equal-width assumption is needed on either auxiliary root. -/
theorem inverse_iff {M L H x y : ℕ} (prod : x*y=M) (xp : 0<x) (order : x≤y)
    (clip : 4*M≤L^2) (limits : L≤H) :
    (L≤x+y ∧ x+y≤H) ↔ lower M H≤x ∧ x≤upper M L := by
  have ll : 2*x≤L := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    apply le_trans _ clip
    rw [←prod]; nlinarith only [Nat.mul_le_mul_left x order]
  have big := clip.trans (Nat.pow_le_pow_left limits 2)
  have high := (square_comparison (u:=H) prod xp (ll.trans limits) big).1
  have low := (square_comparison (u:=L) prod xp ll clip).2
  have below : ceilSqrt (L^2-4*M)≤L := ceilSqrt_le_iff.mpr (Nat.sub_le ..)
  rw [←low,←high,←ceilSqrt_le_iff,←Nat.le_sqrt']
  unfold lower upper
  omega

/-- The final integral trace strictly below the strip's upper endpoint. -/
def lastLabel (M c a b : ℤ) : ℤ := (2*(a*c^2+b*M)+3*c-1)/(2*c)

/-- Two adjacent labels suffice even when the input or either divisor is even. -/
theorem two_labels {M c w a b x y : ℤ} (cur : Curvature M c w b)
    (wt : Weights M c w a b) (prod : M=x*y) (nearby : |x-c|≤w) :
    a*x+b*y=lastLabel M c a b-1 ∨ a*x+b*y=lastLabel M c a b := by
  obtain ⟨l,h⟩ := strip cur wt prod nearby
  have den : 0<2*c := by linarith only [cur.2.1,cur.2.2.1]
  let s := a*x+b*y
  have hi : s≤lastLabel M c a b := by
    apply (Int.le_ediv_iff_mul_le den).mpr
    dsimp [s]
    nlinarith only [h]
  have lo : lastLabel M c a b<s+2 := by
    apply (Int.ediv_lt_iff_lt_mul den).mpr
    dsimp [s]
    nlinarith only [l]
  change s=_ ∨ s=_
  omega

/-- Both signs of the exact discriminant are included. The division here
is an overcount; the executable also checks divisibility before accepting. -/
def roots (M a b z : ℤ) : List ℤ :=
  let δ := z^2-4*a*b*M
  let r : ℤ := δ.toNat.sqrt
  if r^2=δ then [(z-r)/(2*a),(z+r)/(2*a)] else []

def rootList (M c a b : ℤ) : List ℤ :=
  roots M a b (lastLabel M c a b-1) ++ roots M a b (lastLabel M c a b)

theorem at_most_four (M c a b : ℤ) : (rootList M c a b).length≤4 := by
  have cost (z : ℤ) : (roots M a b z).length≤2 := by unfold roots; dsimp only; split <;> simp
  simpa only [rootList,List.length_append] using
    Nat.add_le_add (cost (lastLabel M c a b-1)) (cost (lastLabel M c a b))

private theorem roots_mem {M a b x y z : ℤ} (ap : 0<a) (prod : M=x*y)
    (trace : a*x+b*y=z) : x∈roots M a b z := by
  let g := a*x-b*y
  have sq : z^2-4*a*b*M=g^2 := by dsimp [g]; rw [←trace,prod]; ring
  have eqNat : (g^2).toNat=g.natAbs^2 := by
    apply Int.ofNat_inj.mp
    rw [Int.toNat_of_nonneg (sq_nonneg g),Nat.cast_pow,Int.natCast_natAbs,sq_abs]
  simp only [roots,sq,eqNat,Nat.sqrt_eq',Int.natCast_natAbs,sq_abs,if_true,
    List.mem_cons,List.not_mem_nil,or_false]
  have den : 2*a≠0 := by omega
  rw [←trace]
  rcases le_total g 0 with le|ge
  · left
    rw [abs_of_nonpos le,show a*x+b*y- -g=x*(2*a) by dsimp [g]; ring,Int.mul_ediv_cancel _ den]
  · right
    rw [abs_of_nonneg ge,show a*x+b*y+g=x*(2*a) by dsimp [g]; ring,Int.mul_ediv_cancel _ den]

theorem rootList_mem {M c w a b x y : ℤ} (cur : Curvature M c w b)
    (wt : Weights M c w a b) (prod : M=x*y) (nearby : |x-c|≤w) :
    x∈rootList M c a b := by
  rcases two_labels cur wt prod nearby with first|last
  · exact List.mem_append_left _ (roots_mem wt.1 prod first)
  · exact List.mem_append_right _ (roots_mem wt.1 prod last)

/-- Whenever the computed divisor window fits the curvature check, the
smaller root for every candidate sum in the clipped interval is on one
public list. Testing both quadratic roots for each trace is essential. -/
theorem covers_sum_interval {M L H x y c w a b : ℕ} (prod : x*y=M) (xp : 0<x)
    (order : x≤y) (clip : 4*M≤L^2) (sums : L≤x+y ∧ x+y≤H)
    (fit : c≤lower M H+w ∧ upper M L≤c+w)
    (cur : Curvature M c w b) (wt : Weights M c w a b) :
    (x:ℤ)∈rootList M c a b := by
  have bounds := (inverse_iff prod xp order clip (sums.1.trans sums.2)).mp sums
  exact rootList_mem (y:=(y:ℤ)) cur wt (by exact_mod_cast prod.symm)
    (abs_le.mpr ⟨by omega,by omega⟩)

private theorem pair_of_square {M t r : ℕ} (mp : 0<M) (sq : r^2+4*M=t^2)
    (even : (t+r)%2=0) :
    ∃ x y : ℕ, 0<x ∧ x≤y ∧ x*y=M ∧ x+y=t ∧ y=(t+r)/2 := by
  let y := (t+r)/2
  let x := t-y
  have rt : r≤t := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (by omega)
  have sum : x+y=t := by dsimp [x,y]; omega
  have plus : y=x+r := by dsimp [x,y]; omega
  have pair : x*y=M := by
    rw [←sum,plus] at sq
    rw [plus]
    nlinarith only [sq]
  exact ⟨x,y,by by_contra! bad; have := Nat.eq_zero_of_le_zero bad; simp_all,
    by omega,pair,sum,rfl⟩

/-- A returned direct probe supplies an ordered auxiliary factor pair,
even if its signed square root, weighted factors and low carry were not
chosen from known prime factors. -/
theorem pair_of_probe {n D f : ℕ} {h k : ℤ} (np : 0<n)
    (hit : PredictedTraceCarries.probe n D h k=some f) :
    ∃ x y : ℕ, 0<x ∧ x≤y ∧ x*y=(PredictedTraceCarries.coefficient n D h).toNat*n ∧
      ((x+y:ℕ):ℤ)=PredictedTraceCarries.label n D h k ∧ n.gcd y=f := by
  simp only [PredictedTraceCarries.probe] at hit
  split at hit
  next guards =>
    obtain ⟨cp,tp,sq,even,_,_⟩ := guards
    let C := (PredictedTraceCarries.coefficient n D h).toNat
    have cpos : 0<C := by dsimp [C]; omega
    rw [Nat.mul_assoc 4 C n] at sq even hit
    obtain ⟨x,y,xp,xy,pair,sum,larger⟩ := pair_of_square (Nat.mul_pos cpos np) sq even
    refine ⟨x,y,xp,xy,pair,?_,?_⟩
    · rw [sum,Int.toNat_of_nonneg tp.le]
    · rw [larger]
      exact Option.some.inj hit
  next => contradiction

/-- The smaller auxiliary divisor of *every* splitting direct probe at
every low carry in the budget lies on the very same public list. The gcd
of its complementary divisor gives exactly the direct probe's returned
factor. The center trace S₀ is public and nonnegative. -/
theorem covers_probes {n D budget c w a b S₀ : ℕ} {h : ℤ} (np : 0<n)
    (center : PredictedTraceCarries.label n D h 0=(S₀:ℤ)) :
    let M := (PredictedTraceCarries.coefficient n D h).toNat*n
    let L := max (ceilSqrt (4*M)) (S₀-budget)
    let H := S₀+budget
    (c≤lower M H+w ∧ upper M L≤c+w) →
    Curvature M c w b → Weights M c w a b →
    ∀ k : ℤ, |k|≤budget → ∀ f, PredictedTraceCarries.probe n D h k=some f →
      ∃ x : ℕ, 0<x ∧ (x:ℤ)∈rootList M c a b ∧ x∣M ∧ n.gcd (M/x)=f := by
  dsimp only
  intro fit cur wt k kk f success
  obtain ⟨x,y,xp,order,pair,sum,recovery⟩ := pair_of_probe np success
  let M := (PredictedTraceCarries.coefficient n D h).toNat*n
  have scaled : 4*M≤(x+y)^2 := by rw [←show x*y=M from pair]; nlinarith only [sq_nonneg ((x:ℤ)-y)]
  have dx : PredictedTraceCarries.label n D h k=(S₀:ℤ)-k := by
    rw [←center]; simp only [PredictedTraceCarries.label,sub_zero]
  rw [dx] at sum
  have bounds := abs_le.mp kk
  have sums : max (ceilSqrt (4*M)) (S₀-budget)≤x+y ∧ x+y≤S₀+budget :=
    ⟨max_le (ceilSqrt_le_iff.mpr scaled) (by omega),by omega⟩
  have clip := ceilSqrt_le_iff.mp (le_max_left (ceilSqrt (4*M)) (S₀-budget))
  refine ⟨x,xp,covers_sum_interval (y:=y) pair xp order clip sums fit cur wt,⟨y,pair.symm⟩,?_⟩
  rw [←pair,Nat.mul_div_cancel_left y xp,recovery]

/-- One-sided adjacent squares suffice to check the inverse bounds for a
band wholly above the parabola's minimum. Concrete certificates avoid
kernel evaluation of an enormous natural square root. -/
theorem fit_checked {M c w S₀ E f u : ℕ} (beyond : 4*M≤(S₀-E)^2)
    (top : (S₀+E)^2-4*M < (f+1)^2)
    (bottom : u=0 ∨ (u-1)^2 < (S₀-E)^2-4*M)
    (reach : c≤(S₀+E-f+1)/2+w ∧ (S₀-E-u)/2≤c+w) :
    c≤lower M (S₀+E)+w ∧ upper M (max (ceilSqrt (4*M)) (S₀-E))≤c+w := by
  rw [max_eq_right (ceilSqrt_le_iff.mpr beyond)]
  have hi := Nat.sqrt_lt'.mpr top
  have lo : u≤ceilSqrt ((S₀-E)^2-4*M) := by
    rcases bottom with zero|strict
    · omega
    · by_contra! neg
      have eq := ceilSqrt_le_iff.mp (show ceilSqrt ((S₀-E)^2-4*M)≤u-1 by omega)
      omega
  unfold lower upper
  omega

/-- Check a nonsquare by its sign or by the adjacent nonnegative squares. -/
def NotSquareAt (rad t : ℤ) : Prop := rad<0 ∨ (0≤t ∧ t^2<rad ∧ rad<(t+1)^2)
noncomputable instance (rad t : ℤ) : Decidable (NotSquareAt rad t) := by unfold NotSquareAt; infer_instance

private theorem empty_roots {M a b z t : ℤ} (invalid : NotSquareAt (z^2-4*a*b*M) t) :
    roots M a b z=[] := by
  simp only [roots]
  split
  next square =>
    obtain bad|⟨pos,lo,hi⟩ := invalid
    · linarith only [square,sq_nonneg (((z^2-4*a*b*M).toNat.sqrt:ℕ):ℤ),bad]
    · rw [←square] at lo hi
      have nonneg : (0:ℤ)≤((z^2-4*a*b*M).toNat.sqrt:ℕ) := by positivity
      have l := (sq_lt_sq₀ pos nonneg).mp lo
      have h := (sq_lt_sq₀ nonneg (by omega : (0:ℤ)≤t+1)).mp hi
      omega
  next => rfl

/-- Two verified nonsquares rule out *every* low carry in the supplied
budget, including unsuccessful traces whose underlying roots could have
been composite or even. -/
theorem excludes_of_nonsquares {n D budget c w a b S₀ : ℕ} {h r₁ r₂ : ℤ} (np : 0<n)
    (center : PredictedTraceCarries.label n D h 0=(S₀:ℤ)) :
    let M := (PredictedTraceCarries.coefficient n D h).toNat*n
    let L := max (ceilSqrt (4*M)) (S₀-budget)
    let H := S₀+budget
    let z := lastLabel M c a b
    (c≤lower M H+w ∧ upper M L≤c+w) →
    Curvature M c w b → Weights M c w a b →
    NotSquareAt ((z-1)^2-4*(a:ℤ)*b*M) r₁ →
    NotSquareAt (z^2-4*(a:ℤ)*b*M) r₂ →
    ∀ k : ℤ, |k|≤budget → PredictedTraceCarries.probe n D h k=none := by
  dsimp only
  intro fit cur wt l r k bounded
  cases success : PredictedTraceCarries.probe n D h k with
  | none => rfl
  | some f =>
    obtain ⟨x,_,hx,_,_⟩ := covers_probes np center fit cur wt k bounded f success
    simp only [rootList,empty_roots l,empty_roots r,List.nil_append,List.not_mem_nil] at hx

end PrimeFactors.CarryInterval
