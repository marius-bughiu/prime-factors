import PrimeFactors.ReducedOffsetMinimum
import Mathlib.Data.Nat.Sqrt

namespace PrimeFactors.OffsetMinimumThreshold

/-- Allow an odd middle coefficient as well as the original even coefficient. -/
def value (p q t x y : ℤ) : ℤ := p*x^2-t*x*y+q*y^2

theorem even_middle (p q T x y : ℤ) :
    value p q (2*T) x y = ReducedOffsetMinimum.Q p T q x y := by
  unfold value ReducedOffsetMinimum.Q
  ring

/-- With nonnegative weights the three squares x², y², (x-y)² have at
least two positive entries on each nonzero integer vector. -/
theorem floor_value {p q t x y : ℤ} (pp : 0 < p) (ordered : p ≤ q)
    (low : 0 ≤ t) (high : t ≤ 2*p) (nz : x ≠ 0 ∨ y ≠ 0) :
    min p (p+q-t) ≤ value p q t x y := by
  have sq_one (z : ℤ) (h : z ≠ 0) : 1 ≤ z^2 :=
    Int.add_one_le_iff.mpr (sq_pos_of_ne_zero h)
  have p0 := min_le_left p (p+q-t)
  have diag := min_le_right p (p+q-t)
  have norm : 2*value p q t x y =
      (2*p-t)*x^2+(2*q-t)*y^2+t*(x-y)^2 := by unfold value; ring
  have xa := sub_nonneg.mpr high
  have ya : 0 ≤ 2*q-t := by omega
  by_cases xz : x=0
  · have yz := nz.resolve_left (not_not.mpr xz)
    simpa [value, xz] using
      (p0.trans (ordered.trans (le_mul_of_one_le_right (by omega) (sq_one _ yz))))
  by_cases yz : y=0
  · simpa [value, yz] using
      (p0.trans (le_mul_of_one_le_right pp.le (sq_one _ xz)))
  have a := mul_le_mul_of_nonneg_left (sq_one x xz) xa
  have b := mul_le_mul_of_nonneg_left (sq_one y yz) ya
  have c := mul_nonneg low (sq_nonneg (x-y))
  linarith only [norm, a, b, c, diag]

/-- Membership of a specified direction in the set of shortest vectors,
including at ties. -/
def IsShortest (p q t s v : ℤ) : Prop :=
  ∀ x y : ℤ, x ≠ 0 ∨ y ≠ 0 → value p q t s v ≤ value p q t x y

/-- The axis is shortest up to and including the larger factor. -/
theorem axis_iff {p q t : ℤ} (pp : 0 < p) (ordered : p ≤ q)
    (low : 0 ≤ t) (high : t ≤ 2*p) : IsShortest p q t 1 0 ↔ t ≤ q := by
  constructor
  · intro h
    have compare := h 1 1 (Or.inl one_ne_zero)
    simp [value] at compare
    omega
  · intro h x y nz
    have bound := floor_value pp ordered low high (x := x) (y := y) nz
    rw [show value p q t 1 0 = p by simp [value]]
    simpa only [min_eq_left (by omega : p ≤ p+q-t)] using bound

/-- The diagonal is shortest from the larger factor onwards. -/
theorem diagonal_iff {p q t : ℤ} (pp : 0 < p) (ordered : p ≤ q)
    (low : 0 ≤ t) (high : t ≤ 2*p) : IsShortest p q t 1 1 ↔ q ≤ t := by
  have val : value p q t 1 1 = p+q-t := by unfold value; ring
  constructor
  · intro h
    have compare := h 1 0 (Or.inl one_ne_zero)
    rw [val, show value p q t 1 0 = p by simp [value]] at compare
    omega
  · intro h x y nz
    rw [val]
    simpa only [min_eq_right (by omega : p+q-t ≤ p)] using
      (floor_value pp ordered low high (x := x) (y := y) nz)

/-- An additive error allowance gives an exact uncertainty interval for
each of the two possible answers, including when both answers are valid. -/
theorem approximate_directions {p q t e : ℤ} (pp : 0<p) (ordered : p≤q)
    (low : 0≤t) (high : t≤2*p) (err : 0≤e) :
    ((∀ x y : ℤ, x≠0 ∨ y≠0 → value p q t 1 0 ≤ value p q t x y+e) ↔ t≤q+e) ∧
    ((∀ x y : ℤ, x≠0 ∨ y≠0 → value p q t 1 1 ≤ value p q t x y+e) ↔ q≤t+e) := by
  have axis : value p q t 1 0=p := by simp [value]
  have diagonal : value p q t 1 1=p+q-t := by unfold value; ring
  rw [axis, diagonal]
  constructor
  · constructor
    · intro h
      have g := h 1 1 (Or.inl one_ne_zero)
      rw [diagonal] at g
      omega
    · intro h x y nz
      have g := floor_value pp ordered low high nz
      omega
  · constructor
    · intro h
      have g := h 1 0 (Or.inl one_ne_zero)
      rw [axis] at g
      omega
    · intro h x y nz
      have g := floor_value pp ordered low high nz
      omega

/-- A public coefficient interval that contains the breakpoint, for any
positive pair in the balance range. -/
theorem public_endpoint {p q N : ℕ} (product : p*q=N) (balanced : q ≤ 2*p) :
    q ≤ (2*N).sqrt ∧ (2*N).sqrt ≤ 2*p := by
  have qbound := Nat.mul_le_mul_right q balanced
  have pbound := Nat.mul_le_mul_left (2*p) balanced
  refine ⟨Nat.le_sqrt'.mpr (by nlinarith only [qbound,product]), ?_⟩
  have rad : (2*N).sqrt^2 ≤ (2*p)^2 :=
    (Nat.sqrt_le' _).trans (by nlinarith only [pbound,product])
  exact le_of_not_gt fun bad =>
    (not_le_of_gt (Nat.pow_lt_pow_left bad (by decide : 2 ≠ 0))) rad

/-- In the whole public range, simultaneous minimality singles out the
larger factor exactly. At the public endpoint the diagonal always wins. -/
theorem switch {p q N t : ℕ} (product : p*q=N) (pp : 0<p) (ordered : p≤q)
    (balanced : q≤2*p) (limit : t≤(2*N).sqrt) :
    (IsShortest p q t 1 0 ∧ IsShortest p q t 1 1) ↔ t=q := by
  have upper : (t:ℤ)≤2*(p:ℤ) := by exact_mod_cast limit.trans (public_endpoint product balanced).2
  have pos : 0<(p:ℤ) := by exact_mod_cast pp
  have ord : (p:ℤ)≤q := by exact_mod_cast ordered
  rw [axis_iff pos ord (Int.natCast_nonneg _) upper,
    diagonal_iff pos ord (Int.natCast_nonneg _) upper]
  omega

/-- At the endpoint there is a common winning answer for every balanced
factor pair. Determining both shortest directions singles out the breakpoint. -/
theorem endpoint_diagonal {p q N : ℕ} (product : p*q=N) (pp : 0<p)
    (ordered : p≤q) (balanced : q≤2*p) : IsShortest p q (2*N).sqrt 1 1 := by
  obtain ⟨lo,hi⟩ := public_endpoint product balanced
  exact (diagonal_iff (by exact_mod_cast pp) (by exact_mod_cast ordered)
    (Int.natCast_nonneg _) (by exact_mod_cast hi)).mpr (by exact_mod_cast lo)

/-- A hypothetical selector answers true for the axis, false for the
diagonal. Each answer is allowed additive error e in the minimum value. -/
def bracket (answer : ℤ → Bool) (e : ℤ) : ℕ → ℤ → ℤ → ℤ × ℤ
  | 0, l, h => (l,h)
  | n+1, l, h =>
    let t := (l+h)/2
    if answer t then bracket answer e n (max l (t-e)) h
    else bracket answer e n l (min h (t+e))

/-- n queries reduce an initial excess width 2^n B to B, preserving
the interval containing q even if every allowed tie is chosen adversely. -/
theorem bracket_correct (answer : ℤ → Bool) {q e L U B : ℤ}
    (spec : ∀ t, L≤t → t≤U →
      (answer t=true → t≤q+e) ∧ (answer t=false → q≤t+e)) (steps : ℕ) :
    ∀ l h, L≤l → l≤q → q≤h → h≤U → h-l≤2*e+2^steps*B →
      let out := bracket answer e steps l h
      l≤out.1 ∧ out.1≤q ∧ q≤out.2 ∧ out.2≤h ∧ out.2-out.1≤2*e+B := by
  induction steps with
  | zero =>
    intro l h _ lq qh _ width
    exact ⟨le_rfl,lq,qh,le_rfl,by simpa using width⟩
  | succ n ih =>
    intro l h ll lq qh hu width
    let t := (l+h)/2
    have lo : l≤t := by dsimp [t]; omega
    have hi : t≤h := by dsimp [t]; omega
    obtain ⟨axis,diagonal⟩ := spec t (ll.trans lo) (hi.trans hu)
    rw [pow_succ, mul_right_comm ((2:ℤ)^n) 2 B] at width
    cases a : answer t with
    | true =>
      rw [bracket, if_pos a]
      have newL : max l (t-e)≤q := max_le lq (by have := axis a; omega)
      have shrink : h-max l (t-e)≤2*e+2^n*B := by dsimp [t]; omega
      obtain ⟨ordered,bottom,top,last,size⟩ :=
        ih _ _ (ll.trans (le_max_left ..)) newL qh hu shrink
      exact ⟨(le_max_left ..).trans ordered,bottom,top,last,size⟩
    | false =>
      rw [bracket, if_neg (by simp [a] : ¬answer t=true)]
      have newH : q≤min h (t+e) := le_min qh (diagonal a)
      have shrink : min h (t+e)-l≤2*e+2^n*B := by dsimp [t]; omega
      obtain ⟨first,bottom,top,ordered,size⟩ :=
        ih _ _ ll lq newH ((min_le_left ..).trans hu) shrink
      exact ⟨first,bottom,top,ordered.trans (min_le_left ..),size⟩

/-- For two 1024-bit factors one starts with width at most 2^1023.
This conclusion assumes an axis/diagonal prediction with error 2^508
at every query. No such product-only predictor is supplied here. -/
theorem target_bracket (answer : ℤ → Bool) {q l h : ℤ}
    (inside : l≤q ∧ q≤h) (width : h-l≤2^1023)
    (spec : ∀ t, l≤t → t≤h →
      (answer t=true → t≤q+2^508) ∧ (answer t=false → q≤t+2^508)) :
    let out := bracket answer (2^508) 514 l h
    l≤out.1 ∧ out.1≤q ∧ q≤out.2 ∧ out.2≤h ∧ out.2-out.1≤2^510 := by
  have start : (2:ℤ)^1023 ≤ 2*2^508+2^514*2^509 := by decide +kernel
  obtain ⟨a,b,c,d,small⟩ :=
    bracket_correct answer spec 514 l h le_rfl inside.1 inside.2 le_rfl (width.trans start)
  exact ⟨a,b,c,d,small.trans (by decide +kernel)⟩

/-- Taking reciprocals on the larger-factor side does not enlarge the
width of the integer interval. The product supplies division endpoints. -/
theorem reciprocal_span {N l h a b : ℕ} (lp : 0<l) (order : l≤h) (al : a≤l)
    (upper : b*l≤N) (lower : N≤a*h) : b≤a+(h-l) := by
  have gap := Nat.sub_add_cancel order
  have bound := Nat.mul_le_mul_right (h-l) al
  have spread : b*l ≤ (a+(h-l))*l := by
    nlinarith only [upper,lower,bound,congrArg (fun z => a*z) gap]
  exact Nat.le_of_mul_le_mul_right spread lp

/-- The interval for q gives explicit integer endpoints for p using only N.
For N>0, (N-1)/h+1 is the ceiling of N/h. -/
theorem reciprocal_interval {p q N l h : ℕ} (product : p*q=N) (np : 0<N)
    (lp : 0<l) (lo : l≤q) (hi : q≤h) (side : N≤l^2) :
    let a := (N-1)/h+1
    let b := N/l
    a≤p ∧ p≤b ∧ b-a≤h-l := by
  intro a b
  have hp := lp.trans_le (lo.trans hi)
  have cover (z : ℕ) (bound : N≤z*h) : a≤z := by
    exact (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  have ap := cover p (product ▸ Nat.mul_le_mul_left p hi)
  have pb : p≤b := (Nat.le_div_iff_mul_le lp).mpr (product ▸ Nat.mul_le_mul_left p lo)
  have upper : N≤a*h := by
    have rem := Nat.mod_lt (N-1) hp
    have div := Nat.mod_add_div (N-1) h
    dsimp [a]
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm _ h]
    omega
  have al := cover l (side.trans (by simpa only [pow_two] using Nat.mul_le_mul_left l (lo.trans hi)))
  have width := reciprocal_span lp (lo.trans hi) al (Nat.div_mul_le_self N l) upper
  exact ⟨ap,pb,by dsimp [b];omega⟩

end PrimeFactors.OffsetMinimumThreshold
