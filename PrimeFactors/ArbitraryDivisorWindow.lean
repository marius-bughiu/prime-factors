import PrimeFactors.RootIntervalSlope

namespace PrimeFactors.ArbitraryDivisorWindow

set_option maxRecDepth 16000
set_option exponentiation.threshold 2048

/-- The center and its radius admit the public approximation and curvature bounds. -/
def Window (n c w : ℤ) : Prop :=
  0 < w ∧ 0 < c ∧ c ^ 2 ≤ n ∧ n ≤ 2 * c ^ 2 ∧ 4 * w ^ 3 < c - w

/-- A checkable approximation of the public ratio N/c². -/
def Weights (n c w a b : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ b ≤ 2*w ∧ |a*c^2-b*n| *(2*w+1) ≤ c^2

/-- Dirichlet approximation supplies positive weights for every admissible center. -/
theorem weights_exist {n c w : ℕ} (win : Window n c w) :
    ∃ a b : ℤ, Weights n c w a b := by
  obtain ⟨wp,cp,cn,_,_⟩ := win
  have cw : 0 < c ^ 2 := by exact_mod_cast sq_pos_of_pos cp
  have ww : 0 < 2*w := by omega
  obtain ⟨b, blo, bhi, a, err⟩ := boundedSlope_exists (c^2) (2*w) n cw ww
  push_cast at err
  rw [abs_sub_comm, mul_comm ((c:ℤ)^2) a] at err
  have bz : (1:ℤ) ≤ b := by exact_mod_cast blo
  have nz : (0:ℤ) ≤ n := by positivity
  have cc := sq_pos_of_pos cp
  have ap : 0 < a := by
    by_contra! neg
    have an := mul_nonpos_of_nonpos_of_nonneg neg cc.le
    have bn := mul_le_mul_of_nonneg_right bz nz
    have gap : (c:ℤ)^2 ≤ - (a*c^2-(b:ℤ)*n) := by linarith
    have ae := neg_le_abs (a*c^2-(b:ℤ)*n)
    have extra := mul_pos (show (0:ℤ) < |a*c^2-(b:ℤ)*n| by linarith) wp
    nlinarith only [err,gap,ae,extra]
  exact ⟨a,b,ap,by omega,by exact_mod_cast bhi,err⟩

/-- The greatest integer trace of the required parity strictly below the public upper bound. -/
def traceRow (n c a b : ℤ) : ℤ :=
  a+b + 2*((2*(a*c^2+b*n)+3*c-1-2*c*(a+b))/(4*c))

/-- Direct curvature test used after weights have been chosen. Its non-strict
inequality suffices because the linear approximation is strict. -/
def Curvature (n c w b : ℤ) : Prop :=
  0 ≤ n ∧ 0 < w ∧ w < c ∧ b*n*w^2 ≤ c^2*(c-w)

theorem curvature_of_window {n c w a b : ℤ} (win : Window n c w)
    (wt : Weights n c w a b) : Curvature n c w b := by
  obtain ⟨wp,cp,cn,nhi,size⟩ := win
  have npos := (sq_nonneg c).trans cn
  refine ⟨npos,wp,by linarith only [size,show 0 < 4*w^3 by positivity],?_⟩
  calc
    b*n*w^2 ≤ (2*w)*(2*c^2)*w^2 := mul_le_mul_of_nonneg_right
      (mul_le_mul wt.2.2.1 nhi npos (by positivity)) (sq_nonneg w)
    _ = c^2*(4*w^3) := by ring
    _ ≤ c^2*(c-w) := mul_le_mul_of_nonneg_left size.le (sq_nonneg c)

/-- The curvature and weight bounds place every divisor's weighted sum
inside this open interval of length two, at either parity. -/
theorem strip {n c w a b d q : ℤ} (cur : Curvature n c w b)
    (wt : Weights n c w a b) (pair : n=d*q) (nearby : |d-c| ≤ w) :
    -c < 2*(c*(a*d+b*q)-(a*c^2+b*n)) ∧
    2*(c*(a*d+b*q)-(a*c^2+b*n)) < 3*c := by
  obtain ⟨np,wp,wc,cap⟩ := cur
  have cp := wp.trans wc
  obtain ⟨_,bp,_,approx⟩ := wt
  let e := a*c^2-b*n
  let x := d-c
  change |e| *(2*w+1) ≤ c^2 at approx
  change |x| ≤ w at nearby
  have cc := sq_pos_of_pos cp
  have dp : c-w ≤ d := by
    have lo := (abs_le.mp nearby).1
    dsimp [x] at lo
    linarith
  have dpos : 0 < d := (sub_pos.mpr wc).trans_le dp
  have ex : 2*|e| *w < c^2 := by
    by_cases zero : |e|=0
    · simpa [zero] using cc
    · have : 0 < |e| := lt_of_le_of_ne (abs_nonneg e) (Ne.symm zero)
      linarith only [approx,this]
  have absErr : |2*e*x| < c^2 := by
    rw [abs_mul,abs_mul,abs_of_pos (by decide : (0:ℤ)<2)]
    exact (mul_le_mul_of_nonneg_left nearby (by positivity)).trans_lt ex
  have curv : b*n*x^2 ≤ d*c^2 := calc
    b*n*x^2 ≤ b*n*w^2 := mul_le_mul_of_nonneg_left
      (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) nearby 2)
      (mul_nonneg bp.le np)
    _ ≤ c^2*(c-w) := cap
    _ ≤ d*c^2 := by
      rw [mul_comm d]
      exact mul_le_mul_of_nonneg_left dp cc.le
  have cnon := mul_nonneg (mul_nonneg bp.le np) (sq_nonneg x)
  have id : c*d*(c*(a*d+b*q)-(a*c^2+b*n)) = e*x*d+b*n*x^2 := by
    dsimp [e,x]; rw [pair]; ring
  have low := mul_lt_mul_of_pos_right (abs_lt.mp absErr).1 dpos
  have high := mul_lt_mul_of_pos_right (abs_lt.mp absErr).2 dpos
  constructor <;> apply (mul_lt_mul_iff_of_pos_left (mul_pos cp dpos)).mp
  · linarith only [id,low,cnon]
  · linarith only [id,high,curv]

/-- Every odd factor pair in the chosen interval has precisely the same public trace. -/
theorem trace_eq_of_curvature {n c w a b d q : ℤ} (cur : Curvature n c w b)
    (wt : Weights n c w a b) (pair : n=d*q) (nearby : |d-c| ≤ w)
    (od : Odd d) (oq : Odd q) : a*d+b*q = traceRow n c a b := by
  obtain ⟨lo,hi⟩ := strip cur wt pair nearby
  obtain ⟨s,ds⟩ := od
  obtain ⟨v,qv⟩ := oq
  let t := a*s+b*v
  have id : a*d+b*q = a+b+2*t := by dsimp [t]; rw [ds,qv]; ring
  rw [id] at lo hi ⊢
  have pos : 0 < 4*c := by linarith only [cur.2.1,cur.2.2.1]
  let z := 2*(a*c^2+b*n)+3*c-1-2*c*(a+b)
  have upper : z < (t+1)*(4*c) := by dsimp [z]; linarith only [lo]
  have lower : t*(4*c) ≤ z := by dsimp [z]; linarith only [hi]
  have tz : z/(4*c)=t := by
    have h1 := (Int.le_ediv_iff_mul_le pos).mpr lower
    have h2 := (Int.ediv_lt_iff_lt_mul pos).mpr upper
    omega
  exact congrArg (fun h => a+b+2*h) tz.symm

theorem trace_eq {n c w a b d q : ℤ} (win : Window n c w)
    (wt : Weights n c w a b) (pair : n=d*q) (nearby : |d-c| ≤ w)
    (od : Odd d) (oq : Odd q) : a*d+b*q = traceRow n c a b :=
  trace_eq_of_curvature (curvature_of_window win wt) wt pair nearby od oq

/-- A single exact-square test gives at most two possible divisor values.
A caller may verify the product or reject nonintegral quadratic roots. -/
def candidates (n c a b : ℤ) : List ℤ :=
  let t := traceRow n c a b
  let D := t^2-4*a*b*n
  let g : ℤ := D.toNat.sqrt
  if g^2=D then [(t-g)/(2*a),(t+g)/(2*a)] else []

theorem candidates_length (n c a b : ℤ) : (candidates n c a b).length ≤ 2 := by
  simp only [candidates]
  split <;> simp

theorem candidate_mem_of_curvature {n c w a b d q : ℤ} (cur : Curvature n c w b)
    (wt : Weights n c w a b) (pair : n=d*q) (nearby : |d-c| ≤ w)
    (od : Odd d) (oq : Odd q) : d ∈ candidates n c a b := by
  have row := trace_eq_of_curvature cur wt pair nearby od oq
  let g := a*d-b*q
  have sq : (traceRow n c a b)^2-4*a*b*n=g^2 := by dsimp [g]; rw [←row,pair]; ring
  have eqNat : (g^2).toNat = g.natAbs^2 := by
    apply Int.ofNat_inj.mp
    rw [Int.toNat_of_nonneg (sq_nonneg g),Nat.cast_pow,Int.natCast_natAbs,sq_abs]
  unfold candidates
  simp only [sq,eqNat,Nat.sqrt_eq',Int.natCast_natAbs,sq_abs,if_true,List.mem_cons,
    List.not_mem_nil,or_false]
  have ap : 2*a ≠ 0 := by linarith only [wt.1]
  rw [←row]
  rcases le_total g 0 with h|h
  · left
    rw [abs_of_nonpos h,show a*d+b*q - -g = d*(2*a) by dsimp [g]; ring,Int.mul_ediv_cancel _ ap]
  · right
    rw [abs_of_nonneg h,show a*d+b*q+g = d*(2*a) by dsimp [g]; ring,Int.mul_ediv_cancel _ ap]

theorem candidate_mem {n c w a b d q : ℤ} (win : Window n c w)
    (wt : Weights n c w a b) (pair : n=d*q) (nearby : |d-c| ≤ w)
    (od : Odd d) (oq : Odd q) : d ∈ candidates n c a b :=
  candidate_mem_of_curvature (curvature_of_window win wt) wt pair nearby od oq

/-- A checkable empty candidate list excludes every natural divisor in the public window. -/
theorem excludes {n c w a b : ℕ} (win : Window n c w) (wt : Weights n c w a b)
    (odd : n%2=1) (empty : candidates n c a b=[]) (d : ℕ)
    (lo : c≤d+w) (hi : d≤c+w) : ¬d∣n := by
  rintro ⟨q,pair⟩
  have op : Odd (d*q) := by rw [←pair]; exact Nat.odd_iff.mpr odd
  obtain ⟨od,oq⟩ := Nat.odd_mul.mp op
  have dz : Odd (d:ℤ) := by exact_mod_cast od
  have qz : Odd (q:ℤ) := by exact_mod_cast oq
  have h := candidate_mem win wt (by exact_mod_cast pair) (d:=(d:ℤ)) (q:=(q:ℤ))
    (abs_le.mpr (by omega)) dz qz
  simp [empty] at h

/-- With equal 1024-bit factors the admissible interval for the smaller factor
is bounded below both by its bit length and by √(N/2). -/
def feasibleLower (n : ℕ) : ℕ := max (2^1023) (((n-1)/2).sqrt+1)

/-- Each address has a publicly computed center, clamped to the feasible interval. -/
def center (n : ℕ) (i : Fin (2^682)) : ℕ :=
  min n.sqrt (max (feasibleLower n) (2^1023 + i.val*2^341 + 2^340))

private theorem feasible {p q n : ℕ} (pair : n=p*q) (large : 2^1023≤p)
    (ord : p≤q) (small : q<2^1024) :
    feasibleLower n ≤ p ∧ p ≤ n.sqrt ∧ n ≤ 2*(feasibleLower n)^2 := by
  have pp : p^2 ≤ n := by rw [pair,pow_two]; exact Nat.mul_le_mul_left p ord
  have up : q ≤ 2*p := by
    have eq : 2^1024 = 2*(2^1023:ℕ) := by decide
    omega
  have bound : n ≤ 2*p^2 := by
    rw [pair]; calc
      p*q ≤ p*(2*p) := Nat.mul_le_mul_left _ up
      _ = 2*p^2 := by ring
  have pos : 0<n := by have := Nat.pow_pos (by omega : 0<p) (n:=2); omega
  let t := (n-1)/2
  have tp : t < p^2 := by dsimp [t]; omega
  have under : t.sqrt+1≤p := Nat.sqrt_lt'.mpr tp
  have next := Nat.lt_succ_sqrt' t
  have hu : t.sqrt+1≤feasibleLower n := Nat.le_max_right _ _
  have next' := next.trans_le (Nat.pow_le_pow_left hu 2)
  change (n-1)/2 < (feasibleLower n)^2 at next'
  exact ⟨max_le large under,Nat.le_sqrt'.mpr pp,by omega⟩

/-- Every address, including a clamped one, satisfies the hypotheses for the
same public radius of 2^340. -/
theorem center_window {p q n : ℕ} (pair : n=p*q) (large : 2^1023≤p)
    (ord : p≤q) (small : q<2^1024) (i : Fin (2^682)) :
    Window n (center n i) (2^340) := by
  obtain ⟨lower,upper,ratio⟩ := feasible pair large ord small
  have h : feasibleLower n ≤ center n i :=
    le_min (lower.trans upper) (le_max_left _ _)
  have endpt : center n i ≤ n.sqrt := min_le_left _ _
  have cBig : 2^1023 ≤ center n i := (le_max_left _ _).trans h
  have cs := (Nat.pow_le_pow_left endpt 2).trans (Nat.sqrt_le' n)
  have ns := ratio.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h 2))
  have cz : (2:ℤ)^1023 ≤ center n i := by exact_mod_cast cBig
  have gap : 4*((2:ℤ)^340)^3+2^340 < 2^1023 := by decide
  exact ⟨by decide,by omega,by exact_mod_cast cs,by exact_mod_cast ns,by omega⟩

/-- The equal-width interval has 2^682 bins of 2^341 consecutive integers.
Clamping the midpoint preserves coverage of the actual smaller factor. -/
theorem address_covers {p q n : ℕ} (pair : n=p*q) (large : 2^1023≤p)
    (ord : p≤q) (small : q<2^1024) :
    ∃ i : Fin (2^682), |(p:ℤ)-center n i| ≤ 2^340 := by
  obtain ⟨lower,upper,_⟩ := feasible pair large ord small
  let i := (p-2^1023)/2^341
  have bound : i < 2^682 := by
    apply (Nat.div_lt_iff_lt_mul (show 0<2^341 by decide)).mpr
    have eq : 2^682*2^341 = (2^1023:ℕ) := by decide
    rw [eq]; omega
  let addr : Fin (2^682) := ⟨i,bound⟩
  refine ⟨addr,abs_le.mpr ?_⟩
  have div := Nat.mod_add_div (p-2^1023) (2^341)
  have remm := Nat.mod_lt (p-2^1023) (show 0<2^341 by decide)
  let raw := 2^1023+i*2^341+2^340
  have step : 2^341=2*(2^340:ℕ) := by decide
  have mul : 2^341*((p-2^1023)/2^341) = i*2^341 := Nat.mul_comm _ _
  rw [mul] at div
  have sl : p≤raw+2^340 := by dsimp [raw]; omega
  have sr : raw≤p+2^340 := by dsimp [raw]; omega
  change -(2:ℤ)^340 ≤ (p:ℤ)-(min n.sqrt (max (feasibleLower n) raw):ℕ) ∧
    (p:ℤ)-(min n.sqrt (max (feasibleLower n) raw):ℕ) ≤ 2^340
  omega

/-- Full coverage by product-only addresses. A single common pair of public weights
exists at each address. Any valid choice works for every odd divisor there. -/
theorem schedule {p q n : ℕ} (pair : n=p*q) (large : 2^1023≤p)
    (ord : p≤q) (small : q<2^1024) :
    (∀ i : Fin (2^682), ∃ a b : ℤ, Weights n (center n i) (2^340) a b) ∧
    ∃ i : Fin (2^682), ∀ a b : ℤ, Weights n (center n i) (2^340) a b →
      Odd p → Odd q → (p:ℤ) ∈ candidates n (center n i) a b := by
  obtain ⟨i,nearby⟩ := address_covers pair large ord small
  constructor
  · intro j
    have win : Window n (center n j) ((2:ℕ)^340) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using center_window pair large ord small j
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using weights_exist win
  · refine ⟨i,?_⟩
    intro a b wt od oq
    apply candidate_mem (center_window pair large ord small i) wt (q:=(q:ℤ))
      (by exact_mod_cast pair) nearby <;> exact_mod_cast ‹_›

end PrimeFactors.ArbitraryDivisorWindow
