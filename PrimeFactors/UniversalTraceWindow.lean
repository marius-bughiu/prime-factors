import PrimeFactors.ArbitraryDivisorWindow
import PrimeFactors.WeightedStride

namespace PrimeFactors.UniversalTraceWindow

set_option maxRecDepth 16000
set_option exponentiation.threshold 2048

/-- An interval on which the stationary approximation can cover a whole trace period. -/
def Window (n c w : ℤ) : Prop :=
  6 ≤ w ∧ w < c ∧ c^2 ≤ n ∧ n ≤ 2*c^2 ∧ w^3 ≤ 3*(c-w)

/-- The index-12 lattice fixes the trace residue for every possible factor
coprime to six. The approximation error is checked independently of construction. -/
def Weights (n c w a b : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ b ≤ 2*w ∧ (12:ℤ) ∣ a+b*n ∧
    |a*c^2-b*n| *(2*w+1) ≤ 12*c^2

/-- Approximate (N/c² + (N mod 12))/12 and lift the numerator back to A. -/
theorem weights_exist {n c w : ℕ} (win : Window n c w) :
    ∃ a b : ℤ, Weights n c w a b := by
  obtain ⟨wlo,wc,cn,_,_⟩ := win
  let h := (n:ℤ)%12
  have cp : (0:ℤ)<c := by omega
  have cc := sq_pos_of_pos cp
  have den : 0 < 12*c^2 := Nat.mul_pos (by decide) (by exact_mod_cast cc)
  obtain ⟨b,blo,bhi,j,gap⟩ := boundedSlope_exists (12*c^2) (2*w)
    ((n:ℤ)+h*(c:ℤ)^2) den (by omega)
  let a := 12*j-(b:ℤ)*h
  push_cast at gap
  have sign : (b:ℤ)*(n+h*(c:ℤ)^2) - 12*(c:ℤ)^2*j = -(a*c^2-b*n) := by dsimp [a]; ring
  rw [sign,abs_neg] at gap
  have bz : (1:ℤ)≤b := by exact_mod_cast blo
  have ap : 0<a := by
    apply lt_of_not_ge
    intro non
    have bn := mul_le_mul_of_nonneg_right bz (cc.le.trans cn)
    have ac := mul_nonpos_of_nonpos_of_nonneg non cc.le
    have lb : (c:ℤ)^2 ≤ |a*c^2-b*n| := by linarith only [bn,cn,ac,neg_le_abs (a*c^2-b*n)]
    have more := mul_le_mul_of_nonneg_right lb (show 0 ≤ 2*(w:ℤ)+1 by omega)
    have excess := mul_pos cc (show (0:ℤ)<2*w+1-12 by omega)
    linarith only [gap,more,excess]
  have hw : (n:ℤ)-h = 12*((n:ℤ)/12) := by dsimp [h]; omega
  refine ⟨a,b,ap,by omega,by exact_mod_cast bhi,⟨j+(b:ℤ)*((n:ℤ)/12),?_⟩,gap⟩
  dsimp [a]; linear_combination (b:ℤ)*hw

/-- Every factor coprime to six has the same weighted trace residue.
The coefficient weights may have a common divisor. -/
theorem trace_period {n a b : ℤ} {d q : ℕ} (pair : n=(d:ℤ)*q)
    (unit : d.Coprime 6) (cong : (12:ℤ)∣a+b*n) :
    (24:ℤ) ∣ (a*d+b*q)-(a+b*n) := by
  have odd := Nat.coprime_two_right.mp (unit.of_dvd_right (by decide : 2∣6))
  obtain ⟨v,dv⟩ : Odd (d:ℤ) := by exact_mod_cast odd
  obtain ⟨t,wt⟩ := cong
  have modNat := square_mod_twentyfour unit
  have modZ : (d:ℤ)^2 ≡ 1 [ZMOD 24] := by exact_mod_cast (Int.natCast_modEq_iff.mpr modNat)
  obtain ⟨j,hj⟩ := modZ.symm.dvd
  refine ⟨t*v-b*q*j,?_⟩
  calc
    _ = (a+b*n)*((d:ℤ)-1)-b*q*((d:ℤ)^2-1) := by rw [pair]; ring
    _ = _ := by rw [wt,hj,show (d:ℤ)-1=2*v by omega]; ring

/-- The sole candidate trace is the largest integer congruent to a+bN
strictly below (ac²+bN)/c + 18. -/
def traceRow (n c a b : ℤ) : ℤ :=
  let r := a+b*n
  r+24*((a*c^2+b*n+18*c-1-c*r)/(24*c))

/-- Actual weights can justify even wider intervals by a direct curvature check. -/
def Curvature (n c w b : ℤ) : Prop :=
  0 ≤ n ∧ 0 < w ∧ w < c ∧ b*n*w^2 ≤ 12*c^2*(c-w)

theorem curvature_of_window {n c w a b : ℤ} (win : Window n c w) (wt : Weights n c w a b) :
    Curvature n c w b := by
  obtain ⟨wp,wc,cn,up,cube⟩ := win
  have np := (sq_nonneg c).trans cn
  refine ⟨np,by omega,wc,?_⟩
  calc
    b*n*w^2 ≤ (2*w)*(2*c^2)*w^2 := mul_le_mul_of_nonneg_right
      (mul_le_mul wt.2.2.1 up np (by omega)) (sq_nonneg w)
    _ = 4*c^2*w^3 := by ring
    _ ≤ 12*c^2*(c-w) := by
      have h := mul_le_mul_of_nonneg_left cube (show 0 ≤ 4*c^2 by positivity)
      linarith only [h]

private theorem strip {n c w a b d q : ℤ} (cur : Curvature n c w b)
    (wt : Weights n c w a b) (pair : n=d*q) (nearby : |d-c| ≤ w) :
    -6*c < c*(a*d+b*q)-(a*c^2+b*n) ∧ c*(a*d+b*q)-(a*c^2+b*n) < 18*c := by
  obtain ⟨np,wp,wc,cap⟩ := cur
  obtain ⟨_,bp,_,_,approx⟩ := wt
  have cc := sq_pos_of_pos (wp.trans wc)
  let e := a*c^2-b*n
  let x := d-c
  change |e| *(2*w+1) ≤ 12*c^2 at approx
  change |x| ≤ w at nearby
  have cd : c-w ≤ d := by have := (abs_le.mp nearby).1; dsimp [x] at this; linarith
  have dp := (sub_pos.mpr wc).trans_le cd
  have ex : |e| *w < 6*c^2 := by
    by_cases zero : |e|=0
    · rw [zero,zero_mul]; positivity
    · have := lt_of_le_of_ne (abs_nonneg e) (Ne.symm zero)
      linarith
  have absErr : |e*x| < 6*c^2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left nearby (abs_nonneg e)).trans_lt ex
  have curv : b*n*x^2 ≤ 12*c^2*d := calc
    b*n*x^2 ≤ b*n*w^2 := mul_le_mul_of_nonneg_left
      (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) nearby 2)
      (mul_nonneg bp.le np)
    _ ≤ 12*c^2*(c-w) := cap
    _ ≤ 12*c^2*d := mul_le_mul_of_nonneg_left cd (by positivity)
  have cnon := mul_nonneg (mul_nonneg bp.le np) (sq_nonneg x)
  have id : c*d*(c*(a*d+b*q)-(a*c^2+b*n)) = e*x*d+b*n*x^2 := by
    dsimp [e,x]; rw [pair]; ring
  have low := mul_lt_mul_of_pos_right (abs_lt.mp absErr).1 dp
  have high := mul_lt_mul_of_pos_right (abs_lt.mp absErr).2 dp
  constructor <;> apply (mul_lt_mul_iff_of_pos_left (mul_pos (wp.trans wc) dp)).mp
  · linarith only [id,low,cnon]
  · linarith only [id,high,curv]

/-- All factor values in the interval and coprime to six select this single public row. -/
theorem trace_eq_of_curvature {n c w a b : ℤ} {d q : ℕ} (cur : Curvature n c w b)
    (wt : Weights n c w a b) (pair : n=(d:ℤ)*q) (nearby : |(d:ℤ)-c| ≤ w)
    (unit : d.Coprime 6) : a*d+b*q = traceRow n c a b := by
  obtain ⟨lo,hi⟩ := strip cur wt pair nearby
  obtain ⟨t,ht⟩ := trace_period pair unit wt.2.2.2.1
  have id : a*d+b*q=a+b*n+24*t := by linarith only [ht]
  rw [id] at lo hi ⊢
  have pos : 0<24*c := by linarith only [cur.2.1,cur.2.2.1]
  let z := a*c^2+b*n+18*c-1-c*(a+b*n)
  have upper : z<(t+1)*(24*c) := by dsimp [z]; linarith only [lo]
  have lower : t*(24*c)≤z := by dsimp [z]; linarith only [hi]
  have quot : z/(24*c)=t := by
    have := (Int.le_ediv_iff_mul_le pos).mpr lower
    have := (Int.ediv_lt_iff_lt_mul pos).mpr upper
    omega
  exact congrArg (fun h => a+b*n+24*h) quot.symm

/-- The square test charges up to two integer root guesses. Divisibility
and membership of the requested interval can be checked on each guess. -/
def candidates (n c a b : ℤ) : List ℤ :=
  let t := traceRow n c a b
  let D := t^2-4*a*b*n
  let g : ℤ := D.toNat.sqrt
  if g^2=D then [(t-g)/(2*a),(t+g)/(2*a)] else []

theorem candidates_length (n c a b : ℤ) : (candidates n c a b).length ≤ 2 := by
  simp only [candidates]
  split <;> simp

theorem candidate_mem {n c w a b : ℤ} {d q : ℕ} (win : Window n c w)
    (wt : Weights n c w a b) (pair : n=(d:ℤ)*q) (nearby : |(d:ℤ)-c| ≤ w)
    (unit : d.Coprime 6) : (d:ℤ) ∈ candidates n c a b := by
  have row := trace_eq_of_curvature (curvature_of_window win wt) wt pair nearby unit
  let g := a*d-b*q
  have sq : (traceRow n c a b)^2-4*a*b*n=g^2 := by dsimp [g]; rw [←row,pair]; ring
  have eqNat : (g^2).toNat = g.natAbs^2 := by
    apply Int.ofNat_inj.mp
    rw [Int.toNat_of_nonneg (sq_nonneg g),Nat.cast_pow,Int.natCast_natAbs,sq_abs]
  simp only [candidates,sq,eqNat,Nat.sqrt_eq',Int.natCast_natAbs,sq_abs,if_true,List.mem_cons,
    List.not_mem_nil,or_false]
  rw [←row]
  have ap : 2*a ≠ 0 := by linarith only [wt.1]
  rcases le_total g 0 with h|h
  · left
    rw [abs_of_nonpos h,show a*d+b*q - -g = d*(2*a) by dsimp [g]; ring,Int.mul_ediv_cancel _ ap]
  · right
    rw [abs_of_nonneg h,show a*d+b*q+g = d*(2*a) by dsimp [g]; ring,Int.mul_ediv_cancel _ ap]

/-- A single nonsquare certificate excludes every divisor in the stated natural
interval. The endpoints need only be contained in the certified window. -/
theorem excludes_of_modulus {n l u : ℕ} {c w a b t : ℤ} (m : ℕ)
    (cur : Curvature n c w b) (wt : Weights n c w a b) (unit : n.Coprime 6)
    (val : traceRow n c a b=t) (left : c-w ≤ (l:ℤ)) (right : (u:ℤ) ≤ c+w)
    (miss : ∀ x : ZMod m, x^2 ≠ (t:ZMod m)^2-4*a*b*n)
    (d : ℕ) (lo : l≤d) (hi : d≤u) : ¬d∣n := by
  intro div
  have du := unit.coprime_dvd_left div
  obtain ⟨q,prod⟩ := div
  have pair : (n:ℤ) = (d:ℤ)*q := by exact_mod_cast prod
  have near : |(d:ℤ)-c| ≤ w := abs_le.mpr (by omega)
  have row := trace_eq_of_curvature cur wt pair near du
  have sq : (a*(d:ℤ)-b*q)^2 = t^2-4*a*b*n := calc
    _ = (a*d+b*q)^2-4*a*b*((d:ℤ)*q) := by ring
    _ = _ := by rw [row,val,←pair]
  have modular := congrArg (fun z : ℤ => (z : ZMod m)) sq
  push_cast at modular
  exact miss _ modular

/-- A binary-friendly radius just below the uniform cube-root threshold. -/
def radius : ℕ := 23*2^337

/-- The ceiling of 2^1023 / (2*radius). The last bin is allowed to be short. -/
def addresses : ℕ := (2^685+22)/23

theorem exact_coverage_count :
    (addresses-1)*(2*radius) < 2^1023 ∧ 2^1023 ≤ addresses*(2*radius) ∧
    2^680 < addresses ∧ addresses < 2^681 := by decide

/-- Clamp a public bin midpoint to the balanced smaller-factor interval. -/
def center (n : ℕ) (i : Fin addresses) : ℕ :=
  min n.sqrt (max (ArbitraryDivisorWindow.feasibleLower n) (2^1023+i.val*(2*radius)+radius))

private theorem feasible {p q n : ℕ} (pair : n=p*q) (large : 2^1023≤p)
    (ord : p≤q) (small : q<2^1024) :
    ArbitraryDivisorWindow.feasibleLower n ≤ p ∧ p ≤ n.sqrt ∧
      n ≤ 2*(ArbitraryDivisorWindow.feasibleLower n)^2 := by
  have pp : p^2 ≤ n := by rw [pair,pow_two]; exact Nat.mul_le_mul_left p ord
  have qp : q ≤ 2*p := by omega
  have np : n ≤ 2*p^2 := by
    rw [pair]
    calc
      p*q ≤ p*(2*p) := Nat.mul_le_mul_left p qp
      _ = 2*p^2 := by ring
  have pos : 0<n := by have := Nat.pow_pos (by omega : 0<p) (n:=2); omega
  let t := (n-1)/2
  have tp : t < p^2 := by dsimp [t]; omega
  have under : t.sqrt+1≤p := Nat.sqrt_lt'.mpr tp
  have hu : t.sqrt+1≤ArbitraryDivisorWindow.feasibleLower n := Nat.le_max_right _ _
  have next := (Nat.lt_succ_sqrt' t).trans_le (Nat.pow_le_pow_left hu 2)
  change (n-1)/2 < (ArbitraryDivisorWindow.feasibleLower n)^2 at next
  exact ⟨max_le large under,Nat.le_sqrt'.mpr pp,by omega⟩

/-- Each address independently admits the same radius and period, including
bins clamped at either end of the feasible interval. -/
theorem center_window {p q n : ℕ} (pair : n=p*q) (large : 2^1023≤p)
    (ord : p≤q) (small : q<2^1024) (i : Fin addresses) :
    Window n (center n i) radius := by
  obtain ⟨lower,upper,ratio⟩ := feasible pair large ord small
  have h : ArbitraryDivisorWindow.feasibleLower n ≤ center n i :=
    le_min (lower.trans upper) (le_max_left _ _)
  have endpt : center n i ≤ n.sqrt := min_le_left _ _
  have cbig : 2^1023 ≤ center n i := (le_max_left _ _).trans h
  have cs := (Nat.pow_le_pow_left endpt 2).trans (Nat.sqrt_le' n)
  have ns := ratio.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h 2))
  have cz : (2:ℤ)^1023 ≤ center n i := by exact_mod_cast cbig
  have gap : (radius:ℤ)^3 ≤ 3*((2:ℤ)^1023-radius) := by decide
  exact ⟨by decide,lt_of_lt_of_le (by decide) cz,by exact_mod_cast cs,
    by exact_mod_cast ns,by linarith only [gap,cz]⟩

theorem address_covers {p q n : ℕ} (pair : n=p*q) (large : 2^1023≤p)
    (ord : p≤q) (small : q<2^1024) :
    ∃ i : Fin addresses, |(p:ℤ)-center n i| ≤ radius := by
  obtain ⟨lower,upper,_⟩ := feasible pair large ord small
  let k := (p-2^1023)/(2*radius)
  have width : 0<2*radius := by decide
  have bound : k < addresses := by
    apply (Nat.div_lt_iff_lt_mul width).mpr
    have cap := exact_coverage_count.2.1
    omega
  let addr : Fin addresses := ⟨k,bound⟩
  refine ⟨addr,abs_le.mpr ?_⟩
  have div := Nat.mod_add_div (p-2^1023) (2*radius)
  have remm := Nat.mod_lt (p-2^1023) width
  let raw := 2^1023+k*(2*radius)+radius
  have mul : (2*radius)*((p-2^1023)/(2*radius)) = k*(2*radius) := Nat.mul_comm _ _
  rw [mul] at div
  have sl : p≤raw+radius := by dsimp [raw]; omega
  have sr : raw≤p+radius := by dsimp [raw]; omega
  change -(radius:ℤ) ≤ (p:ℤ)-(min n.sqrt (max (ArbitraryDivisorWindow.feasibleLower n) raw):ℕ) ∧
    (p:ℤ)-(min n.sqrt (max (ArbitraryDivisorWindow.feasibleLower n) raw):ℕ) ≤ radius
  omega

/-- A complete public schedule for equal-width factors. Every valid weight
choice at the correct address yields the smaller factor among at most two guesses. -/
theorem schedule {p q n : ℕ} (pair : n=p*q) (large : 2^1023≤p)
    (ord : p≤q) (small : q<2^1024) (unit : p.Coprime 6) :
    (∀ i : Fin addresses, ∃ a b : ℤ, Weights n (center n i) radius a b) ∧
    ∃ i : Fin addresses, ∀ a b : ℤ, Weights n (center n i) radius a b →
      (p:ℤ) ∈ candidates n (center n i) a b := by
  obtain ⟨i,nearby⟩ := address_covers pair large ord small
  exact ⟨fun j => weights_exist (center_window pair large ord small j),i,
    fun _ _ wt => candidate_mem (center_window pair large ord small i) wt (q:=q)
      (by exact_mod_cast pair) nearby unit⟩

/-- A short interval beyond the former parity window, with one successful root. -/
theorem example_87097 :
    Window 87097 255 8 ∧ Weights 87097 255 8 7 5 ∧ traceRow 87097 255 7 5 = 3492 ∧
    candidates 87097 255 7 5 = [247,251] ∧ (251:ℕ)*347=87097 := by
  unfold Window Weights
  decide

end PrimeFactors.UniversalTraceWindow
