import PrimeFactors.ChebyshevPrimeSample
import PrimeFactors.UniformDivisorCount
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

/-! Population bounds allowing both multipliers and both labels to depend on the
product. The finite estimate assumes a bound on positive nonsingular solutions
at each four-tuple of multipliers and labels. -/
namespace PrimeFactors.WeightedMultiplierPopulation
open Finset

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

private abbrev X : ℕ := 2^1023

/-- A possible label among the first J positions of a progression of gap at most 24. -/
def Label (r J a : ℕ) (t : ℝ) : Prop :=
  0 ≤ (a : ℝ) - 2 * Real.sqrt r * t ∧ (a : ℝ) - 2 * Real.sqrt r * t < 24 * J

def difference (w : ℕ × ℕ) (a b : ℕ) : ℕ :=
  ((w.2 : ℤ) * (a : ℤ)^2 - (w.1 : ℤ) * (b : ℤ)^2).natAbs

private theorem sqrt_bounds {r R : ℕ} (hr : 0 < r) (cap : r ≤ R^2) :
    1 ≤ Real.sqrt r ∧ Real.sqrt r ≤ R := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    exact_mod_cast (show 1^2 ≤ r by omega)
  · apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity, by exact_mod_cast cap⟩

private theorem center_le {x R r : ℕ} {t : ℝ} (rp : 0 < r) (cap : r ≤ R^2)
    (ht : 0 ≤ t) (top : t ≤ 2 * x) : 2 * Real.sqrt r * t ≤ 4 * R * x := by
  have h := mul_le_mul (sqrt_bounds rp cap).2 top ht (by positivity)
  linarith

/-- A uniform upper endpoint for the first label. -/
theorem first_lt {r R x J a : ℕ} {t : ℝ} (rp : 0 < r) (cap : r ≤ R^2)
    (small : 24*J ≤ R*x) (ht : 0 ≤ t) (top : t ≤ 2 * x) (label : Label r J a t) :
    a < 5*R*x := by
  have small' : (24:ℝ)*J ≤ R*x := by exact_mod_cast small
  have h := center_le rp cap ht top
  exact_mod_cast (show (a:ℝ) < 5*R*x by linarith only [label.2,h,small'])

/-- A fixed first label confines second labels even when they come from
different products (represented by two possibly different real square roots). -/
theorem second_lt {r s R J a b₁ b₂ : ℕ} {t₁ t₂ : ℝ}
    (rp : 0 < r) (sp : 0 < s) (rCap : r ≤ R^2) (sCap : s ≤ R^2) (jp : 0 < J)
    (a₁ : Label r J a t₁) (a₂ : Label r J a t₂)
    (b₁' : Label s J b₁ t₁) (b₂' : Label s J b₂ t₂) :
    b₁ < b₂ + 48*R*J := by
  obtain ⟨rlo,_⟩ := sqrt_bounds rp rCap
  obtain ⟨slo,shi⟩ := sqrt_bounds sp sCap
  have Jpos : (0:ℝ) < J := by exact_mod_cast jp
  have Rlo : (1:ℝ) ≤ R := slo.trans shi
  have spread : t₁ - t₂ < 12 * J := by
    by_cases h : t₂ ≤ t₁
    · nlinarith only [a₁.1,a₂.2,mul_nonneg (sub_nonneg.mpr rlo) (sub_nonneg.mpr h)]
    · linarith
  have step := mul_lt_mul_of_pos_left spread (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) slo)
  have bound := mul_le_mul_of_nonneg_right shi Jpos.le
  have slack := mul_le_mul_of_nonneg_right Rlo Jpos.le
  exact_mod_cast (show (b₁:ℝ) < (b₂:ℝ) + 48 * R * J by
    nlinarith only [b₁'.2,b₂'.1,step,bound,slack])

/-- The positive part of a weighted square expression has a uniform product-only cap. -/
theorem excess {r R x J a : ℕ} {t : ℝ} (rp : 0 < r) (cap : r ≤ R^2)
    (small : 24*J ≤ R*x) (ht : 0 ≤ t) (top : t ≤ 2*x) (label : Label r J a t) :
    0 ≤ (a:ℝ)^2 - 4*r*t^2 ∧ (a:ℝ)^2 - 4*r*t^2 < 216*R*x*J := by
  let u := 2 * Real.sqrt r * t
  have u0 : 0 ≤ u := by dsimp [u]; positivity
  have uc : u ≤ 4*R*x := center_le rp cap ht top
  have hA : (a:ℝ) < 5*R*x := by exact_mod_cast first_lt rp cap small ht top label
  have plus : (a:ℝ) + u ≤ 9*R*x := by linarith
  have minus : 0 ≤ (a:ℝ)-u ∧ (a:ℝ)-u < 24*J := label
  have sumPos := (add_nonneg (by positivity : 0 ≤ (a:ℝ)) u0).lt_or_eq
  have eq : (a:ℝ)^2 - 4*r*t^2 = (a-u)*(a+u) := by
    dsimp [u]
    linear_combination 4*t^2*Real.sq_sqrt (by positivity : 0≤(r:ℝ))
  rw [eq]
  refine ⟨mul_nonneg minus.1 (add_nonneg (by positivity) u0),?_⟩
  have jp : (0:ℝ)<J := by linarith only [minus.1,minus.2]
  rcases sumPos with pos | zero
  · have m := mul_lt_mul_of_pos_right minus.2 pos
    have cap' := mul_le_mul_of_nonneg_left plus (by positivity : (0:ℝ) ≤ 24*J)
    nlinarith only [m,cap']
  · rw [←zero,mul_zero]
    have prodPos : (0:ℝ)<(R:ℝ)*x := by linarith only [uc,u0,hA,show 0≤(a:ℝ) by positivity]
    nlinarith only [mul_pos prodPos jp]

private theorem weighted_excess_upper {K R x J : ℕ} (z : ℕ) (pos : 0 < z) (le : z ≤ K) (y : ℝ) (hy : y < 216*R*x*J) :
      z*y < 256*K*R*x*J := by
  have h := mul_lt_mul_of_pos_left hy (by exact_mod_cast pos : (0:ℝ)<z)
  have zK : (z:ℝ) ≤ K := by exact_mod_cast le
  have hK := mul_le_mul_of_nonneg_right zK (by positivity : (0:ℝ) ≤ 216*R*x*J)
  have extra : (0:ℝ) ≤ (K:ℝ)*R*x*J := by positivity
  nlinarith only [h,hK,extra]

/-- The absolute norm constant stays small even when the two multipliers are
selected after seeing the product. -/
theorem difference_lt {r s K R x J a b : ℕ} {t : ℝ}
    (rp : 0 < r) (sp : 0 < s) (rK : r ≤ K) (sK : s ≤ K) (cap : K ≤ R^2)
    (small : 24*J ≤ R*x) (ht : 0 ≤ t) (top : t ≤ 2*x)
    (first : Label r J a t) (second : Label s J b t) :
    difference (r,s) a b < 256*K*R*x*J := by
  obtain ⟨d0,d⟩ := excess rp (rK.trans cap) small ht top first
  obtain ⟨e0,e⟩ := excess sp (sK.trans cap) small ht top second
  have plus := weighted_excess_upper s sp sK _ d
  have minus := weighted_excess_upper r rp rK _ e
  have h : |(s:ℝ)*(a:ℝ)^2-(r:ℝ)*(b:ℝ)^2| < 256*K*R*x*J := by
    rw [abs_lt]
    constructor
    · nlinarith only [minus, mul_nonneg (by positivity : 0≤(s:ℝ)) d0]
    · nlinarith only [plus, mul_nonneg (by positivity : 0≤(r:ℝ)) e0]
  apply (Nat.cast_lt (α := ℝ)).mp
  simpa [difference, Int.cast_natAbs, Int.cast_abs] using h

/-- For the two genuine excesses D and E, the first positive Pell coordinate
is s*D+r*E. Dividing it by a positive gcd only decreases this bound. -/
theorem first_coordinate_lt {r s K R x J a f n D E : ℕ} {t : ℝ}
    (rp : 0 < r) (sp : 0 < s) (rK : r ≤ K) (sK : s ≤ K) (cap : K ≤ R^2)
    (small : 24*J ≤ R*x) (ht : 0 ≤ t) (top : t ≤ 2*x)
    (first : Label r J a t) (second : Label s J f t)
    (product : t^2=(n:ℝ)) (deq : a^2=D+4*r*n) (eeq : f^2=E+4*s*n) :
    s*D+r*E < 512*K*R*x*J := by
  have d := (excess rp (rK.trans cap) small ht top first).2
  have e := (excess sp (sK.trans cap) small ht top second).2
  rw [product] at d e
  have deq' : (a:ℝ)^2 = (D:ℝ) + 4*r*n := by exact_mod_cast deq
  have eeq' : (f:ℝ)^2 = (E:ℝ) + 4*s*n := by exact_mod_cast eeq
  have posD := weighted_excess_upper (R:=R) (x:=x) (J:=J) s sp sK (D:ℝ) (by linarith only [d,deq'])
  have posE := weighted_excess_upper (R:=R) (x:=x) (J:=J) r rp rK (E:ℝ) (by linarith only [e,eeq'])
  exact_mod_cast (show (s:ℝ)*D+(r:ℝ)*E < 512*K*R*x*J by linarith only [posD,posE])

/-- A positive-norm solution has positive embedding at most twice its first
coordinate. Taking U=512KRXJ gives the separate 1024KRXJ height estimate. -/
theorem embedding_lt {a y t c U : ℝ} (norm : a^2 = t*y^2+c^2)
    (ap : 0≤a) (yp : 0≤y) (tp : 0≤t) (size : a<U) :
    a+Real.sqrt t*y < 2*U := by
  have sq : (Real.sqrt t*y)^2 ≤ a^2 := by
    rw [mul_pow,Real.sq_sqrt tp,norm]
    linarith only [sq_nonneg c]
  have root := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg t) yp) ap).mp sq
  linarith

private abbrev coefficient : ℕ := 197*4096*21000000

/-- Bit cost of the common divisor cap, including the finite counting constants.
The ceiling is taken after scaling both quantities to the 336th power. -/
def loss (k b : ℕ) : ℕ := (14766+14882+64*(1031+k+k/2+b)+335)/336

def saving (k b : ℕ) : ℕ := 1023-(2*k+k/2+b+loss k b)

theorem reported_savings : saving 4 0 = 727 ∧ saving 16 16 = 674 ∧
    saving 64 64 = 483 ∧ saving 128 128 = 229 ∧
    saving 160 64 = 216 ∧ saving 64 256 = 255 := by decide +kernel

private def cap (k b : ℕ) : ℕ := 2^(loss k b)/coefficient

set_option exponentiation.threshold 20000 in
private theorem divisor_cap {k b c : ℕ} (pos : 0<c)
    (bound : c<256*2^k*2^(k/2)*X*2^b) : (c^2).divisors.card ≤ cap k b := by
  have size : c < 2^(1031+k+k/2+b) := by
    convert bound using 1
    rw [show 1031+k+k/2+b = 8+k+k/2+1023+b by omega]
    simp only [pow_add]
    rfl
  have sq : c^2 < 2^(2*(1031+k+k/2+b)) := by
    rw [Nat.mul_comm 2 _,pow_mul]
    exact Nat.pow_lt_pow_left size (by decide)
  have hb := UniformDivisorCount.below_power_two (pow_pos pos 2) sq
  have hc : coefficient^336 ≤ 2^14766 := by decide +kernel
  have budget : 14766+(14882+32*(2*(1031+k+k/2+b))) ≤ loss k b * 336 := by
    unfold loss
    omega
  have root : (coefficient*(c^2).divisors.card)^336 < (2^(loss k b))^336 := by
    rw [mul_pow,←pow_mul]
    calc
      _ ≤ 2^14766 * (c^2).divisors.card^336 := Nat.mul_le_mul_right _ hc
      _ < 2^14766 * 2^(14882+32*(2*(1031+k+k/2+b))) :=
        Nat.mul_lt_mul_of_pos_left hb (by positivity)
      _ ≤ _ := by rw [←pow_add]; exact Nat.pow_le_pow_right (by decide) budget
  apply (Nat.le_div_iff_mul_le (by decide : 0<coefficient)).mpr
  simpa only [Nat.mul_comm] using
    ((Nat.pow_lt_pow_iff_left (by decide : 336≠0)).mp root).le

private theorem sum_bound {α : Type*} {s : Finset α} {f : α→ℕ} {n m : ℕ}
    (size : s.card ≤ n) (each : ∀ i∈s, f i ≤ m) : ∑ i∈s, f i ≤ n*m := calc
  _ ≤ ∑ _i∈s, m := Finset.sum_le_sum each
  _ = s.card*m := by simp
  _ ≤ _ := Nat.mul_le_mul_right _ size

private theorem weights_card {w : Finset (ℕ×ℕ)} {K : ℕ}
    (inside : ∀ i ∈ w, 0 < i.1 ∧ i.1 ≤ K ∧ 0 < i.2 ∧ i.2 ≤ K) : w.card ≤ K^2 := by
  have sub : w ⊆ Icc 1 K ×ˢ Icc 1 K := by
    intro i hi
    obtain ⟨r,rs,s,ss⟩ := inside i hi
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨r,rs⟩,mem_Icc.mpr ⟨s,ss⟩⟩
  simpa [Nat.card_Icc,pow_two] using Finset.card_le_card sub

/-- Counting the first and second labels for the same pair of multipliers
saves an entire factor R. The density in the second label is inversely
proportional to the square root of the first multiplier. -/
theorem trace_pairs {r s R x J : ℕ} (rp : 0 < r) (sp : 0 < s)
    (rCap : r ≤ R^2) (sCap : s ≤ R^2) (jp : 0 < J) (short : 64*(24*J+1) ≤ x)
    (as : Finset ℕ) (bs : ℕ → Finset ℕ)
    (first : ∀ a∈as, ∃ t:ℝ, 0≤t ∧ t≤2*x ∧ Label r J a t)
    (pair : ∀ a∈as, ∀ f∈bs a, ∃ t:ℝ, Label r J a t ∧ Label s J f t) :
    ∑ a∈as, (bs a).card ≤ 197*R*x*J := by
  classical
  rcases as.eq_empty_or_nonempty with empty | nonempty
  · simp [empty]
  let u := Real.sqrt r
  let v := Real.sqrt s
  obtain ⟨ulo,uhi⟩ := sqrt_bounds rp rCap
  obtain ⟨vlo,vhi⟩ := sqrt_bounds sp sCap
  have up : 0 < u := by dsimp [u]; linarith only [ulo]
  have vp : 0 < v := by dsimp [v]; linarith only [vlo]
  have J1 : (1:ℝ) ≤ J := by exact_mod_cast jp
  have short' : (64:ℝ)*(24*J+1) ≤ x := by exact_mod_cast short
  have ac : (64:ℝ)*as.card ≤ 257*u*x := by
    let a := as.max' nonempty
    have sub : as ⊆ range (a+1) := by
      intro i hi
      exact mem_range.mpr (Nat.lt_succ_of_le (as.le_max' i hi))
    have small : as.card ≤ a+1 := by simpa using Finset.card_le_card sub
    have small' : (as.card:ℝ) ≤ a+1 := by exact_mod_cast small
    obtain ⟨t,_,bound,lab⟩ := first a (as.max'_mem nonempty)
    have prod := mul_le_mul_of_nonneg_left bound up.le
    have xu := mul_le_mul_of_nonneg_right ulo (by positivity : 0≤(x:ℝ))
    have err : (a:ℝ)-2*u*t<24*J := lab.2
    nlinarith only [small',err,short',prod,xu]
  obtain ⟨a,ha,largest⟩ := as.exists_max_image (fun i => (bs i).card) nonempty
  have count : ∑ i∈as, (bs i).card ≤ as.card * (bs a).card := sum_bound le_rfl largest
  rcases (bs a).eq_empty_or_nonempty with empty | occupied
  · simp only [empty,card_empty,Nat.mul_zero] at count
    exact count.trans (Nat.zero_le _)
  let low := (bs a).min' occupied
  let high := (bs a).max' occupied
  have sub : bs a ⊆ Icc low high := by
    intro f hf
    exact mem_Icc.mpr ⟨(bs a).min'_le f hf, (bs a).le_max' f hf⟩
  have bcount : (bs a).card + low ≤ high + 1 := by
    have le := Finset.card_le_card sub
    rw [Nat.card_Icc] at le
    have lh : low ≤ high := (bs a).le_max' low ((bs a).min'_mem occupied)
    omega
  obtain ⟨t₁,ah,bh⟩ := pair a ha high ((bs a).max'_mem occupied)
  obtain ⟨t₂,al,bl⟩ := pair a ha low ((bs a).min'_mem occupied)
  have rangeA : u*(t₁-t₂) ≤ 12*J := by
    dsimp [u]
    linarith only [ah.1,al.2]
  have rangeB : (high:ℝ)-low ≤ 2*v*(t₁-t₂) + 24*J := by
    dsimp [v]
    linarith only [bh.2,bl.1]
  have combined : u*((high:ℝ)-low) ≤ 24*(u+v)*J := by
    nlinarith only [mul_le_mul_of_nonneg_left rangeA vp.le,
      mul_le_mul_of_nonneg_left rangeB up.le]
  have bc : u*((bs a).card:ℝ) ≤ 49*R*J := by
    have card' : ((bs a).card:ℝ) + low ≤ high+1 := by exact_mod_cast bcount
    have uh : u ≤ R := uhi
    have vh : v ≤ R := vhi
    have uj : u ≤ u*J := by nlinarith only [mul_le_mul_of_nonneg_left J1 up.le]
    nlinarith only [combined,mul_le_mul_of_nonneg_left card' up.le,
      mul_le_mul_of_nonneg_right uh (le_trans (by norm_num) J1),
      mul_le_mul_of_nonneg_right vh (le_trans (by norm_num) J1),uj]
  have rect : as.card * (bs a).card ≤ 197*R*x*J := by
    apply (Nat.cast_le (α:=ℝ)).mp
    push_cast
    have positive : 0≤(R:ℝ)*x*J := by positivity
    nlinarith only [mul_le_mul_of_nonneg_right ac (by positivity : 0≤((bs a).card:ℝ)),
      mul_le_mul_of_nonneg_right bc (by positivity : 0≤(x:ℝ)),positive]
  exact count.trans rect

/-- A bound for arbitrary finite sets of weights and traces, allowing the
hits to select any of them after seeing the product. Each positive norm
constant uses the Pell count supplied in the final hypothesis. -/
theorem population {k b hits : ℕ} (even : 2*(k/2)=k)
    (room : 2*k+k/2+b+loss k b ≤ 1023)
    (short : 64*(24*2^b+1) ≤ X)
    (ws : Finset (ℕ×ℕ)) (as : ℕ×ℕ → Finset ℕ) (bs : ℕ×ℕ → ℕ → Finset ℕ)
    (weights : ∀ w∈ws, 0<w.1 ∧ w.1≤2^k ∧ 0<w.2 ∧ w.2≤2^k)
    (first : ∀ w∈ws, ∀ a∈as w, ∃ t:ℝ, 0≤t ∧ t≤2*X ∧ Label w.1 (2^b) a t)
    (pairs : ∀ w∈ws, ∀ a∈as w, ∀ f∈bs w a, ∃ t:ℝ, 0≤t ∧ t≤2*X ∧
        Label w.1 (2^b) a t ∧ Label w.2 (2^b) f t)
    (nonsingular : ∀ w∈ws, ∀ a∈as w, ∀ f∈bs w a, 0 < difference w a f)
    (count : hits ≤ ∑ w∈ws, ∑ a∈as w, ∑ f∈bs w a, 4096*((difference w a f)^2).divisors.card) :
    2^(saving k b)*hits < MixedPrefixSample.eligible.card := by
  let K := (2:ℕ)^k
  let R := (2:ℕ)^(k/2)
  let J := (2:ℕ)^b
  have capR : K ≤ R^2 := by
    dsimp [K,R]
    rw [←pow_mul,Nat.mul_comm (k/2),even]
  have labels_fit : 24*J ≤ R*X :=
    (show 24*J ≤ X by dsimp [J]; omega).trans
      (Nat.le_mul_of_pos_left _ (by dsimp [R]; positivity))
  have rows : hits ≤ K^2*((197*R*X*J)*(4096*cap k b)) := by
    apply count.trans
    apply sum_bound (weights_card weights)
    intro w hw
    obtain ⟨rp,rK,sp,sK⟩ := weights w hw
    have cnt := trace_pairs rp sp (rK.trans capR) (sK.trans capR)
      (by positivity : 0 < (2:ℕ)^b) short (as w) (bs w) (first w hw) (by
        intro a ha f hf
        obtain ⟨t,_,_,al,bl⟩ := pairs w hw a ha f hf
        exact ⟨t,al,bl⟩)
    calc
      _ ≤ ∑ a∈as w, (bs w a).card*(4096*cap k b) := by
        apply sum_le_sum
        intro a ha
        apply sum_bound le_rfl
        intro f hf
        obtain ⟨t,ht,top,al,bl⟩ := pairs w hw a ha f hf
        exact Nat.mul_le_mul_left _ (divisor_cap (nonsingular w hw a ha f hf)
          (difference_lt rp sp rK sK capR labels_fit ht top al bl))
      _ = (∑ a∈as w,(bs w a).card)*(4096*cap k b) := (Finset.sum_mul ..).symm
      _ ≤ _ := Nat.mul_le_mul_right _ cnt
  have lim : cap k b * coefficient ≤ 2^(loss k b) := Nat.div_mul_le_self ..
  have exponent : saving k b + k*2 + k/2 + 1023 + b + loss k b = 2046 := by
    unfold saving
    omega
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  apply lt_of_le_of_lt _ ChebyshevPrimeSample.eligible_count
  calc
    _ ≤ 21000000*(2^(saving k b)*(K^2*((197*R*X*J)*(4096*cap k b)))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ rows)
    _ = (2^(saving k b)*K^2*R*X*J)*(cap k b*coefficient) := by
      unfold coefficient
      ac_rfl
    _ ≤ (2^(saving k b)*K^2*R*X*J)*2^(loss k b) := Nat.mul_le_mul_left _ lim
    _ = _ := by
      change (2^(saving k b)*(2^k)^2*2^(k/2)*2^1023*2^b)*2^(loss k b)=(2:ℕ)^2046
      rw [←pow_mul,←pow_add,←pow_add,←pow_add,←pow_add,←pow_add,exponent]

/-- The numerical hypotheses of the population bound hold in every listed case. -/
theorem reported_budgets {k b : ℕ}
    (row : (k,b) ∈ [(4,0),(16,16),(64,64),(128,128),(160,64),(64,256)]) :
    2*(k/2)=k ∧ 2*k+k/2+b+loss k b≤1023 ∧ 64*(24*2^b+1)≤X := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ <;> decide +kernel

/-- The first coordinate is below the 2048-bit cutoff used for counting
normalized Pell representatives in every row of the table. -/
theorem reported_height {k b : ℕ}
    (row : (k,b) ∈ [(4,0),(16,16),(64,64),(128,128),(160,64),(64,256)]) :
    512*2^k*2^(k/2)*X*2^b < 2^2048 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ <;> decide +kernel

end PrimeFactors.WeightedMultiplierPopulation
