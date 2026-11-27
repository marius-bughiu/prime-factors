import PrimeFactors.ChebyshevPrimeSample
import Mathlib.Data.Real.Sqrt

/-! Count balanced prime pairs for which a single fixed factor-ratio prediction
approximates the true factor sum. The same real ratio must be used for all
pairs in the population. -/

namespace PrimeFactors.FixedRatioSumPopulation

open Finset MixedPrefixSample
set_option exponentiation.threshold 4096
set_option maxRecDepth 16384
attribute [local irreducible] X primes ordered eligible

/-- Error at most K for one fixed geometric coefficient confines q to a strip
about rp. The proof includes r=1, where the first derivative vanishes. -/
theorem strip_sq {p q r K H : ℝ} (pn : 0≤p) (order : p≤q) (height : q≤H)
    (ratio : r ∈ Set.Icc (1:ℝ) 2) (kn : 0≤K)
    (fit : |p+q-(Real.sqrt r+1/Real.sqrt r)*Real.sqrt (p*q)|≤K) :
    (q-r*p)^2≤16*H*K := by
  let x := Real.sqrt q
  let y := Real.sqrt p
  let w := Real.sqrt r
  let h := Real.sqrt H
  have qn := pn.trans order
  have hn := qn.trans height
  have rn : 0≤r := zero_le_one.trans ratio.1
  have xs : x^2=q := Real.sq_sqrt qn
  have ys : y^2=p := Real.sq_sqrt pn
  have ws : w^2=r := Real.sq_sqrt rn
  have hs : h^2=H := Real.sq_sqrt hn
  have yn : 0≤y := Real.sqrt_nonneg _
  have wn : 0≤w := Real.sqrt_nonneg _
  have xy : y≤x := Real.sqrt_le_sqrt order
  have xh : x≤h := Real.sqrt_le_sqrt height
  have w1 : 1≤w := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ratio.1
  have w15 : w≤3/2 := Real.sqrt_le_iff.mpr ⟨by norm_num,ratio.2.trans (by norm_num)⟩
  have wp : 0<w := zero_lt_one.trans_le w1
  have cancel : w*(y/w)=y := by field_simp
  have rhs : 0≤x-y/w := sub_nonneg.mpr ((div_le_self yn w1).trans xy)
  have both : |x-w*y|≤w*(x-y/w) := by
    rw [mul_sub,cancel]
    exact abs_le.mpr ⟨by nlinarith only [mul_nonneg (sub_nonneg.mpr xy) (by linarith : 0≤w+1)],
      by nlinarith only [mul_nonneg (sub_nonneg.mpr w1) (by linarith : 0≤x+y)]⟩
  have equality : (x-w*y)*(x-y/w)=p+q-(w+1/w)*Real.sqrt (p*q) := by
    rw [Real.sqrt_mul pn]
    change (x-w*y)*(x-y/w)=p+q-(w+1/w)*(y*x)
    rw [←xs,←ys]
    field_simp
    ring
  have small : (x-w*y)^2 ≤ (3/2)*K := calc
    _ = |x-w*y| * |x-w*y| := by rw [←sq,sq_abs]
    _ ≤ |x-w*y| * (w*(x-y/w)) := mul_le_mul_of_nonneg_left both (abs_nonneg _)
    _ = w* |(x-w*y)*(x-y/w)| := by rw [abs_mul,abs_of_nonneg rhs]; ring
    _ ≤ w*K := by rw [equality]; exact mul_le_mul_of_nonneg_left fit wn
    _ ≤ _ := mul_le_mul_of_nonneg_right w15 kn
  have big : (x+w*y)^2 ≤ 9*H := calc
    _ ≤ (3*h)^2 := by
      apply pow_le_pow_left₀ (by have := yn.trans xy; positivity)
      have wy := mul_le_mul_of_nonneg_right (show w≤2 by linarith) yn
      linarith
    _ = 9*H := by rw [←hs]; ring
  calc
    _ = (x-w*y)^2*(x+w*y)^2 := by rw [←xs,←ys,←ws]; ring
    _ ≤ ((3/2)*K)*(9*H) := mul_le_mul small big (sq_nonneg _) (by positivity)
    _ ≤ _ := by nlinarith only [mul_nonneg hn kn]

/-- A sum fit within K places q within four square roots of HK of rp. -/
theorem strip_distance {p q r K H : ℝ} (pn : 0≤p) (order : p≤q) (height : q≤H)
    (ratio : r ∈ Set.Icc (1:ℝ) 2) (kn : 0≤K)
    (fit : |p+q-(Real.sqrt r+1/Real.sqrt r)*Real.sqrt (p*q)|≤K) :
    |q-r*p| ≤ 4*Real.sqrt (H*K) := by
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,mul_pow,Real.sq_sqrt (mul_nonneg ((pn.trans order).trans height) kn)]
  exact (strip_sq pn order height ratio kn fit).trans_eq (by ring)

/-- Sorted eligible prime pairs whose sum lies within K of this one fixed prediction. -/
noncomputable def fits (r K : ℝ) : Finset (ℕ×ℕ) := by
  classical exact eligible.filter fun z => |(z.1:ℝ)+z.2-(Real.sqrt r+1/Real.sqrt r)*
    Real.sqrt ((z.1:ℝ)*z.2)|≤K

theorem mem_fits {r K : ℝ} {p q : ℕ} : (p,q)∈fits r K ↔ (p,q)∈eligible ∧
    |(p:ℝ)+q-(Real.sqrt r+1/Real.sqrt r)*Real.sqrt ((p:ℝ)*q)|≤K := by
  classical exact mem_filter

private theorem coords {p q : ℕ} (ok : (p,q)∈eligible) :
    X≤p ∧ p<2*X ∧ p≤q ∧ q<2^1024 := by
  rw [eligible,sample,mem_filter] at ok
  obtain ⟨inside,order⟩ := ok
  obtain ⟨pm,qm,_,_,_⟩ := mem_ordered.mp inside
  rw [primes,mem_filter,mem_Ico] at pm qm
  have boundary : 2*X=2^1024 := by unfold X; decide +kernel
  exact ⟨pm.1.1,pm.1.2,order.le,qm.1.2.trans_eq boundary⟩

private theorem center_bounds {r K : ℝ} (ratio : r∈Set.Icc (1:ℝ) 2) {p q W : ℕ}
    (kn : 0≤K) (width : 16*(2:ℝ)^1024*K ≤ (W:ℝ)^2) (member : (p,q)∈fits r K) :
    ⌊r*p⌋₊≤q+W ∧ q≤⌊r*p⌋₊+W := by
  obtain ⟨ok,approx⟩ := mem_fits.mp member
  obtain ⟨_,_,order,top⟩ := coords ok
  have bound := strip_sq (p:=(p:ℝ)) (q:=(q:ℝ)) (H:=(2:ℝ)^1024)
    (by positivity) (by exact_mod_cast order) (by exact_mod_cast top.le) ratio kn approx
  have dist : |(q:ℝ)-r*p|≤(W:ℝ) := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]
    exact bound.trans width
  have ge := (abs_le.mp dist).1
  have le := (abs_le.mp dist).2
  have low := Nat.floor_le (show 0≤r*p by
    exact mul_nonneg (zero_le_one.trans ratio.1) (Nat.cast_nonneg _))
  have high := Nat.lt_floor_add_one (r*(p:ℝ))
  constructor
  · exact_mod_cast (by linarith : (⌊r*p⌋₊:ℝ)≤(q:ℝ)+W)
  · have h : (q:ℝ)<⌊r*p⌋₊+(W:ℝ)+1 := by linarith
    exact Nat.le_of_lt_succ (by exact_mod_cast h)

/-- Fix a center for each first coordinate. At most 2W+1 integers
fit per coordinate even if the strip crosses zero. -/
theorem strip_count (pairs : Finset (ℕ×ℕ)) (center : ℕ → ℕ) (L W : ℕ)
    (bounds : ∀ z∈pairs, L≤z.1 ∧ z.1<2*L ∧ center z.1≤z.2+W ∧ z.2≤center z.1+W) :
    pairs.card≤L*(2*W+1) := by
  let code (z : ℕ×ℕ) := (z.1,z.2+W-center z.1)
  have into : ∀ z∈pairs, code z∈Ico L (2*L) ×ˢ range (2*W+1) := by
    rintro ⟨p,q⟩ member
    obtain ⟨bottom,top,low,high⟩ := bounds (p,q) member
    exact mem_product.mpr ⟨mem_Ico.mpr ⟨bottom,top⟩,mem_range.mpr (by
      change center p ≤ q+W at low
      change q ≤ center p+W at high
      change q+W-center p < 2*W+1
      omega)⟩
  have distinguish : ∀ z∈pairs, ∀ v∈pairs, code z=code v → z=v := by
    rintro ⟨p,q⟩ first ⟨s,t⟩ second eq
    have hp : p=s := congrArg Prod.fst eq
    subst s
    have h := congrArg Prod.snd eq
    change q+W-center p=t+W-center p at h
    have lo : center p≤q+W := (bounds (p,q) first).2.2.1
    have lt : center p≤t+W := (bounds (p,t) second).2.2.1
    exact Prod.ext rfl (by omega)
  have bound := card_le_card_of_injOn code into distinguish
  simpa only [card_product,Nat.card_Ico,card_range,show 2*L-L=L by omega] using bound

/-- An integer bound on the strip radius bounds the number of pairs for
any nonnegative error allowance. -/
theorem count_at {r K : ℝ} (ratio : r∈Set.Icc (1:ℝ) 2) (kn : 0≤K)
    (W : ℕ) (width : 16*(2:ℝ)^1024*K ≤ (W:ℝ)^2) :
    (fits r K).card ≤ 2^1023*(2*W+1) := by
  have bounded : (fits r K).card≤X*(2*W+1) := by
    apply strip_count _ (fun p => ⌊r*p⌋₊)
    rintro ⟨p,q⟩ member
    obtain ⟨lo,hi,_,_⟩ := coords (mem_fits.mp member).1
    exact ⟨lo,hi,center_bounds ratio kn width member⟩
  simpa only [X] using bounded

/-- Each lower prime permits a strip twelve times 2^512 on each side at error eight. -/
theorem count {r : ℝ} (ratio : r∈Set.Icc (1:ℝ) 2) :
    (fits r 8).card ≤ 2^1023*(2*(12*2^512)+1) :=
  count_at ratio (by norm_num) _ (by norm_num)

/-- For each ratio fixed independently of the pair, an additive-eight fit
occurs on fewer than one in 2^482 ordered-by-size eligible prime pairs. -/
theorem frequency {r : ℝ} (ratio : r∈Set.Icc (1:ℝ) 2) :
    2^482*(fits r 8).card < eligible.card := by
  have arithmetic : 21000000*(2^482*(2^1023*(2*(12*2^512)+1))) < 2^2046 := by decide +kernel
  have bounded := Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left (2^482) (count ratio))
  exact Nat.lt_of_mul_lt_mul_left ((bounded.trans_lt arithmetic).trans ChebyshevPrimeSample.eligible_count)

/-- Even with additive error 2^428 the same fixed prediction fits fewer
than one eligible pair in 2^269. -/
theorem coarse_fraction {r : ℝ} (ratio : r∈Set.Icc (1:ℝ) 2) :
    2^269*(fits r (2^428)).card < eligible.card := by
  have size := count_at (K:=(2:ℝ)^428) ratio (by positivity) (2^728) (by norm_num)
  have margin : 21000000*(2^269*(2^1023*(2*2^728+1))) < 2^2046 := by decide +kernel
  have bound := Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left (2^269) size)
  exact Nat.lt_of_mul_lt_mul_left ((bound.trans_lt margin).trans ChebyshevPrimeSample.eligible_count)

end PrimeFactors.FixedRatioSumPopulation
