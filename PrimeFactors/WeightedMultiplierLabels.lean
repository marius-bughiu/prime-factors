import PrimeFactors.Fermat
import PrimeFactors.WeightedMultiplierCoverage

/-! The integer rank used by the public weighted search gives a label in the
larger real interval allowed by the population theorem. -/
namespace PrimeFactors.WeightedMultiplierLabels
open WeightedMultiplierPopulation
set_option maxRecDepth 4096
set_option exponentiation.threshold 4096

/-- Zero-based position in the publicly admissible weighted sum progression. -/
def labelAt (n w i : ℕ) : ℕ :=
  let s := Nat.gcd 24 (2*(w+n))
  let a := ceilSqrt (4*w*n)
  a+((w+n)%s+s-a%s)%s+s*i

private theorem ceiling (m : ℕ) :
    Real.sqrt m ≤ (ceilSqrt m : ℝ) ∧ (ceilSqrt m : ℝ) < Real.sqrt m + 1 := by
  have lo := ceilSqrt_le_iff.mp (le_refl (ceilSqrt m))
  constructor
  · exact (Real.sqrt_le_iff.mpr ⟨by positivity,by exact_mod_cast lo⟩)
  · cases eq : ceilSqrt m with
    | zero => simp [add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)<1)]
    | succ a =>
      have high : a^2<m := by
        by_contra! h
        have := ceilSqrt_le_iff.mpr h
        omega
      have lt : (a:ℝ)<Real.sqrt m := Real.lt_sqrt_of_sq_lt (by exact_mod_cast high)
      push_cast
      linarith

/-- The stride alignment and all subsequent steps cost less than 24J from
the real square-root endpoint, including an exactly square radicand. -/
theorem inside {n w i J : ℕ} (rank : i<J) :
    Label w J (labelAt n w i) (Real.sqrt n) := by
  let s := Nat.gcd 24 (2*(w+n))
  let a := ceilSqrt (4*w*n)
  let off := ((w+n)%s+s-a%s)%s
  have pos : 0<s := Nat.gcd_pos_of_pos_left _ (by decide)
  have cap : s≤24 := Nat.gcd_le_left _ (by decide)
  have small : off<s := Nat.mod_lt _ pos
  have slots := Nat.mul_le_mul_left s rank
  have maxSlots := Nat.mul_le_mul_right J cap
  have room : off+s*i+1 ≤ 24*J := by
    rw [Nat.mul_succ] at slots
    omega
  have scale : Real.sqrt ((4*w*n:ℕ):ℝ) = 2*Real.sqrt w*Real.sqrt n := by
    push_cast
    rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]
    norm_num
  obtain ⟨lo,hi⟩ := ceiling (4*w*n)
  rw [scale] at lo hi
  have budget : (off:ℝ)+(s:ℝ)*i+1≤24*J := by exact_mod_cast room
  change 0≤((a+off+s*i:ℕ):ℝ)-2*Real.sqrt w*Real.sqrt n ∧
    ((a+off+s*i:ℕ):ℝ)-2*Real.sqrt w*Real.sqrt n<24*J
  change 2*Real.sqrt w*Real.sqrt n≤(a:ℝ) at lo
  change (a:ℝ)<2*Real.sqrt w*Real.sqrt n+1 at hi
  push_cast
  constructor
  · have off0 : 0≤(off:ℝ) := by positivity
    have step0 : 0≤(s:ℝ)*i := by positivity
    linarith only [lo,off0,step0]
  · linarith only [hi,budget]

/-- Exactly the nontrivial difference gcd tested after an integer square root.
Witnesses may use the same weight more than once or depend on the full input. -/
def Found (k b n : ℕ) : Prop :=
  ∃ r s i j : ℕ, 0<r ∧ r≤2^k ∧ 0<s ∧ s≤2^k ∧ i<2^b ∧ j<2^b ∧
    let A := labelAt n r i
    let B := labelAt n s j
    let v := (A^2-4*r*n)*(B^2-4*s*n)
    v.sqrt^2=v ∧ 1<(A*B-v.sqrt).gcd n ∧ (A*B-v.sqrt).gcd n<n

/-- Every executable label is on or above its weighted square-root endpoint. -/
theorem above (n w i : ℕ) : 4*w*n≤(labelAt n w i)^2 := by
  apply ceilSqrt_le_iff.mp
  exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)

theorem found_implies_reached {k b n : ℕ} (found : Found k b n) :
    WeightedMultiplierCoverage.Reached k b n := by
  obtain ⟨r,s,i,j,rp,rk,sp,sk,ir,jr,square,_,proper⟩ := found
  let A := labelAt n r i
  let B := labelAt n s j
  let d := A^2-4*r*n
  let e := B^2-4*s*n
  refine ⟨r,s,A,B,rp,rk,sp,sk,inside ir,inside jr,d,e,(d*e).sqrt,?_,?_,square,proper⟩
  · exact (Nat.sub_add_cancel (above n r i)).symm
  · exact (Nat.sub_add_cancel (above n s j)).symm

attribute [local irreducible] MixedPrefixSample.ordered MixedPrefixSample.primes

/-- An unconditional bound for the actual integer progression and square/gcd
test, measured against the entire uniform prime-pair population. -/
theorem population {k b : ℕ}
    (row : (k,b)∈[(4,0),(16,16),(64,64),(128,128),(160,64),(64,256)]) :
    2^(saving k b)*(MixedPrefixSample.sample (Found k b)).card <
      MixedPrefixSample.eligible.card := by
  classical
  have sub : MixedPrefixSample.sample (Found k b) ⊆
      MixedPrefixSample.sample (WeightedMultiplierCoverage.Reached k b) := by
    intro z hz
    rw [MixedPrefixSample.sample,Finset.mem_filter] at hz ⊢
    obtain ⟨mem,order⟩ := hz
    obtain ⟨p,q,ne,size,hit⟩ := (MixedPrefixSample.mem_ordered (E:=Found k b) (z:=z)).mp mem
    exact ⟨(MixedPrefixSample.mem_ordered (E:=WeightedMultiplierCoverage.Reached k b) (z:=z)).mpr
      ⟨p,q,ne,size,found_implies_reached hit⟩,order⟩
  exact (Nat.mul_le_mul_left _ (Finset.card_le_card sub)).trans_lt
    (WeightedMultiplierCoverage.eligible_coverage row)

end PrimeFactors.WeightedMultiplierLabels
