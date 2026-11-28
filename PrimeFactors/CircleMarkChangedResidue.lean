import PrimeFactors.CircleMarkChangedPrimeSum
import Mathlib.NumberTheory.LSeries.ZMod

/-! The residue of the periodic L-function for the unsigned change indicator.
An approximation to this residue is an input to the rounding theorem. -/

namespace PrimeFactors.CircleMarkChangedResidue

open Finset CircleMarkSharedOccurrence CircleMarkChangedPrimeSum
open scoped Classical Topology

set_option exponentiation.threshold 4096

/-- One when the square prefix changes the ordinary Jacobi score, zero otherwise. -/
noncomputable def indicator (n : ℕ) [NeZero n] (d : ℕ) (t : ZMod n) : ℂ :=
  if t ∈ changed n {Icc 1 d} then 1 else 0

/-- Exact real residue, represented as a rational frequency. -/
noncomputable def value (n : ℕ) [NeZero n] (d : ℕ) : ℚ := (tally n d : ℚ) / n

theorem residue (n : ℕ) [NeZero n] (d : ℕ) :
    Filter.Tendsto (fun s : ℂ => (s-1) * ZMod.LFunction (indicator n d) s)
      (𝓝[≠] 1) (𝓝 (value n d : ℂ)) := by
  have cnt : (∑ t : ZMod n, indicator n d t) = (tally n d : ℂ) := by
    simp [indicator, sum_boole, tally]
  simpa only [← sum_div, cnt, value, Rat.cast_div, Rat.cast_natCast] using
    ZMod.LFunction_residue_one (indicator n d)

/-- Before local square repetitions, the residue numerator is linear in the prime sum. -/
theorem prefix_value {p q d : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) (cap : d ≤ (p-1)/2) :
    value (p*q) d = ((d*(p+q-2-d) : ℕ) : ℚ) / (p*q : ℕ) := by
  rw [value, tally_eq order op oq cap]

theorem singleton_value {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) :
    value (p*q) 1 = ((p+q-3 : ℕ) : ℚ) / (p*q : ℕ) := by
  rw [value, (singleton order op oq).1]

/-- Rational precision result lifted to arbitrary real readings by bracketing
the reading with two rationals inside the same strict error interval. -/
private theorem rounded_real {p q d : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) (pos : 0 < d) (cap : d ≤ (p-1)/2)
    (x : ℝ) (err : |x - (tally (p*q) d : ℝ)| < d) :
    2*⌊(x/d+d+2)/2+1/2⌋ = (p : ℤ)+q := by
  let h := tally (p*q) d
  change |x-(h:ℝ)| < d at err
  rw [abs_lt] at err
  let f (z : ℝ) := 2*⌊(z/d+d+2)/2+1/2⌋
  have mono : Monotone f := by
    intro a b hab
    apply mul_le_mul_of_nonneg_left (Int.floor_le_floor ?_) (by decide)
    gcongr
  have rational (z : ℚ) (lo : (h:ℝ)-d < z) (hi : (z:ℝ) < h+d) : f z = (p : ℤ)+q := by
    have L : (h:ℚ)-d < z := by exact_mod_cast lo
    have U : z < (h:ℚ)+d := by exact_mod_cast hi
    have prec : |z-(h:ℚ)| < d := by rw [abs_lt]; constructor <;> linarith
    have id : (((z/d+d+2)/2+1/2 : ℚ) : ℝ) = ((z:ℝ)/d+d+2)/2+1/2 := by
      push_cast
      rfl
    change 2*⌊((z:ℝ)/d+d+2)/2+1/2⌋ = _
    rw [← id, Rat.floor_cast]
    exact rounded_sum order op oq pos cap z prec
  obtain ⟨a,la,ax⟩ := exists_rat_btwn (by linarith only [err.1] : (h:ℝ)-d < x)
  obtain ⟨b,xb,bu⟩ := exists_rat_btwn (by linarith only [err.2] : x < (h:ℝ)+d)
  exact le_antisymm ((mono xb.le).trans_eq (rational b (la.trans (ax.trans xb)) bu))
    ((rational a la (ax.trans (xb.trans bu))).symm.le.trans (mono ax.le))

/-- For a supplied real reading of the residue, strict absolute error below
d/N suffices to recover the prime sum by rounding to the nearest even integer. -/
theorem recover {p q d : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) (pos : 0 < d) (cap : d ≤ (p-1)/2)
    (y : ℝ) (err : |y - (value (p*q) d : ℝ)| < (d : ℝ) / (p*q : ℕ)) :
    2*⌊((((p*q : ℕ) : ℝ)*y)/d+d+2)/2+1/2⌋ = (p : ℤ)+q := by
  let n := p*q
  have nn : 0 < (n : ℝ) := by exact_mod_cast Nat.mul_pos hp.out.pos hq.out.pos
  apply rounded_real order op oq pos cap
  change |(n:ℝ)*y-(tally n d:ℝ)| < d
  have scaled : (n:ℝ)*y-(tally n d:ℝ) = n*(y-(value n d:ℝ)) := by
    simp only [value, Rat.cast_div, Rat.cast_natCast]
    field_simp
    ring
  rw [scaled, abs_mul, abs_of_pos nn]
  have strict := mul_lt_mul_of_pos_left err nn
  change (n:ℝ)*|y-(value n d:ℝ)| < n*((d:ℝ)/n) at strict
  rwa [mul_div_cancel₀ _ nn.ne'] at strict

/-- A singleton reading with error below 1/N suffices. -/
theorem recover_singleton {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime] (order : p < q)
    (op : p ≠ 2) (oq : q ≠ 2) (y : ℝ)
    (err : |y - (value (p*q) 1 : ℝ)| < 1/(p*q : ℕ)) :
    2*⌊((((p*q : ℕ) : ℝ)*y)+3)/2+1/2⌋ = (p : ℤ)+q := by
  have pp := hp.out.two_le
  have cap : 1 ≤ (p-1)/2 := by omega
  have res := recover order op oq (by decide : 0<1) cap y (by simpa only [Nat.cast_one] using err)
  norm_num only [Nat.cast_one, div_one, add_assoc, Nat.reduceAdd, one_add_one_eq_two] at res
  convert res using 1

/-- For two 1024-bit primes, the public length and any supplied residue
reading with absolute error below 2⁻¹⁰²⁶ determine the rounded prime sum. -/
theorem full_width {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (lo : 2^1023 ≤ p) (order : p < q) (hi : q < 2^1024)
    (y : ℝ) (err : |y - (value (p*q) (publicLength (p*q)) : ℝ)| < 1/2^1026) :
    let d := publicLength (p*q)
    2*⌊((((p*q : ℕ) : ℝ)*y)/d+d+2)/2+1/2⌋ = (p : ℤ)+q := by
  have op : 2 < p := (by decide +kernel : 2 < 2^1023).trans_le lo
  have bal : q < 2*p := calc
    q < 2^1024 := hi
    _ = 2*2^1023 := by decide +kernel
    _ ≤ 2*p := Nat.mul_le_mul_left 2 lo
  obtain ⟨pos,cap⟩ := public_safe order bal op.ne'
  apply recover order op.ne' (op.trans order).ne' pos cap y
  apply err.trans
  rw [div_lt_div_iff₀ (by positivity) (by exact_mod_cast Nat.mul_pos hp.out.pos hq.out.pos), one_mul]
  exact_mod_cast public_scale lo order hi

/-- At 37·59 the singleton and the balanced public length 16 have distinct
residues. The reading 0.57 lies strictly within the length-16 rounding margin. -/
theorem example_2183 :
    publicLength 2183 = 16 ∧ value 2183 1 = 93/2183 ∧ value 2183 16 = 1248/2183 ∧
      |(57/100 : ℝ) - (value 2183 16 : ℝ)| < 16/2183 ∧
      2*⌊(((2183 : ℝ)*(57/100))/16+16+2)/2+1/2⌋ = 96 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 59) := ⟨by decide⟩
  have single := singleton_value (p:=37) (q:=59) (by decide) (by decide) (by decide)
  have many := prefix_value (p:=37) (q:=59) (d:=16) (by decide) (by decide) (by decide) (by decide)
  norm_num at single many
  refine ⟨by norm_num [publicLength], single, many, ?_, ?_⟩
  · rw [many]
    norm_num [abs_lt]
  · norm_num

end PrimeFactors.CircleMarkChangedResidue
