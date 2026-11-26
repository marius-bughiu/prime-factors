import PrimeFactors.AscendingDivisorRank
import PrimeFactors.FactorialCheckpointCoverage
import PrimeFactors.FactorialCheckpointMean
import PrimeFactors.MixedPrefixSample
import PrimeFactors.GrowingFactorial

/-! Per-input credit for a skipped terminal convolution on the actual equal-width
prime-pair sample. A pair receives credit only when its smaller prime is in the
penultimate grid and its public feasible width is at least 2^40. -/
namespace PrimeFactors.FactorialCheckpointTarget

open MixedPrefixSample FactorialCheckpointCoverage Finset

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

private theorem xlarge : 2 ≤ X := by decide +kernel
attribute [local irreducible] X eligible sample ordered primes

abbrev Pair := ℕ × ℕ
def product (z : Pair) : ℕ := z.1*z.2

noncomputable def low (n : ℕ) : ℝ := n/(2*(X : ℝ))
noncomputable def span (n : ℕ) : ℝ := Real.sqrt n - low n
noncomputable def rank (z : Pair) : ℝ := ((z.1 : ℝ)-low (product z))/span (product z)

def base (n : ℕ) := ((ShortPascalRow.lower n X - 1 + 209) / 210)*210
def cycles (n : ℕ) := (n.sqrt - base n)/210

/-- The two consecutive tests in the public doubling rule. -/
def WidthAt (C k : ℕ) : Prop := 96*(2*2^k)^2 < C ∧ C ≤ 96*(4*2^k)^2

/-- The terminal width is 4·2^rounds on each sufficiently wide eligible input. -/
noncomputable def rounds (C : ℕ) : ℕ := by
  classical exact if h : ∃ k, WidthAt C k then Nat.find h else 0

private theorem rounds_spec {C : ℕ} (exists_width : ∃ k, WidthAt C k) :
    WidthAt C (rounds C) := by
  classical simpa [rounds, exists_width] using Nat.find_spec exists_width

def blocks (n k : ℕ) := cycles n / (4*2^k)

/-- The precise ranges of the integer checkpoint. The strict bound on the
left of the centered interval is written without truncated subtraction. -/
def inGrid (folded : Bool) (n x k : ℕ) : Prop :=
  if folded then
    let center := base n + 210*(2*2^k*blocks n k)
    let radius := 210*footprint (2^k)
    center < x + radius ∧ x ≤ center + radius
  else base n < x ∧ x ≤ base n + 210*footprint (2*2^k)

def contains (folded : Bool) (z : Pair) (k : ℕ) : Prop := inGrid folded (product z) z.1 k

noncomputable def band (folded : Bool) : Finset Pair := by
  classical
  exact eligible.filter fun z => (2 : ℝ)^40 ≤ span (product z) ∧
    if folded then 48/100 ≤ rank z ∧ rank z ≤ 52/100
    else 1/100 ≤ rank z ∧ rank z ≤ 11/100

private theorem member {folded : Bool} {z : Pair} (hz : z∈band folded) :
    z∈eligible ∧ (2 : ℝ)^40 ≤ span (product z) ∧
    (if folded then 48/100 ≤ rank z ∧ rank z ≤ 52/100
     else 1/100 ≤ rank z ∧ rank z ≤ 11/100) := mem_filter.mp hz

private theorem product_band {z : Pair} (hz : z∈eligible) :
    2*X^2 ≤ product z ∧ product z < 4*X^2 := by
  rw [eligible, sample] at hz
  obtain ⟨mem,_⟩ := mem_filter.mp hz
  obtain ⟨hp,hq,_,lo,_⟩ := (mem_ordered (E:=fun _ => True) (z:=z)).mp mem
  rw [primes] at hp hq
  have p : z.1 < 2*X := (mem_Ico.mp (mem_filter.mp hp).1).2
  have q : z.2 < 2*X := (mem_Ico.mp (mem_filter.mp hq).1).2
  refine ⟨lo, ?_⟩
  dsimp only [product]
  have less := Nat.mul_lt_mul_of_lt_of_lt p q
  nlinarith only [less]

private theorem schedule {z : Pair} (hz : z∈eligible) (wide : (2 : ℝ)^40 ≤ span (product z)) :
    Grid (low (product z)) (Real.sqrt (product z)) (base (product z)) (cycles (product z)) ∧
      WidthAt (cycles (product z)) (rounds (cycles (product z))) := by
  obtain ⟨small, large⟩ := product_band hz
  have grid := product_grid xlarge small large wide
  exact ⟨grid, rounds_spec (terminal_width grid wide)⟩

/-- The actual smaller prime is within the penultimate checkpoint, and the cap
permits every sample through that checkpoint, for the corresponding band. -/
theorem checkpoint {folded : Bool} {z : Pair} (hz : z∈band folded) :
    let n := product z
    let k := rounds (cycles n)
    contains folded z k ∧
    (∀ j, 0 < j → j ≤ (if folded then 2^k else 2*2^k) →
      min (48*j+1) ((if folded then 2*2^k*blocks n k else cycles n)/j) = 48*j+1) := by
  obtain ⟨eligible_mem, wide, bounds⟩ := member hz
  obtain ⟨grid, prev, stop⟩ := schedule eligible_mem wide
  let n := product z
  let k := rounds (cycles n)
  change 96*(2*2^k)^2 < cycles n at prev
  change cycles n ≤ 96*(4*2^k)^2 at stop
  have pos : 0 < span n := lt_of_lt_of_le (by norm_num : (0:ℝ)<2^40) wide
  have actual : low n + rank z * (Real.sqrt n-low n) = z.1 := by
    change low n + (((z.1:ℝ)-low n)/span n)*span n = z.1
    rw [div_mul_cancel₀ _ pos.ne']
    ring
  cases folded with
  | false =>
    obtain ⟨rl, ru⟩ := (show 1/100 ≤ rank z ∧ rank z ≤ 11/100 from bounds)
    have stop' : cycles n ≤ 96*(2*(2*2^k))^2 := by simpa only [← mul_assoc 2 2] using stop
    obtain ⟨pl, pu⟩ := forward_rank (h:=2*2^k) grid wide stop' rl ru
    rw [actual] at pl pu
    refine ⟨⟨?_,?_⟩,fun j jp jh => forward_sample_cap prev jp jh⟩
    · exact_mod_cast pl
    · exact_mod_cast pu
  | true =>
    obtain ⟨rl, ru⟩ := (show 48/100 ≤ rank z ∧ rank z ≤ 52/100 from bounds)
    obtain ⟨pl, pu⟩ := folded_rank (h:=2^k) grid wide (by positivity) prev stop rl ru
    rw [actual] at pl pu
    have pl' := sub_lt_iff_lt_add.mp pl
    refine ⟨⟨?_,?_⟩,fun j jp jh => folded_sample_cap prev jp jh⟩
    · exact_mod_cast pl'
    · exact_mod_cast pu

/-- The unordered candidate set represented by the penultimate wheel blocks,
restricted to positive integers at most the public integer square root. -/
noncomputable def candidates (folded : Bool) (n k : ℕ) : Finset ℕ := by
  classical exact (Icc 1 n.sqrt).filter fun x => x.Coprime 210 ∧ inGrid folded n x k

/-- Membership credited by the model really exposes the smaller prime via one
product gcd. The finite set describes the tested product, without prescribing
a direct enumeration of its entries. -/
theorem reached_gcd {folded : Bool} {z : Pair} {k : ℕ} (hz : z∈eligible)
    (reached : contains folded z k) :
    (product z).gcd (candidates folded (product z) k).toList.prod = z.1 := by
  classical
  rw [eligible, sample] at hz
  obtain ⟨ord, lt⟩ := mem_filter.mp hz
  obtain ⟨pm,qm,_,_,_⟩ := (mem_ordered (E:=fun _ => True) (z:=z)).mp ord
  rw [primes] at pm qm
  obtain ⟨pb,pp⟩ := mem_filter.mp pm
  obtain ⟨qb,qp⟩ := mem_filter.mp qm
  have px := (mem_Ico.mp pb).1
  have qx := (mem_Ico.mp qb).2
  have cop : z.1.Coprime 210 := pp.coprime_iff_not_dvd.mpr (fun dvd => by
    have h := Nat.le_of_dvd (by decide : 0<210) dvd
    have target : 210 < X := by rw [X]; decide +kernel
    omega)
  have bot : z.1 ≤ (product z).sqrt := Nat.le_sqrt.mpr (Nat.mul_le_mul_left _ lt.le)
  let S := candidates folded (product z) k
  have inside : z.1 ∈ S.toList := by
    apply mem_toList.mpr
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨pp.pos,bot⟩,cop,reached⟩
  have checked : ∀ x ∈ S.toList, 0<x ∧ x≤(z.1*z.2).sqrt := by
    intro x hx
    exact mem_Icc.mp (mem_filter.mp (mem_toList.mp hx : x∈S)).1
  have h := GrowingFactorial.membership pp qp lt (by omega) S.toList checked
  simpa only [if_pos inside] using h

theorem band_gcd {folded : Bool} {z : Pair} (hz : z∈band folded) :
    (product z).gcd (candidates folded (product z) (rounds (cycles (product z)))).toList.prod =
      z.1 := reached_gcd (member hz).1 (checkpoint hz).1

/-- Number of submitted coefficients in the complete convolution schedule. -/
noncomputable def fullCount (folded : Bool) (k g : ℕ) :=
  if folded then FoldedFactorial.foldedInputs 48 g k else FoldedFactorial.ordinaryInputs 48 g k

/-- Number of coefficients in the final convolution alone. -/
def lastCount (folded : Bool) (k g : ℕ) :=
  if folded then 3*48*2^k+2*g+2 else 48*2^(k+1)+2*g

private theorem last_le_full (folded : Bool) (k g : ℕ) :
    lastCount folded k g ≤ fullCount folded k g := by
  cases folded <;> simp only [lastCount,fullCount,FoldedFactorial.foldedInputs,
    FoldedFactorial.ordinaryInputs,Bool.false_eq_true,if_false,if_true] <;> omega

private theorem last_pos (folded : Bool) (k g : ℕ) : 0 < lastCount folded k g := by
  cases folded <;> simp only [lastCount,Bool.false_eq_true,if_false,if_true] <;> positivity

/-- The reference count is set to zero on tiny intervals, for which the model
assigns zero relative saving. -/
noncomputable def baseline (folded : Bool) (z : Pair) : ℕ :=
  let n := product z
  let k := rounds (cycles n)
  if (2:ℝ)^40 ≤ span n then fullCount folded k (blocks n k) else 0

noncomputable def terminalCount (folded : Bool) (z : Pair) : ℕ :=
  let n := product z
  let k := rounds (cycles n)
  lastCount folded k (blocks n k)

/-- Credit just the final convolution when the actual smaller prime was
already reached. Give full price to all other pairs. -/
noncomputable def charged (folded : Bool) (z : Pair) : ℕ := by
  classical
  exact if (2:ℝ)^40 ≤ span (product z) ∧ contains folded z (rounds (cycles (product z)))
    then baseline folded z - terminalCount folded z else baseline folded z

theorem checkpoint_price {folded : Bool} {z : Pair} (hz : z∈band folded) :
    0 < baseline folded z ∧
    charged folded z + terminalCount folded z = baseline folded z ∧
    (if folded then 49 else 37) * baseline folded z ≤ 100 * terminalCount folded z := by
  obtain ⟨elig, wide, _⟩ := member hz
  have cover := (checkpoint hz).1
  obtain ⟨_,prev,_⟩ := schedule elig wide
  let n := product z
  let k := rounds (cycles n)
  let g := blocks n k
  have slots : 24*(4*2^k)≤g := terminal_slots k (cycles n) prev
  have hb : baseline folded z = fullCount folded k g := by simp [baseline,wide,n,k,g]
  have last : terminalCount folded z = lastCount folded k g := rfl
  have paid : charged folded z = baseline folded z - terminalCount folded z :=
    if_pos ⟨wide,cover⟩
  rw [paid,hb,last]
  refine ⟨(last_pos folded k g).trans_le (last_le_full folded k g),
    Nat.sub_add_cancel (last_le_full folded k g),?_⟩
  cases folded
  · exact ordinary_share k g slots
  · exact folded_share k g slots

/-- Uniform mean saving in submitted coefficients under the stated normalized
prime-population inequalities. Earlier exits and runtime are outside the metric. -/
theorem target_mean
    (pop : (eligible.card:ℝ)/(X:ℝ)^2 ≤ (1-Real.log 2)/709^2+12/10^16)
    (front : (1-Real.log 2)/(10*710^2)-25/10^16 ≤ ((band false).card:ℝ)/(X:ℝ)^2)
    (mid : (1-Real.log 2)*40/(1021*710^2)-25/10^16 ≤ ((band true).card:ℝ)/(X:ℝ)^2) :
    (36889:ℚ)/1000000 < FactorialCheckpointMean.mean eligible (baseline false) (charged false) ∧
    (1911:ℚ)/100000 < FactorialCheckpointMean.mean eligible (baseline true) (charged true) := by
  have xpos : (0:ℝ)<X := by exact_mod_cast (show 0<X by have := xlarge; omega)
  obtain ⟨f,c⟩ := AscendingDivisorRank.band_counts xpos pop front mid
  have sub (folded : Bool) : band folded ⊆ eligible := fun _ hz => (member hz).1
  have nonempty : eligible.Nonempty := by
    have h := card_le_card (sub false)
    exact card_pos.mp (by omega)
  have less (b : Bool) (z : Pair) : charged b z ≤ baseline b z := by
    unfold charged
    split <;> omega
  constructor
  · apply FactorialCheckpointMean.forward_mean (early:=band false) (last:=terminalCount false)
      nonempty (sub false) f (fun z _ => less false z)
    · exact fun _ h => (checkpoint_price h).1
    · exact fun _ h => (checkpoint_price h).2.1.le
    · exact fun _ h => (checkpoint_price h).2.2
  · apply FactorialCheckpointMean.centered_mean (early:=band true) (last:=terminalCount true)
      nonempty (sub true) c (fun z _ => less true z)
    · exact fun _ h => (checkpoint_price h).1
    · exact fun _ h => (checkpoint_price h).2.1.le
    · exact fun _ h => (checkpoint_price h).2.2

end PrimeFactors.FactorialCheckpointTarget
