import PrimeFactors.InteriorBatchPopulation
import PrimeFactors.MarginalTraceWidth

/-! Connect the ordinary mod-24 trace schedule to the prime-pair count. -/
namespace PrimeFactors.InteriorBatchPopulation
open Real Finset MarginalTraceWidth

set_option exponentiation.threshold 8192
set_option maxHeartbeats 1000000

/-- The zero-based admissible ordinary trace at a public product. -/
noncomputable def ordinaryLabel (n i : ℕ) : ℕ :=
  let f := ⌈2 * sqrt (n:ℝ)⌉₊
  f + offset (n%24) (f%24) 1 1 i

private theorem period_data : ∀ r o : Fin 24, (r:ℕ).Coprime 6 →
    (step r=6 ∨ step r=12 ∨ step r=24) ∧
    offset r o 1 1 0 < 24 ∧ (offsets r o 1 1).length ∣ 4 := by decide +kernel

/-- If the ordinary sum is between the first and last labels of the extra
batch, its two prime square roots belong to one of the three counted shells. -/
theorem tail_of_labels {p q : ℕ} (unit : (p*q).Coprime 6)
    (lo : ordinaryLabel (p*q) (m*B) ≤ p+q)
    (hi : p+q ≤ ordinaryLabel (p*q) ((m+1)*B)) :
    ∃ s∈({6,12,24}:Finset ℕ), Tail p q s := by
  let n := p*q
  let x : ℝ := 2*sqrt (n:ℝ)
  let f := ⌈x⌉₊
  let r : Fin 24 := ⟨n%24, Nat.mod_lt _ (by decide)⟩
  let o : Fin 24 := ⟨f%24, Nat.mod_lt _ (by decide)⟩
  have ru : (r:ℕ).Coprime 6 := by
    change (n%24).gcd 6=1
    rw [Nat.gcd_comm, Nat.gcd_rec, Nat.mod_mod_of_dvd _ (by decide : 6∣24), ←Nat.gcd_rec, Nat.gcd_comm]
    exact unit
  obtain ⟨st,off,dvd⟩ := period_data r o ru
  change f+offset r o 1 1 (m*B) ≤ p+q at lo
  change p+q ≤ f+offset r o 1 1 ((m+1)*B) at hi
  rw [ordinary_multiple r o ru (dvd.trans (by decide : 4∣m*B))] at lo
  rw [ordinary_multiple r o ru (dvd.trans (by decide : 4∣(m+1)*B))] at hi
  have off' : (offset r o 1 1 0:ℝ) ≤ 23 := by exact_mod_cast (show offset r o 1 1 0≤23 by omega)
  have low : (f:ℝ)+(offset r o 1 1 0+step r*(m*B)) ≤ (p:ℝ)+q := by exact_mod_cast lo
  have high : (p:ℝ)+q ≤ (f:ℝ)+(offset r o 1 1 0+step r*((m+1)*B)) := by exact_mod_cast hi
  have x0 : 0≤x := by dsimp [x]; positivity
  have fle : x≤f := Nat.le_ceil _
  have flt : (f:ℝ)<x+1 := Nat.ceil_lt_add_one x0
  have id : (sqrt q-sqrt p)^2=(p:ℝ)+q-x := by
    dsimp [x,n]
    rw [Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg p)]
    nlinarith only [sq_sqrt (Nat.cast_nonneg q), sq_sqrt (Nat.cast_nonneg p)]
  refine ⟨step r,by simpa using st,?_⟩
  unfold Tail
  rw [id]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  have off0 : (0:ℝ) ≤ offset r o 1 1 0 := by positivity
  norm_num [m,B] at low high ⊢
  constructor
  · linarith only [low,fle,off0]
  · linarith only [high,flt,off']

end PrimeFactors.InteriorBatchPopulation
