import PrimeFactors.Fermat
import PrimeFactors.CircleMarkFirstTarget
import Mathlib.Tactic.NormNum.LegendreSymbol

/-! The factors in a common short-deficit rectangle already lie within the
first Fermat midpoint. A single prime in that interval need not suffice. -/
namespace PrimeFactors.CircleMarkRationalMidpoint

/-- The exact first-midpoint condition. Equality at the upper limit puts the
product at the preceding square, which is why the inequality is strict. -/
theorem midpoint_iff {p d : ℕ} (positive : 0 < p) :
    ceilSqrt (p*(p+2*d)) = p+d ↔ d^2+1 < 2*(p+d) := by
  let m := p+d-1
  have next : m+1 = p+d := by dsimp [m]; omega
  have upper : ceilSqrt (p*(p+2*d)) ≤ p+d :=
    ceilSqrt_le_iff.mpr (by nlinarith only [Nat.zero_le (d^2)])
  have previous : m^2 < p*(p+2*d) ↔ d^2+1 < 2*(p+d) := by
    have identity : m^2+d^2+2*(p+d) = p*(p+2*d)+1+2*d^2 := by
      have squares := congrArg (fun n : ℕ => n^2) next
      dsimp only at squares
      nlinarith only [next,squares]
    omega
  constructor
  · intro eqn
    apply previous.mp
    exact lt_of_not_ge fun too_low => (by omega : ¬ceilSqrt (p*(p+2*d)) ≤ m)
      (ceilSqrt_le_iff.mpr too_low)
  · intro gap
    have lower : ¬ceilSqrt (p*(p+2*d)) ≤ m := fun h =>
      (not_le_of_gt (previous.mpr gap)) (ceilSqrt_le_iff.mp h)
    omega

/-- A product-only computation of both factors by the first square test. -/
def FirstSplit (p q : ℕ) : Prop :=
  let n := p*q
  let m := ceilSqrt n
  let d := (m^2-n).sqrt
  m = (p+q)/2 ∧ m^2 = n+d^2 ∧ m-d = p ∧ m+d = q

private theorem split_of_gap {p d : ℕ} (positive : 0 < p) (gap : d^2+1<2*(p+d)) :
    FirstSplit p (p+2*d) := by
  have middle := (midpoint_iff positive).mpr gap
  have eqn : (p+d)^2 = p*(p+2*d)+d^2 := by ring
  have delta : (p+d)^2-p*(p+2*d)=d^2 := by omega
  simp only [FirstSplit,middle,delta,Nat.sqrt_eq']
  exact ⟨by omega,eqn,by omega,by omega⟩

/-- Both factors can lie on either side of the rectangle's threshold. Any
odd ordered pair in the symmetric band still splits on the first midpoint. -/
theorem symmetric_band {H D p q : ℕ} (op : Odd p) (oq : Odd q) (ordered : p≤q)
    (low : (H+1)*(D+1) ≤ p+min H D) (high : q ≤ (H+1)*(D+1)+min H D) : FirstSplit p q := by
  let k := min H D
  have kh : k ≤ H := min_le_left ..
  have kd : k ≤ D := min_le_right ..
  have width := Nat.mul_le_mul (Nat.succ_le_succ kh) (Nat.succ_le_succ kd)
  change (H+1)*(D+1) ≤ p+k at low
  change q ≤ (H+1)*(D+1)+k at high
  let d := (q-p)/2
  have step : q=p+2*d := by
    obtain ⟨x,hx⟩ := op
    obtain ⟨y,hy⟩ := oq
    dsimp [d]; omega
  have bound : d ≤ k := by omega
  have strong : k^2 < p := by nlinarith only [width,low,Nat.zero_le k]
  have gap := (Nat.pow_le_pow_left bound 2).trans_lt strong
  rw [step]
  exact split_of_gap (by omega) (by omega)

/-- The shared two-prime shortfalls from the exact target-count formula are
inside the symmetric band. Only oddness and the two interval bounds are used. -/
theorem shortfalls {H D p q s t : ℕ} (op : Odd p) (oq : Odd q) (ordered : p≤q)
    (pe : p=(H+1)*(D+1)+s) (qe : q=(H+1)*(D+1)+t) (th : t≤H) (td : t≤D) : FirstSplit p q := by
  apply symmetric_band (H:=H) (D:=D) op oq ordered
  · omega
  · exact qe.trans_le (Nat.add_le_add_left (le_min th td) _)

/-- The 3×3 grid's two-prime count at 323 lies in the first-midpoint band. -/
theorem at_323 : FirstSplit 17 19 :=
  shortfalls (H:=3) (D:=3) (s:=1) (t:=3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem first_9017 : CircleMarkFirstTarget.First 9017 3 := by
  refine ⟨by norm_num, ?_⟩
  intro a neg
  by_cases small : a ≤ 2
  · interval_cases a <;> norm_num at neg
  · omega

private theorem ceiling_9017 : ceilSqrt 9017=95 := by
  have upper : ceilSqrt 9017≤95 := ceilSqrt_le_iff.mpr (by decide)
  have lower : ¬ceilSqrt 9017≤94 := fun h => (by decide : ¬9017≤94^2) (ceilSqrt_le_iff.mp h)
  omega

private theorem first_four {n m : ℕ} (start : ceilSqrt n=m)
    (tests : ∀ k ∈ [0,1,2,3], ((m+k)^2-n).sqrt^2 ≠ (m+k)^2-n) :
    fermatWindowMiss n 4 = true := by
  rw [fermatWindowMiss, start, show List.range 4=[0,1,2,3] by rfl, List.all_eq_true]
  exact fun k hk => decide_eq_true (tests k hk)

private theorem miss_9017 : fermatWindowMiss 9017 4 = true := by
  apply first_four ceiling_9017
  intro k hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl <;> norm_num

/-- Only the smaller prime is close to the 6×9 grid's threshold, 70. The
first selected target supplies a successful grid leaf at (2,5). Fermat needs
five midpoints for these two seven-bit primes. -/
theorem one_side : 71*127 = 9017 ∧ (71:ℕ).Prime ∧ (127:ℕ).Prime ∧
    CircleMarkFirstTarget.First 9017 3 ∧
    Nat.gcd 9017 (((2:ℤ)^2-3*5^2).natAbs) = 71 ∧
    ceilSqrt 9017 = 95 ∧ fermatWindowMiss 9017 4 = true ∧ 99^2 = 9017+28^2 :=
  ⟨by decide,by decide,by decide,first_9017,by decide,ceiling_9017,miss_9017,by decide⟩

end PrimeFactors.CircleMarkRationalMidpoint
