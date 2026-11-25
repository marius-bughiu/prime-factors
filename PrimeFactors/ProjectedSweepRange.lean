import PrimeFactors.Fermat
import PrimeFactors.ProjectedSweepBudget
import Mathlib.Tactic.FinCases

namespace PrimeFactors.ProjectedSweepRange

/-- In the lower half of the target product interval both public windows
used by the centered solver have widths proportional to a factor. -/
theorem window_lower {b N : ℕ} (hb : 2≤b) (low : 2*(256*b)^2≤N)
    (high : N≤3*(256*b)^2) :
    let U := 512*b-1
    let L := (N+U-1)/U
    let span := U+N/U-ceilSqrt (4*N)
    3*b ≤ (U-L+1)/2 ∧ 3*b ≤ 2*((span+3)/4) := by
  let U := 512*b-1
  let K := ceilSqrt (4*N)
  have hu : 0<U := by dsimp [U]; omega
  have ue : U+1=512*b := by dsimp [U]; omega
  have cap : K≤896*b := ceilSqrt_le_iff.mpr (by nlinarith [Nat.zero_le (b*b)])
  have kp : 0<K := by
    by_contra! zero
    have eq : K=0 := by omega
    have h : 4*N ≤ (0:ℕ)^2 := ceilSqrt_le_iff.mp (by change K≤0; omega)
    nlinarith [Nat.mul_self_le_mul_self hb]
  have sq : (K-1)^2 < 4*N := lt_of_not_ge (fun h => by
    have bad : K≤K-1 := ceilSqrt_le_iff.mpr h
    omega)
  have lcap : (N+U-1)/U≤400*b := by
    apply Nat.div_le_of_le_mul
    have eu : (U:ℤ)+1=512*(b:ℤ) := by exact_mod_cast ue
    have hpos : 0≤b*(b-1:ℤ) := by apply mul_nonneg <;> omega
    zify at high
    zify [show 1≤N+U by omega]
    nlinarith [eu, congrArg (fun t : ℤ => t*(b:ℤ)) eu]
  have delta : (128*(b:ℤ)-2)^2 ≤ (2*(U:ℤ)-K)^2 := by
    simpa only [pow_two] using mul_self_le_mul_self (by omega : (0:ℤ)≤128*b-2)
      (by omega : 128*(b:ℤ)-2≤2*U-K)
  have sumlow : K+6*b ≤ U+N/U := by
    apply le_of_not_gt
    intro small
    have rem := Nat.lt_mul_div_succ N hu
    have above : (U+N/U+1)*U ≤ (K+6*b)*U := Nat.mul_le_mul_right _ small
    have eu : (U:ℤ)+1=512*(b:ℤ) := by exact_mod_cast ue
    have bbig : 0 ≤ (b:ℤ)*(b-2) := by apply mul_nonneg <;> omega
    zify [show 1≤K by omega] at sq
    zify at rem above cap
    nlinarith only [rem,above,sq,cap,eu,delta,bbig,
      congrArg (fun t : ℤ => t*(b:ℤ)) eu, show 2≤(b:ℤ) by exact_mod_cast hb]
  change 3*b ≤ (U-(N+U-1)/U+1)/2 ∧ 3*b ≤ 2*((U+N/U-K+3)/4)
  omega

set_option exponentiation.threshold 4096 in
/-- X=2^1023 and b=X/256. The conservative window lower bound pays for
the same one-block threshold used on the fresh product. -/
theorem scale_2048 : 360*2^1009 ≤ 2*(3*(2:ℕ)^1015) := by decide +kernel

set_option exponentiation.threshold 4096

private theorem four_weights {b H s : ℕ} (i : Fin 4)
    (hH : 3*b ≤ H) (hs : 3*b ≤ 2*s) (one : 1 ≤ s) :
    3*b ≤ ![2*s,H,2*s^2,2*H*s] i := by
  fin_cases i
  · exact hs
  · exact hH
  · exact hs.trans (Nat.mul_le_mul_left 2 (by simpa [pow_two] using Nat.le_mul_of_pos_right s one))
  · exact hH.trans ((Nat.le_mul_of_pos_left H (by decide : 0 < 2)).trans (Nat.le_mul_of_pos_right _ one))

private theorem ceilSqrt_pos_formula {n : ℕ} (hn : 0 < n) : ceilSqrt n = 1+(n-1).sqrt := by
  cases n with
  | zero => contradiction
  | succ k => simp [ceilSqrt, Nat.add_comm]

private theorem lower_weights {b X U N : ℕ} (hb : 2 ≤ b)
    (first : 256*b = X) (last : 512*b-1 = U) (bound : U*X ≤ 2*X^2)
    (low : 2*X^2 ≤ N) (high : N ≤ 3*X^2) (i : Fin 4) :
    let L := max X ((N+U-1)/U)
    let V := min U (N/X)
    let s := max 1 ((V+N/V-(1+(4*N-1).sqrt)+3)/4)
    let H := max 1 ((V-L+1)/2)
    3*b ≤ ![2*s,H,2*s^2,2*H*s] i := by
  have hu : 0<U := by omega
  have hx : 0<X := by omega
  have upper : U ≤ N/X := (Nat.le_div_iff_mul_le hx).mpr (bound.trans low)
  have lower : X ≤ (N+U-1)/U := by
    apply (Nat.le_div_iff_mul_le hu).mpr
    rw [Nat.mul_comm]
    exact bound.trans (low.trans (Nat.le_sub_of_add_le (Nat.add_le_add_left hu N)))
  have pos : 0<4*N := Nat.mul_pos (by decide) (lt_of_lt_of_le (by positivity) low)
  have root := ceilSqrt_pos_formula pos
  have widths := window_lower (b:=b) (N:=N) hb
    (by simpa only [first] using low) (by simpa only [first] using high)
  dsimp only at widths
  rw [last, root] at widths
  let H := max 1 ((U-(N+U-1)/U+1)/2)
  let s := max 1 ((U+N/U-(1+(4*N-1).sqrt)+3)/4)
  have hH : 3*b ≤ H := widths.1.trans (le_max_right ..)
  have hs : 3*b ≤ 2*s := widths.2.trans (Nat.mul_le_mul_left _ (le_max_right ..))
  have one : 1 ≤ s := le_max_left ..
  dsimp only
  rw [min_eq_left upper, max_eq_right lower]
  change 3*b ≤ ![2*s,H,2*s^2,2*H*s] i
  exact four_weights i hH hs one

/-- Every product in this numerical band has the required four weights
when the scanner uses the bit-width bounds for two 1,024-bit factors. -/
theorem band_weights {N : ℕ} (low : 2*(2^1023)^2 ≤ N) (high : N ≤ 3*(2^1023)^2)
    (i : Fin 4) : 3*2^1015 ≤ ProjectedSweepBudget.windowWeights N i :=
  lower_weights (b:=2^1015) (X:=2^1023) (U:=2^1024-1) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) low high i

/-- A complete sweep in the lower half of the 2,048-bit input interval
satisfies the same conservative work bound as the fresh control. -/
theorem band_full_sweep {N : ℕ} (low : 2*(2^1023)^2 ≤ N) (high : N ≤ 3*(2^1023)^2)
    {ι : Type*} (schedule : Finset ι) (q : ι → ProjectedSweepBudget.Query)
    (covers : ProjectedSweepBudget.oddWords ⊆ schedule.biUnion (fun i => (q i).covered)) :
    2^247 ≤ ∑ i ∈ schedule, (q i).work (ProjectedSweepBudget.windowWeights N) :=
  ProjectedSweepBudget.full_sweep schedule q _ (band_weights low high) scale_2048 covers

end PrimeFactors.ProjectedSweepRange
