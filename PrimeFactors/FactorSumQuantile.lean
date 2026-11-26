import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! For ordered factors p≤q bounded by B, this public cutoff tests whether
q³≤B²p. Its width is at most one quarter of the exact real sum interval.
These are finite algebraic statements, independent of any sampling law. -/
namespace PrimeFactors.FactorSumQuantile

/-- Squared version of the half-quantile cutoff using only the product and B. -/
def inWindow (N B S : ℕ) : Prop := B^2*(S^2-2*N)^2≤N*(B^2+N)^2

/-- The decision can be made from the public product and a sum candidate. -/
theorem criterion {p q B : ℕ} (order : p≤q) (bound : q≤B) :
    inWindow (p*q) B (p+q) ↔ q^3≤B^2*p := by
  have square : (p+q)^2-2*(p*q)=p^2+q^2 := by
    apply Nat.sub_eq_of_eq_add
    ring
  rw [inWindow,square]
  by_cases eq : p=q
  · subst q
    have le : p^3≤B^2*p := by
      rw [pow_succ p 2]
      exact Nat.mul_le_mul_right p (Nat.pow_le_pow_left bound 2)
    simp only [le,iff_true]
    nlinarith only [sq_nonneg ((B:ℤ)^2-p^2)]
  · have h : p<q := lt_of_le_of_ne order eq
    have pos : (p:ℤ)^3<(B:ℤ)^2*q := by
      have qq : (p:ℤ)^3<(q:ℤ)^3 := by exact_mod_cast Nat.pow_lt_pow_left h (by decide : 3≠0)
      have bq : (q:ℤ)^3≤(B:ℤ)^2*q := by
        rw [pow_succ]
        exact_mod_cast Nat.mul_le_mul_right q (Nat.pow_le_pow_left bound 2)
      exact qq.trans_le bq
    zify
    have factor : (p:ℤ)*q*((B:ℤ)^2+p*q)^2-B^2*(p^2+q^2)^2=
        (B^2*p-q^3)*(B^2*q-p^3) := by ring
    have sign := mul_nonneg_iff_of_pos_right (sub_pos.mpr pos) (b:=(B:ℤ)^2*p-q^3)
    omega

/-- Largest natural candidate in the cutoff. -/
def upperSum (n B : ℕ) : ℕ :=
  (2*n+(n*(B^2+n)^2/B^2).sqrt).sqrt

theorem le_upperSum {n B S : ℕ} (bp : 0<B) :
    S≤upperSum n B ↔ inWindow n B S := by
  rw [upperSum,Nat.le_sqrt']
  rw [←Nat.sub_le_iff_le_add']
  rw [Nat.le_sqrt']
  rw [Nat.le_div_iff_mul_le (pow_pos bp 2)]
  simp only [inWindow,mul_comm]

/-- Let T=2√N and U=B+N/B. The real upper endpoint is the square
root of T(T+U)/2, so the public window uses at most a quarter of the span. -/
theorem quarter_span {T U : ℝ} (t0 : 0≤T) (range : T≤U) :
    Real.sqrt (T*(T+U)/2)-T≤(U-T)/4 := by
  have upper : 0≤T+(U-T)/4 := by linarith
  have sq := sq_nonneg (U-T)
  have bound : Real.sqrt (T*(T+U)/2) ≤ T+(U-T)/4 :=
    Real.sqrt_le_iff.mpr ⟨upper,by nlinarith⟩
  linarith

/-- Direct real-width consequence of the public integer test on an actual sum. -/
theorem tested_span {n B S : ℕ} (bp : 0<B) (sumSize : 2*n≤S^2)
    (inside : inWindow n B S) :
    (S:ℝ)-2*Real.sqrt n ≤ ((B:ℝ)+(n:ℝ)/B-2*Real.sqrt n)/4 := by
  let t := Real.sqrt (n:ℝ)
  have t0 : 0≤t := Real.sqrt_nonneg _
  have sq : t^2=(n:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have br : (0:ℝ)<B := by exact_mod_cast bp
  have delta : ((B:ℝ)*((S:ℝ)^2-2*n))^2≤(t*(B^2+n))^2 := by
    unfold inWindow at inside
    have cast := (Nat.cast_le (α:=ℝ)).mpr inside
    push_cast [Nat.cast_sub sumSize] at cast
    nlinarith only [cast,congrArg (fun x : ℝ => x*((B:ℝ)^2+n)^2) sq]
  have bound := le_of_pow_le_pow_left₀ (by decide : 2≠0)
    (show 0≤t*((B:ℝ)^2+n) by positivity) delta
  have order : 2*t ≤ (B:ℝ)+n/B := by
    have le : 2*t-B ≤ (n:ℝ)/B := (le_div_iff₀ br).mpr
      (by nlinarith only [sq,sq_nonneg ((B:ℝ)-t)])
    linarith
  have Sbound : (S:ℝ)≤Real.sqrt ((2*t)*(2*t+(B+n/B))/2) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (mul_le_mul_iff_of_pos_right br).mp
    have clear : ((B:ℝ)+n/B)*B=B^2+n := by rw [add_mul,div_mul_cancel₀ _ br.ne',pow_two]
    rw [mul_assoc (2*t),add_mul,clear]
    nlinarith only [bound,congrArg (fun x : ℝ => (B:ℝ)*x) sq]
  have quarter := quarter_span (T:=2*t) (U:=(B:ℝ)+n/B) (by positivity) order
  change (S:ℝ)-2*t ≤ ((B:ℝ)+n/B-2*t)/4
  linarith

end PrimeFactors.FactorSumQuantile
