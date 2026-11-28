import PrimeFactors.CircleMarkTwoAdicSavings
import PrimeFactors.CircleMarkReducedBands

/-! For certain circle targets the power of two removed from the positive
remainder depends only on the parity of the coordinate. Each parity therefore
has explicit coordinate intervals for all admissible cofactor bands. -/
namespace PrimeFactors.CircleMarkParityLanes

open Finset MixedPrefixSample CircleMarkBandSavings CircleMarkCofactorBands
open scoped Classical
open private PrimeFactors.CircleMarkBandSavings.away PrimeFactors.CircleMarkBandSavings.stop_data
  from PrimeFactors.CircleMarkBandSavings

set_option exponentiation.threshold 8192
set_option maxRecDepth 8192
attribute [local irreducible] eligible primes

def allowed (t : ℕ) : Prop := t=2 ∨ t%8=3 ∨ t%8=5 ∨ t%8=7

/-- The two lanes use c=2,1 at t=2, c=1,4 at t≡5 mod 8, and c=1,2
at t≡3 or 7 mod 8, listed in even-then-odd order. -/
def divisor (t x : ℕ) : ℕ :=
  if t=2 then (if x%2=0 then 2 else 1)
  else if x%2=0 then 1 else if t%8=5 then 4 else 2

theorem divisor_bounds (t x : ℕ) : 0<divisor t x ∧ divisor t x≤4 := by
  unfold divisor
  split_ifs <;> decide

private theorem square_mod (x : ℕ) :
    (x%2=0 → x^2%8=0 ∨ x^2%8=4) ∧ (x%2≠0 → x^2%8=1) := by
  have residues : ∀ i : Fin 8,
      (i.val%2=0 → i.val^2%8=0 ∨ i.val^2%8=4) ∧ (i.val%2≠0 → i.val^2%8=1) := by decide
  have test := residues ⟨x%8,Nat.mod_lt _ (by decide)⟩
  have even : x%8%2=x%2 := Nat.mod_mod_of_dvd _ (by decide)
  have squared : (x%8)^2%8=x^2%8 := (Nat.mod_modEq x 8).pow 2
  simpa only [even,squared] using test

private theorem parts {t x : ℕ} (ok : allowed t) (above : t<x^2) :
    divisor t x*((x^2-t)/divisor t x)=x^2-t ∧ ((x^2-t)/divisor t x)%2=1 := by
  have s := square_mod x
  have rep : x^2-t+t=x^2 := by omega
  have mod := congrArg (fun z : ℕ => z%8) rep
  change (x^2-t+t)%8=x^2%8 at mod
  rw [Nat.add_mod] at mod
  unfold allowed at ok
  unfold divisor
  split_ifs <;> omega

/-- The lane multiplier is the entire two-part, even when the input is far
beyond the small examples. -/
theorem exact_divisor {t x : ℕ} (ok : allowed t) (above : t<x^2) :
    2^((x^2-t).factorization 2)=divisor t x ∧
    ordCompl[2] (x^2-t)=(x^2-t)/divisor t x := by
  let c := divisor t x
  let y := x^2-t
  let z := y/c
  have d := parts ok above
  have form : c*z=y := d.1
  have odd : z%2=1 := d.2
  have c1 : ordCompl[2] 1=1 := by simp
  have c2 : ordCompl[2] 2=1 := by
    change 2/2^((2:ℕ).factorization 2)=1
    rw [Nat.prime_two.factorization_self]
    decide
  have c4 : ordCompl[2] 4=1 := by
    rw [show (4:ℕ)=2*2 by decide,Nat.ordCompl_mul,c2,one_mul]
  have cz : ordCompl[2] c=1 := by unfold c divisor; split_ifs <;> assumption
  have nd : ¬2∣z := by omega
  have zz : ordCompl[2] z=z := by
    change z/2^(z.factorization 2)=z
    simp [Nat.factorization_eq_zero_of_not_dvd nd]
  have rem : ordCompl[2] y=z := by rw [←form,Nat.ordCompl_mul,cz,zz,one_mul]
  have raw := Nat.ordProj_mul_ordCompl_eq_self y 2
  rw [rem] at raw
  have zp : 0<z := Nat.pos_of_ne_zero (fun hz => by simp [hz] at odd)
  exact ⟨Nat.eq_of_mul_eq_mul_right zp (raw.trans form.symm),rem⟩

/-- For a specified positive band index k, the two endpoints are exact.
Only integers of the stated lane parity are used with the corresponding c. -/
theorem lane_interval {t x P H k : ℕ} (ok : allowed t) (above : t<x^2) :
    let c := divisor t x
    let z := ordCompl[2] (x^2-t)
    (k*P≤z ∧ z≤k*H) ↔ ceilSqrt (t+c*k*P)≤x ∧ x≤(t+c*k*H).sqrt := by
  have form := (parts ok above).1
  have cp := (divisor_bounds t x).1
  dsimp only
  rw [(exact_divisor ok above).2,ceilSqrt_le_iff,Nat.le_sqrt']
  have left := Nat.mul_le_mul_left (divisor t x) (n:=k*P) (m:=(x^2-t)/divisor t x)
  have right := Nat.mul_le_mul_left (divisor t x) (n:=(x^2-t)/divisor t x) (m:=k*H)
  rw [←Nat.mul_assoc,form] at left
  rw [←Nat.mul_assoc,form] at right
  constructor
  · rintro ⟨lo,hi⟩
    have l := left lo
    have h := right hi
    omega
  · rintro ⟨lo,hi⟩
    constructor
    · apply (Nat.mul_le_mul_left_iff cp).mp
      rw [←Nat.mul_assoc,form]
      omega
    · apply (Nat.mul_le_mul_left_iff cp).mp
      rw [←Nat.mul_assoc,form]
      omega

/-- The union of the exact intervals over positive k is the full
power-of-two-reduced band test. -/
theorem lanes {t x P H : ℕ} (ok : allowed t) (above : t<x^2) :
    inBands P H (ordCompl[2] (x^2-t)) ↔
      ∃ k, 0<k ∧ ceilSqrt (t+divisor t x*k*P)≤x ∧ x≤(t+divisor t x*k*H).sqrt := by
  exact exists_congr fun _ => and_congr_right fun _ => lane_interval ok above

private theorem skipped_count {n t stop G k R : ℕ} (ok : allowed t) (width : lower n≤U-G)
    (gap : 0<G) (gu : G≤U) (kp : 0<k) (touch : U-G-1≤k*(G-1))
    (edge : 4*(k*(U-G))+CircleMarkSmallTargetPopulation.A≤R^2)
    (target : t≤CircleMarkSmallTargetPopulation.A) :
    (CircleMarkTwoAdicSavings.stripped n t stop).card≤R-1 := by
  have sub : CircleMarkTwoAdicSavings.stripped n t stop⊆Icc 1 (R-1) := by
    intro x hx
    obtain ⟨iv,miss⟩ := mem_filter.mp hx
    refine mem_Icc.mpr ⟨(mem_Icc.mp iv).1,?_⟩
    by_contra! out
    have square := Nat.pow_le_pow_left (show R≤x by omega) 2
    have pp : 0<lower n := by simp [lower]
    have pos : 0<k*(U-G) := Nat.mul_pos kp (pp.trans_le width)
    have above : t<x^2 := by omega
    rw [(exact_divisor ok above).2] at miss
    apply miss (continuous pp (by omega) kp ?_ ?_)
    · exact (Nat.sub_le_sub_right width 1).trans
        (touch.trans (Nat.mul_le_mul_left k (by omega)))
    · have cm := divisor_bounds t x
      apply (Nat.le_div_iff_mul_le cm.1).mpr
      have le := Nat.mul_le_mul (Nat.mul_le_mul_left k width) cm.2
      omega
  exact (card_le_card sub).trans_eq (by simp [Nat.card_Icc])

/-- Sharper savings bound from the at-most-four multiplier on these lanes. The
exception set has share less than 2^-85 over the eligible prime pairs. -/
theorem broad_fraction {v : ℕ×ℕ} (member : v∈eligible) (good : v∉exceptional (2^968))
    {t stop : ℕ} (ok : allowed t) (target : t∈Icc 1 CircleMarkSmallTargetPopulation.A)
    (neg : jacobiSym t (v.1*v.2)= -1) (start : 0<stop)
    (hit : ¬(v.1*v.2).Coprime (CircleMarkSmallTargetPopulation.magnitude t stop 1)) :
    2^359*(CircleMarkTwoAdicSavings.stripped (v.1*v.2) t stop).card<stop := by
  obtain ⟨sep,late⟩ := PrimeFactors.CircleMarkBandSavings.stop_data member good target neg start hit
  have card := skipped_count (stop:=stop) (k:=2^56) (R:=2^541) ok
    (PrimeFactors.CircleMarkBandSavings.away member sep) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (mem_Icc.mp target).2
  exact ((Nat.mul_le_mul_left (2^359) card).trans
    (by decide +kernel : 2^359*(2^541-1)≤2^900)).trans_lt late

/-- Away from the slightly larger exception of share below 2^-23, the
same two-lane filter removes less than 2^-375 of the ordinary walk. -/
theorem far_fraction {v : ℕ×ℕ} (member : v∈eligible) (good : v∉exceptional (2^1000))
    {t stop : ℕ} (ok : allowed t) (target : t∈Icc 1 CircleMarkSmallTargetPopulation.A)
    (neg : jacobiSym t (v.1*v.2)= -1) (start : 0<stop)
    (hit : ¬(v.1*v.2).Coprime (CircleMarkSmallTargetPopulation.magnitude t stop 1)) :
    2^375*(CircleMarkTwoAdicSavings.stripped (v.1*v.2) t stop).card<stop := by
  obtain ⟨sep,late⟩ := PrimeFactors.CircleMarkBandSavings.stop_data member good target neg start hit
  have card := skipped_count (stop:=stop) (k:=2^24) (R:=2^525) ok
    (PrimeFactors.CircleMarkBandSavings.away member sep) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (mem_Icc.mp target).2
  exact ((Nat.mul_le_mul_left (2^375) card).trans
    (by decide +kernel : 2^375*(2^525-1)≤2^900)).trans_lt late

end PrimeFactors.CircleMarkParityLanes
