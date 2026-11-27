import PrimeFactors.ReciprocalDivisorSums
import PrimeFactors.HalfPeriodWindow
import PrimeFactors.ReciprocalTraceHalving
import Mathlib.Data.Nat.Sqrt

/-! Apply the divisor and factor-sum class counts on an actual candidate
interval, after fixing any earlier arithmetic-progression test. -/
namespace PrimeFactors.ReciprocalSearchWindow
open Finset ReciprocalDivisorSums CharacterInterval
variable {d : ℕ} [NeZero d]

noncomputable def divisorClasses (d : ℕ) [NeZero d] : Finset (ZMod d) :=
  (positive d).image fun x : (ZMod d)ˣ => (x : ZMod d)

theorem divisor_mem {N f : ℕ} {t : ℤ} (hd : d%4=3) (odd : Odd f)
    (div : f ∣ N) (cop : N.Coprime d) (root : (N:ℤ) ∣ t^2+d) :
    (f : ZMod d) ∈ divisorClasses d := by
  let x := ZMod.unitOfCoprime f (cop.of_dvd_left div)
  have point : (x : ZMod d) = f := ZMod.coe_unitOfCoprime ..
  have hpos := divisor_sign hd odd div cop root
  rw [←point] at hpos
  exact mem_image.mpr ⟨x,(pos_mem x).mpr hpos,point⟩

theorem divisor_capacity (hd : d%4=3) (first step len blocks : ℕ)
    (cop : step.Coprime d) (fit : len ≤ blocks*d) :
    2*(surviving (divisorClasses d) first step len).card ≤ blocks*d := by
  have unit := (ZMod.isUnit_iff_coprime step d).mpr cop
  have h := capacity (divisorClasses d) first step len blocks unit fit
  have keys : (divisorClasses d).card ≤ (positive d).card := card_image_le
  have bound := (Nat.mul_le_mul_left 2 keys).trans ((positive_card hd).le.trans (Nat.totient_le d))
  calc
    _ ≤ 2*(blocks*(divisorClasses d).card) := Nat.mul_le_mul_left _ h
    _ = blocks*(2*(divisorClasses d).card) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ bound

theorem sum_capacity {N : ℕ} {t : ℤ} (hd : d%4=3) (small : d≤2^1024)
    (odd : Odd N) (cop : N.Coprime d) (root : (N:ℤ) ∣ t^2+d)
    (first step len blocks : ℕ) (stride : step.Coprime d) (fit : len ≤ blocks*d) :
    4*(surviving (sums (ZMod.unitOfCoprime N cop)) first step len).card ≤ blocks*(d+2^130) := by
  let n := ZMod.unitOfCoprime N cop
  have pos : ReciprocalSumCharacter.sign (n : ZMod d) = 1 := by
    rw [show (n : ZMod d) = N from ZMod.coe_unitOfCoprime ..]
    exact divisor_sign hd odd (dvd_refl N) cop root
  have keys := (card_1024 hd small n pos).trans (Nat.add_le_add_right (Nat.totient_le d) _)
  have h := capacity (sums n) first step len blocks ((ZMod.isUnit_iff_coprime step d).mpr stride) fit
  calc
    _ ≤ 4*(blocks*(sums n).card) := Nat.mul_le_mul_left _ h
    _ = blocks*(4*(sums n).card) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ keys

theorem same_modulus (hd : d%4=3) (n : (ZMod d)ˣ) (square : IsSquare (n : ZMod d))
    (first step len blocks : ℕ) (stride : step.Coprime d)
    (lower : blocks*d ≤ len) (upper : len ≤ (blocks+1)*d) :
    (2*blocks+1)*(surviving (sums n) first step len).card ≤
      (blocks+1)*(surviving (ReciprocalTraceHalving.ordinary n) first step len).card := by
  have sub : sums n ⊆ ReciprocalTraceHalving.ordinary n := by
    intro s hs
    obtain ⟨x,_,eq⟩ := mem_image.mp hs
    exact (ReciprocalTraceHalving.mem_ordinary (Nat.odd_iff.mpr (by omega))).mpr ⟨x,eq⟩
  exact HalfPeriodWindow.compare sub (ReciprocalTraceHalving.exact_half hd n square)
    first step len blocks ((ZMod.isUnit_iff_coprime step d).mpr stride) lower upper

theorem sqrt_of_bounds {x r : ℕ} (lower : r^2≤x) (upper : x<(r+1)^2) :
    x.sqrt = r := Nat.le_antisymm (Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr upper)) (Nat.le_sqrt'.mpr lower)

/-- In a width-L interval, the initial offset of a modulus-60 lane lies in
0 through 59. Its inclusive length differs from L/60 by at most one. -/
def laneLength (width offset : ℕ) := if offset<width then (width-1-offset)/60+1 else 0

theorem lane_sizes (width offset : ℕ) (h : offset<60) :
    width/60≤laneLength width offset ∧ laneLength width offset≤width/60+1 := by
  unfold laneLength
  split_ifs <;> omega

theorem ratio {den actual bound rate low len : ℕ} (pos : 0<den) (cap : den*actual≤bound)
    (scaled : 1000*bound≤den*(rate*low)) (fits : low≤len) : 1000*actual≤rate*len := by
  apply (Nat.mul_le_mul_left_iff pos).mp
  calc
    den*(1000*actual) = 1000*(den*actual) := by ring
    _ ≤ 1000*bound := Nat.mul_le_mul_left _ cap
    _ ≤ den*(rate*low) := scaled
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ fits)

/-- Inclusive endpoints for an ordered factor pair below the public width bound B.
The bounds use integer arithmetic and require no primality assumptions. -/
theorem ranges {p q B : ℕ} (pq : p≤q) (qb : q<B) (large : 1<B) (pos : 0<p) :
    (p*q + (B-1) - 1)/(B-1) ≤ p ∧ p≤(p*q).sqrt ∧
    (4*(p*q)-1).sqrt+1 ≤ p+q ∧ p+q ≤ (B^2+p*q-1)/B := by
  have cap : 0<B-1 := by omega
  have qa : q ≤ B-1 := by omega
  have upper := Nat.mul_le_mul_left p qa
  have enough : 0<p*q := Nat.mul_pos pos (pos.trans_le pq)
  refine ⟨(Nat.div_le_iff_le_mul cap).mpr (by omega), Nat.le_sqrt'.mpr (by nlinarith), ?_, ?_⟩
  · have le : 4*(p*q) ≤ (p+q)^2 := by
      zify; nlinarith [sq_nonneg ((p:ℤ)-q)]
    have inc : 4*(p*q)-1 < (p+q)^2 := by omega
    have lt := Nat.sqrt_lt'.mpr inc
    omega
  · apply (Nat.le_div_iff_mul_le (by omega : 0<B)).mpr
    have pp : p<B := pq.trans_lt qb
    have strict : (p+q)*B < B^2+p*q := by
      zify at pp qb ⊢
      nlinarith only [mul_pos (sub_pos.mpr pp) (sub_pos.mpr qb)]
    omega

end PrimeFactors.ReciprocalSearchWindow
