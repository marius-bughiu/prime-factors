import PrimeFactors.GeometricWheelBlocks
import PrimeFactors.PrimePowerCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Local divisibility of a fixed one-variable quadratic-sieve polynomial on
an actual block. Each lane labels one root at one prime-power level. Signed
weights compare two polynomials at matching positions. -/
namespace PrimeFactors.MultiplierPolynomialScore
open Finset

/-- The residue is relative to the start of the sampled polynomial block. -/
structure Lane where
  modulus : ℕ
  root : ℕ
  valid : root < modulus

def Lane.accepts (s : Lane) (i : ℕ) : Prop := i ≡ s.root [MOD s.modulus]
instance (s : Lane) (i : ℕ) : Decidable (s.accepts i) := inferInstanceAs (Decidable (_ ≡ _ [MOD _]))

/-- The final, possibly incomplete turn of the progression is included. -/
def Lane.count (s : Lane) (W : ℕ) : ℕ := GeometricWheelBlocks.laneLength s.modulus W s.root

theorem Lane.count_eq (s : Lane) (W : ℕ) :
    ((range W).filter s.accepts).card = s.count W := by
  change ((range W).filter (fun i => i%s.modulus = s.root%s.modulus)).card = _
  rw [Nat.mod_eq_of_lt s.valid]
  simpa [Lane.count] using
    GeometricWheelBlocks.retained_count {s.root} (m:=s.modulus) (by simpa using s.valid) W

/-- One common congruence counts a pair of prime-power root events, even at
two different powers of the same prime. Incompatible roots contribute zero. -/
def intersectionCount (a b : Lane) (W : ℕ) : ℕ :=
  if h : a.root ≡ b.root [MOD a.modulus.gcd b.modulus] then
    GeometricWheelBlocks.laneLength (a.modulus.lcm b.modulus) W (Nat.chineseRemainder' h : ℕ)
  else 0

theorem intersection_exact (a b : Lane) (W : ℕ) :
    ((range W).filter (fun i => a.accepts i ∧ b.accepts i)).card = intersectionCount a b W := by
  unfold intersectionCount
  split_ifs with compatible
  · let c : Lane := ⟨_,Nat.chineseRemainder' compatible,Nat.chineseRemainder'_lt_lcm compatible
      (Nat.zero_lt_of_lt a.valid).ne' (Nat.zero_lt_of_lt b.valid).ne'⟩
    have joined (i : ℕ) : (a.accepts i ∧ b.accepts i) ↔ c.accepts i := by
      obtain ⟨ca,cb⟩ := (Nat.chineseRemainder' compatible).property
      exact ⟨fun ⟨ha,hb⟩ => Nat.mod_lcm (ha.trans ca.symm) (hb.trans cb.symm),
        fun hc => ⟨((Nat.ModEq.of_dvd (Nat.dvd_lcm_left _ _) hc).trans ca),
          ((Nat.ModEq.of_dvd (Nat.dvd_lcm_right _ _) hc).trans cb)⟩⟩
    simpa only [joined] using c.count_eq W
  · have impossible (i : ℕ) : ¬(a.accepts i ∧ b.accepts i) := fun ⟨ha,hb⟩ =>
      compatible ((Nat.ModEq.of_dvd (Nat.gcd_dvd_left _ _) ha).symm.trans
        (Nat.ModEq.of_dvd (Nat.gcd_dvd_right _ _) hb))
    simp [impossible]

/-- Taking one real weight log(p) for every root modulo every included p^j
recovers the truncated log of the small prime part. Negative weights allow a
pointwise paired comparison with the k=1 polynomial on the same block. -/
noncomputable def score {ι : Type*} (I : Finset ι) (roots : ι → Lane) (w : ι → ℝ) (i : ℕ) : ℝ :=
  ∑ a ∈ I, if (roots a).accepts i then w a else 0

private theorem indicator_sum (W : ℕ) (P : ℕ → Prop) [DecidablePred P] (w : ℝ) :
    (∑ i ∈ range W, if P i then w else 0) = (((range W).filter P).card : ℝ) * w := by
  rw [← Finset.sum_filter]
  simp

/-- Exact first moment before division by the block length. Only one integer
progression count is needed per supplied root. -/
theorem first_moment {ι : Type*} (I : Finset ι) (roots : ι → Lane) (w : ι → ℝ) (W : ℕ) :
    (∑ i ∈ range W, score I roots w i) = ∑ a ∈ I, ((roots a).count W : ℝ) * w a := by
  unfold score
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => by rw [indicator_sum,Lane.count_eq])

/-- Exact second moment before division by W. The right side uses only the
root list and pairwise CRT calculations, never a loop over the W positions. -/
theorem second_moment {ι : Type*} (I : Finset ι) (roots : ι → Lane) (w : ι → ℝ) (W : ℕ) :
    (∑ i ∈ range W, (score I roots w i)^2) =
      ∑ a ∈ I, ∑ b ∈ I, (intersectionCount (roots a) (roots b) W : ℝ) * (w a * w b) := by
  let f (a : ι) (i : ℕ) : ℝ := if (roots a).accepts i then w a else 0
  have paired (a b : ι) (i : ℕ) : f a i * f b i =
      if (roots a).accepts i ∧ (roots b).accepts i then w a * w b else 0 := by
    by_cases ha : (roots a).accepts i <;> by_cases hb : (roots b).accepts i <;> simp [ha,hb,f]
  change (∑ i ∈ range W, (∑ a ∈ I, f a i)^2) = _
  simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  simp_rw [paired]
  rw [indicator_sum,intersection_exact]

/-- A deterministic upper bound on the number of sites attaining a specified
score (or paired score gain). A height charge can be included in the threshold.
For any chosen center c the two sums on the right are given above. -/
theorem threshold_bound {ι : Type*} (I : Finset ι) (roots : ι → Lane) (w : ι → ℝ)
    (W : ℕ) (c t : ℝ) (ordered : c ≤ t) :
    (((range W).filter (fun i => t ≤ score I roots w i)).card : ℝ) * (t-c)^2 ≤
    (∑ a ∈ I, ∑ b ∈ I, (intersectionCount (roots a) (roots b) W : ℝ) * (w a * w b)) -
      2*c*(∑ a ∈ I, ((roots a).count W : ℝ) * w a) + (W : ℝ)*c^2 := by
  rw [← indicator_sum, ← first_moment, ← second_moment]
  let f := score I roots w
  change (∑ i ∈ range W, if t ≤ f i then (t-c)^2 else 0) ≤ _
  calc
    _ ≤ ∑ i ∈ range W, (f i-c)^2 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with h
      · exact pow_le_pow_left₀ (sub_nonneg.mpr ordered) (sub_le_sub_right h c) 2
      · exact sq_nonneg _
    _ = _ := by
      simp_rw [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib]
      rw [Finset.sum_const,card_range,nsmul_eq_mul,← Finset.sum_mul,← Finset.mul_sum]
      dsimp [f]
      ring

/-- Every relative root progression contributes less than one site's rounding
error in comparison with its complete-period density. -/
theorem Lane.rounding (s : Lane) (W : ℕ) : |(s.count W : ℝ) - W/(s.modulus : ℝ)| < 1 := by
  have hp : 0 < s.modulus := Nat.zero_lt_of_lt s.valid
  have hp' : (0:ℝ) < s.modulus := by exact_mod_cast hp
  have rem : (W % s.modulus : ℕ) < s.modulus := Nat.mod_lt _ hp
  have rem' : ((W % s.modulus : ℕ) : ℝ) < s.modulus := by exact_mod_cast rem
  have total : (W : ℝ) = ((W/s.modulus : ℕ) : ℝ)*s.modulus + ((W%s.modulus : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod' W s.modulus).symm
  have fraction : (W : ℝ)/(s.modulus : ℝ) = ((W/s.modulus : ℕ) : ℝ) +
      ((W%s.modulus : ℕ) : ℝ)/(s.modulus : ℝ) := by
    rw [total,add_div,mul_div_cancel_right₀ _ hp'.ne']
  have fract_lt : ((W % s.modulus : ℕ) : ℝ)/(s.modulus : ℝ) < 1 :=
    (div_lt_one hp').mpr rem'
  have fract_ge : 0 ≤ ((W % s.modulus : ℕ) : ℝ)/(s.modulus : ℝ) := by positivity
  rw [fraction,abs_lt]
  unfold Lane.count GeometricWheelBlocks.laneLength
  split_ifs with inside
  · have rp : 0 < W%s.modulus := Nat.zero_lt_of_lt inside
    have fract_pos : 0 < ((W%s.modulus : ℕ):ℝ)/(s.modulus : ℝ) := div_pos (by exact_mod_cast rp) hp'
    push_cast
    constructor <;> linarith only [fract_pos,fract_lt]
  · push_cast
    constructor <;> linarith only [fract_ge,fract_lt]

/-- A complete-period density predicts the sum on *every* block with an
additive error at most the total absolute weights of its root lanes. -/
theorem finite_block_error {ι : Type*} (I : Finset ι) (roots : ι → Lane) (w : ι → ℝ) (W : ℕ) :
    |(∑ i ∈ range W, score I roots w i) - ∑ a ∈ I, (W : ℝ)/(roots a).modulus*w a| ≤ ∑ a ∈ I, |w a| := by
  rw [first_moment,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum
  intro a _
  rw [← sub_mul,abs_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right ((roots a).rounding W).le (abs_nonneg (w a))

/-- The local lanes for a shifted integer quadratic are exactly the prime-
power divisibility events, even for negative positions or values. -/
theorem layer {m : ℕ} (A b C start : ℤ) (i : ℕ) :
    (m:ℤ) ∣ A*(start+i)^2+b*(start+i)+C ↔
    (A : ZMod m)*((start : ZMod m)+i)^2 + (b : ZMod m)*((start : ZMod m)+i)+C=0 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rfl

/-- In a modulus where A is a unit, the ordinary MPQS identity sends the
roots to the square roots of the scaled target D by x ↦ Ax+B. -/
theorem unit_leading {R : Type*} [CommRing R] (A B C D : R) (unit : IsUnit A)
    (discriminant : B^2-A*C=D) :
    Nat.card {x : R // A*x^2+2*B*x+C=0} = Nat.card {y : R // y^2=D} := by
  have iffQ (x : R) : A*x^2+2*B*x+C=0 ↔ (A*x+B)^2=D := by
    have eq : A*(A*x^2+2*B*x+C)=(A*x+B)^2-D := by rw [← discriminant]; ring
    constructor
    · intro h
      exact sub_eq_zero.mp (by rw [← eq,h,mul_zero])
    · intro h
      apply unit.mul_right_inj.mp
      rw [eq,h,sub_self,mul_zero]
  let f : {x : R // A*x^2+2*B*x+C=0} → {y : R // y^2=D} :=
    fun x => ⟨A*x.val+B,(iffQ _).mp x.property⟩
  apply Nat.card_congr (Equiv.ofBijective f ⟨?_,?_⟩)
  · intro x y eq
    exact Subtype.ext (unit.mul_right_inj.mp (add_right_cancel (congrArg Subtype.val eq)))
  · intro y
    obtain ⟨v,hv⟩ := unit
    have pre : A*((↑v⁻¹ : R)*(y.val-B))+B = y.val := by
      rw [← hv,← mul_assoc,Units.mul_inv,one_mul,sub_add_cancel]
    exact ⟨⟨_,(iffQ _).mpr (by rw [pre]; exact y.property)⟩,Subtype.ext pre⟩

/-- If p divides the leading coefficient and the linear coefficient stays a
unit modulo p, the quadratic polynomial permutes *every* p^e. In particular
there is exactly one root at each positive power, independent of C. -/
theorem coefficient_permutation {p : ℕ} [Fact p.Prime] (e : ℕ)
    (A b C : ZMod (p^(e+1))) (leading : firstPrimeDigit p e A=0)
    (linear : firstPrimeDigit p e b ≠ 0) :
    Function.Bijective (fun x : ZMod (p^(e+1)) => A*x^2+b*x+C) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,rfl⟩
  intro x y eq
  have regular : firstPrimeDigit p e (A*(x+y)+b) ≠ 0 := by simpa only [map_add,map_mul,leading,zero_mul,zero_add] using linear
  have unit : IsUnit (A*(x+y)+b) := by
    obtain ⟨v,hv⟩ := ZMod.natCast_zmod_surjective (A*(x+y)+b)
    rw [← hv] at regular ⊢
    rw [map_natCast] at regular
    exact (ZMod.isUnit_iff_coprime _ _).mpr <| Nat.Coprime.pow_right _ <|
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun hd => regular <|
        (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hd)).symm
  apply unit.mul_right_inj.mp
  change A*x^2+b*x+C = A*y^2+b*y+C at eq
  linear_combination eq

end PrimeFactors.MultiplierPolynomialScore
