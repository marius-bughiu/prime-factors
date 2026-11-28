import PrimeFactors.WidePrimePairSumFrequency

/-! Population frequency from the unconditional prime-count bound of Bennett,
Martin, O'Bryant and Rechnitzer, Theorem 1.3, with (1.10) and (1.11)
(https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5).
The published endpoint inequalities are explicit Lean hypotheses. -/
namespace PrimeFactors.UnconditionalPrimePairSumFrequency

open Real WideResiduePrimeSupply WidePrimePairSumFrequency ResiduePairWeights
open private PrimeFactors.WideResiduePrimeSupply.count_add from PrimeFactors.WideResiduePrimeSupply
set_option exponentiation.threshold 4096

private abbrev W : ℕ := 2^1022
private abbrev E : ℕ := 10*2^993
private noncomputable abbrev μ := increment L W/20
private noncomputable abbrev pop (x : ZMod 25) := population (L+1) B x

/-- Theorem 1.3 at the two endpoints, specialized to q=25. The paper's
common Li(L) value is c. The difference between its Li values is the
ordinary integral of 1/log on the given interval. -/
def Endpoints25 (a : ℕ) (c : ℝ) : Prop :=
  |((through 25 a L).card:ℝ)-c/20| ≤ (L:ℝ)/(840*(log L)^2) ∧
  |((through 25 a B).card:ℝ)-(c+increment L W)/20| ≤ (B:ℝ)/(840*(log B)^2)

/-- The constants in the paper apply at both endpoints for modulus 25. -/
theorem source_domain : 3≤(25:ℕ) ∧ 25≤(10000:ℕ) ∧ 8000000000≤L ∧ L≤B := by decide +kernel

private theorem endpoint_cap {x : ℕ} (left : 2^1023≤x) :
    (x:ℝ)/(840*(log x)^2) ≤ (x:ℝ)/(840*700^2) := by
  have logx := log_le_log (by positivity : 0<(2:ℝ)^1023) (by exact_mod_cast left : (2:ℝ)^1023≤x)
  rw [log_pow] at logx
  norm_num only [Nat.cast_ofNat] at logx
  have bound : (700:ℝ)≤log x := by linarith only [logx,log_two_gt_d9]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) bound 2) (by norm_num))

private theorem difference {lo hi d c t e f : ℝ} (left : |lo-c|≤e) (right : |hi-(c+t)|≤f)
    (add : d+lo=hi) : |d-t|≤e+f := by
  rw [abs_le] at left right ⊢
  constructor <;> linarith

/-- The sum of the two endpoint errors is at most 7·2^1022/(840·700²). -/
theorem class_error {c : ℝ} (x : ZMod 25) (endpoints : Endpoints25 x.val c) :
    |(pop x:ℝ)-μ| ≤ 7*(2:ℝ)^1022/(840*700^2) := by
  have lo := endpoints.1.trans (endpoint_cap (by decide : 2^1023≤L))
  have hi := endpoints.2.trans (endpoint_cap (by decide : 2^1023≤B))
  rw [add_div] at hi
  have count : ((intervalPrimes 25 x.val).card:ℝ)+(through 25 x.val L).card=(through 25 x.val B).card := by
    exact_mod_cast PrimeFactors.WideResiduePrimeSupply.count_add 25 x.val L W
  rw [show pop x=(intervalPrimes 25 x.val).card from class_card_eq x]
  exact (difference lo hi count).trans (by norm_num [L,B])

/-- The common-center error as a fraction of the guaranteed main term. -/
theorem relative_error {c : ℝ} (x : ZMod 25) (endpoints : Endpoints25 x.val c) :
    |(pop x:ℝ)-μ| < 0.000242*μ := by
  have low := increment_lower (A:=L) (W:=W) (by decide) (by decide)
  have coarse : 7*(2:ℝ)^1022/(840*700^2) < 0.000242*((W:ℝ)/710/20) := by norm_num [W]
  exact (class_error x endpoints).trans_lt (coarse.trans_le (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right low (by norm_num)) (by norm_num)))

private theorem common_range {c : ℝ} (bounds : ∀ a<25, a.Coprime 25 → Endpoints25 a c) :
    ∃ l u : ℕ, 1≤l ∧ l≤u ∧ 525*u^2≤526*(l-1)^2 ∧
      ∀ x : ZMod 25, IsUnit x → l≤pop x ∧ pop x≤u := by
  let k := ⌊μ⌋₊
  have calcLow := increment_lower (A:=L) (W:=W) (by decide) (by decide)
  have low : ((2^1008+E+1:ℕ):ℝ)≤μ := by
    have finite : ((2^1008+E+1:ℕ):ℝ)≤(W:ℝ)/710/20 := by norm_num [W,E]
    exact finite.trans (div_le_div_of_nonneg_right calcLow (by norm_num))
  have kbig : 2^1008+E+1≤k := Nat.le_floor low
  let l := k-E
  let u := k+E
  have enough : 2^1008≤l-1 := by dsimp only [l]; omega
  have room : 3*525*(2*E+1)≤l-1 := le_trans (by decide +kernel) enough
  have gap : u=(l-1)+(2*E+1) := by dsimp only [u,l]; omega
  have small : 2*E+1≤l-1 := le_trans (by decide +kernel) enough
  have square : 525*u^2≤526*(l-1)^2 := by
    rw [gap]
    have g₁ := Nat.mul_le_mul_left (l-1) room
    have g₂ := Nat.mul_le_mul_left (525*(2*E+1)) small
    nlinarith only [g₁,g₂]
  refine ⟨l,u,by omega,by omega,square,?_⟩
  have centerPos : 0≤μ := (Nat.cast_nonneg _).trans low
  have floorLow : (k:ℝ)≤μ := Nat.floor_le centerPos
  have floorHi : μ<(k:ℝ)+1 := Nat.lt_floor_add_one _
  intro x unit
  have err := (class_error x (bounds x.val x.val_lt ((ZMod.isUnit_iff_coprime _ _).mp
    (by simpa only [ZMod.natCast_zmod_val] using unit)))).trans
      (show 7*(2:ℝ)^1022/(840*700^2)≤E by norm_num [E])
  have within {z v b e : ℝ} (h : |z-v|≤e) (lo : b≤v) (hi : v<b+1) :
      b≤z+e ∧ z<b+e+1 := by rw [abs_le] at h; constructor <;> linarith
  have h := within err floorLow floorHi
  have lower : k≤pop x+E := by exact_mod_cast h.1
  have upper : pop x<k+E+1 := by exact_mod_cast h.2
  dsimp only [l,u]
  omega

/-- The population frequency is within 1/1050 of one half using only
the unconditional paper's two endpoint estimates in the unit classes. -/
theorem near_half (c : ℝ) (bounds : ∀ a<25, a.Coprime 25 → Endpoints25 a c) :
    |share-1/2|≤1/1050 := by
  obtain ⟨l,u,lp,lu,tight,popBounds⟩ := common_range bounds
  simpa only [Nat.cast_ofNat,show (525:ℚ)*2=1050 by norm_num] using
    from_range (by decide : 0<525) lp lu tight popBounds

private theorem rounded {x : ℚ} (acc : |x-1/2|≤1/1050) :
    49.9<100*x ∧ 100*x<50.1 := by rw [abs_le] at acc; constructor <;> linarith

/-- Strict percentage bounds for actual unordered distinct prime pairs. -/
theorem percentage (c : ℝ) (bounds : ∀ a<25, a.Coprime 25 → Endpoints25 a c) :
    49.9<100*share ∧ 100*share<50.1 := rounded (near_half c bounds)

end PrimeFactors.UnconditionalPrimePairSumFrequency
