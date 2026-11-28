import PrimeFactors.FullRangeResidueEstimates

/-! Prime populations of grid cells in the full 1,024-bit range. Fine-grid results
use the EHP error bound under Dirichlet GRH. Coarse-grid results use the
unconditional BMOR bound. Both inputs are the published pointwise estimates
already specified in FullRangeResidueEstimates. -/

namespace PrimeFactors.PrimeGridMass

open Real Finset MeasureTheory WideResiduePrimeSupply FullRangeResidueEstimates
open private PrimeFactors.WideResiduePrimeSupply.count_add from PrimeFactors.WideResiduePrimeSupply
open private PrimeFactors.UnconditionalPrimePairSumFrequency.endpoint_cap from
  PrimeFactors.UnconditionalPrimePairSumFrequency

set_option exponentiation.threshold 4096

/-- Primes in one specified residue class in the cell (A,A+W]. -/
noncomputable abbrev bin (a : ZMod 25) (A W : ℕ) := inBand 25 a.val A W

abbrev low (W : ℕ) := W/14205
abbrev high (W : ℕ) := W/14175

private theorem integrable_inv_log {a b : ℝ} (over : 1<a) (ord : a≤b) :
    IntervalIntegrable (fun x : ℝ => 1/log x) volume a b := by
  have continuous : ContinuousOn (fun x : ℝ => 1/log x) (Set.Icc a b) := by
    apply continuousOn_const.div
    · exact continuousOn_log.mono (fun x hx => ((by norm_num : (0:ℝ)<1).trans (over.trans_le hx.1)).ne')
    · intro x hx
      exact (log_pos (over.trans_le hx.1)).ne'
  exact continuous.intervalIntegrable_of_Icc ord

private theorem integral_add (A W : ℕ) (lo : X≤A) (hi : A+W≤B) :
    increment A W + increment (A+W) (B-(A+W)) = increment A (B-A) := by
  have ord := Nat.le_add_right A W
  have apos : (1:ℝ)<A := by exact_mod_cast (lt_of_lt_of_le (by decide : 1<X) lo)
  have ord' : (A:ℝ)≤((A+W:ℕ):ℝ) := by exact_mod_cast ord
  have hi' : ((A+W:ℕ):ℝ)≤B := by exact_mod_cast hi
  simpa only [increment,Nat.add_sub_of_le hi,Nat.add_sub_of_le (ord.trans hi)] using
    intervalIntegral.integral_add_adjacent_intervals (integrable_inv_log apos ord')
      (integrable_inv_log (apos.trans_le ord') hi')

private theorem increment_upper (A W : ℕ) (lo : X≤A) :
    increment A W ≤ (W:ℝ)/709 := by
  have logX : (709:ℝ)≤log (X:ℝ) := by
    simp only [X,Nat.cast_pow,Nat.cast_ofNat,log_pow]
    linarith only [log_two_gt_d9]
  have pos : (0:ℝ)<X := by norm_num [X]
  have lo' : (X:ℝ)≤A := by exact_mod_cast lo
  have apos : (1:ℝ)<A := (by norm_num [X] : (1:ℝ)<X).trans_le lo'
  have ord : (A:ℝ)≤((A+W:ℕ):ℝ) := by exact_mod_cast Nat.le_add_right A W
  have bound := intervalIntegral.integral_mono_on (μ:=volume) (f:=fun x : ℝ => 1/log x)
    (g:=fun _ : ℝ => (1:ℝ)/709) ord (integrable_inv_log apos ord) intervalIntegrable_const
    (fun x hx => one_div_le_one_div_of_le (by norm_num) (logX.trans (log_le_log pos (lo'.trans hx.1))))
  rw [intervalIntegral.integral_const,smul_eq_mul] at bound
  simpa only [increment,Nat.cast_add,add_sub_cancel_left,div_eq_mul_inv,one_mul] using bound

private theorem interval_error {m a A W : ℕ} {phi : ℝ} {li err : ℕ → ℝ}
    (lo : X≤A) (hi : A+W≤B)
    (suffix : ∀ z, X≤z → z≤B → li B=li z+increment z (B-z))
    (atPoint : ∀ z, X≤z → z≤B →
      |((through m a z).card:ℝ)-li z/phi|≤err z) :
    |((inBand m a A W).card:ℝ)-increment A W/phi| ≤ err A + err (A+W) := by
  have ord := Nat.le_add_right A W
  have l₁ := suffix A lo (ord.trans hi)
  have l₂ := suffix (A+W) (lo.trans ord) hi
  have segment {u v z f g t : ℝ} (hu : z=u+f) (hv : z=v+g) (join : t+g=f) : v=u+t := by linarith
  have liAdd := segment l₁ l₂ (integral_add A W lo hi)
  have e₁ := atPoint A lo (ord.trans hi)
  have e₂ := atPoint (A+W) (lo.trans ord) hi
  rw [liAdd,add_div] at e₂
  have eq : ((inBand m a A W).card:ℝ)+(through m a A).card=(through m a (A+W)).card := by
    exact_mod_cast PrimeFactors.WideResiduePrimeSupply.count_add m a A W
  have difference {z x y c t d f : ℝ} (add : z+x=y) (left : |x-c|≤d)
      (right : |y-(c+t)|≤f) : |z-t|≤d+f := by
    rw [abs_le] at left right ⊢
    constructor <;> linarith
  exact difference eq e₁ e₂

/-- Only two endpoint errors enter a given grid cell, even though the
input records logarithmic integral differences relative to a common B. -/
theorem bin_error {li err : ℕ → ℝ} (h : EndpointEstimates err li) {A W : ℕ}
    (lo : X≤A) (hi : A+W≤B) (a : ZMod 25) (ua : IsUnit a) :
    |((bin a A W).card:ℝ)-increment A W/20| ≤ err A + err (A+W) :=
  interval_error lo hi h.integral (h.pointwise a ua)

private theorem bin_bounds {li err : ℕ → ℝ} (h : EndpointEstimates err li) {A W : ℕ}
    (lo : X≤A) (hi : A+W≤B) (a : ZMod 25) (ua : IsUnit a)
    (error : err A + err (A+W) ≤ (W:ℝ)/50000000) :
    low W ≤ (bin a A W).card ∧ (bin a A W).card ≤ high W := by
  have bound := abs_le.mp ((bin_error h lo hi a ua).trans error)
  have upper := increment_upper A W lo
  have lower := increment_lower lo hi
  have margins {v t w : ℝ} (wl : 0≤w) (lo : w/710≤t) (hi : t≤w/709)
      (a : -(w/50000000)≤v-t/20) (b : v-t/20≤w/50000000) :
      w ≤ 14205*v ∧ 14175*v ≤ w := by constructor <;> linarith
  have ar := margins (Nat.cast_nonneg W) lower upper bound.1 bound.2
  have l : W ≤ 14205*(bin a A W).card := by exact_mod_cast ar.1
  have u : 14175*(bin a A W).card ≤ W := by exact_mod_cast ar.2
  dsimp only [low,high]
  omega

/-- Every class and every location meet the same integer bounds, for any width
down to B/131072. This includes 65536 cells across the full factor interval. -/
theorem ehp_bin {li : ℕ → ℝ} (h : EndpointEstimates ehpError25 li) {A W : ℕ}
    (lo : X≤A) (hi : A+W≤B) (wide : 2^1007≤W) (a : ZMod 25) (ua : IsUnit a) :
    low W ≤ (bin a A W).card ∧ (bin a A W).card ≤ high W := by
  apply bin_bounds h lo hi a ua
  have cap (z : ℕ) (left : X≤z) (right : z≤B) :
      ehpError25 z≤13200*(2:ℝ)^512 :=
    error_cap (by decide) (by decide) (by exact_mod_cast left) (by exact_mod_cast right)
  have exactMargin : 13200*(2:ℝ)^512 + 13200*2^512 ≤ 2^1007/50000000 := by norm_num
  have width : (2:ℝ)^1007≤W := by exact_mod_cast wide
  exact ((add_le_add (cap A lo ((Nat.le_add_right ..).trans hi))
    (cap (A+W) (lo.trans (Nat.le_add_right ..)) hi)).trans exactMargin).trans
    (div_le_div_of_nonneg_right width (by norm_num))

/-- The same bounds on a coarse cell, from the unconditional BMOR endpoint inputs. -/
theorem bmor_bin {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) {A W : ℕ}
    (lo : X≤A) (hi : A+W≤B) (wide : 2^1022≤W) (a : ZMod 25) (ua : IsUnit a) :
    low W ≤ (bin a A W).card ∧ (bin a A W).card ≤ high W := by
  apply bin_bounds h lo hi a ua
  have cap (z : ℕ) (left : X≤z) (right : z≤B) : bmorError25 z≤(B:ℝ)/(840*700^2) :=
    (PrimeFactors.UnconditionalPrimePairSumFrequency.endpoint_cap left).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast right) (by norm_num))
  have exactMargin : (B:ℝ)/(840*700^2)+B/(840*700^2) ≤ 2^1022/50000000 := by norm_num [B]
  exact ((add_le_add (cap A lo ((Nat.le_add_right ..).trans hi))
    (cap (A+W) (lo.trans (Nat.le_add_right ..)) hi)).trans exactMargin).trans
    (div_le_div_of_nonneg_right (by exact_mod_cast wide) (by norm_num))

/-- Ordered pairs of distinct primes from two one-dimensional bins. -/
noncomputable def rectangle (P Q : Finset ℕ) := (P ×ˢ Q).filter (fun v => v.1≠v.2)

/-- Removing equal factors subtracts exactly the size of the intersection of
the bins. This applies both to coinciding and disjoint residue classes. -/
theorem rectangle_exact (P Q : Finset ℕ) :
    (rectangle P Q).card+(P∩Q).card=P.card*Q.card := by
  have eq : (P ×ˢ Q).filter (fun v => v.1=v.2) = (P∩Q).diag := by
    ext ⟨p,q⟩
    simp only [mem_filter,mem_product,mem_diag,mem_inter]
    constructor <;> rintro ⟨⟨pIn,qIn⟩,rfl⟩ <;> exact ⟨⟨pIn,qIn⟩,rfl⟩
  have both := filter_card_add_filter_neg_card_eq_card (s:=P ×ˢ Q) (fun v => v.1=v.2)
  rw [eq,diag_card,card_product] at both
  exact (Nat.add_comm ..).trans both

/-- The two ways of assigning the increasing pair to the two bins add back
to the distinct ordered count. Taking both bins equal gives the exact half. -/
theorem increasing_counts (P Q : Finset ℕ) :
    ((P ×ˢ Q).filter fun v => v.1<v.2).card + ((Q ×ˢ P).filter fun v => v.1<v.2).card =
      (rectangle P Q).card := by
  have reversed : ((P ×ˢ Q).filter fun v => v.2<v.1).card =
      ((Q ×ˢ P).filter fun v => v.1<v.2).card := by
    apply card_nbij' Prod.swap Prod.swap
    · intro v hv
      exact mem_filter.mpr ⟨mem_product.mpr (mem_product.mp (mem_filter.mp hv).1).symm,(mem_filter.mp hv).2⟩
    · intro v hv
      exact mem_filter.mpr ⟨mem_product.mpr (mem_product.mp (mem_filter.mp hv).1).symm,(mem_filter.mp hv).2⟩
    all_goals intro _ _; rfl
  have up : (rectangle P Q).filter (fun v => v.1<v.2) =
      (P ×ˢ Q).filter fun v => v.1<v.2 := by
    ext v
    simp only [rectangle,mem_filter]
    constructor
    · rintro ⟨⟨mem,_⟩,lt⟩; exact ⟨mem,lt⟩
    · rintro ⟨mem,lt⟩; exact ⟨⟨mem,lt.ne⟩,lt⟩
  have down : (rectangle P Q).filter (fun v => ¬v.1<v.2) =
      (P ×ˢ Q).filter fun v => v.2<v.1 := by
    ext v
    simp only [rectangle,mem_filter]
    constructor
    · rintro ⟨⟨mem,ne⟩,nlt⟩; exact ⟨mem,lt_of_le_of_ne (le_of_not_gt nlt) ne.symm⟩
    · rintro ⟨mem,lt⟩; exact ⟨⟨mem,lt.ne'⟩,not_lt_of_ge lt.le⟩
  simpa only [up,down,reversed] using
    filter_card_add_filter_neg_card_eq_card (s:=rectangle P Q) (fun v => v.1<v.2)

/-- Counts of ordered distinct pairs in full rectangles, including equal bins. -/
theorem rectangle_bounds {P Q : Finset ℕ} {l u : ℕ} (p : l≤P.card ∧ P.card≤u)
    (q : l≤Q.card ∧ Q.card≤u) :
    (l-1)^2 ≤ (rectangle P Q).card ∧ (rectangle P Q).card ≤ u^2 := by
  have exactSize := rectangle_exact P Q
  have loss : (P∩Q).card ≤ P.card := card_le_card inter_subset_left
  have clipped : P.card*(Q.card-1) ≤ (rectangle P Q).card := by
    rw [Nat.mul_sub_left_distrib,Nat.mul_one]
    omega
  have lowSize := Nat.mul_le_mul (show l-1 ≤ P.card by omega) (show l-1≤Q.card-1 by omega)
  rw [pow_two,pow_two]
  exact ⟨lowSize.trans clipped,(by omega : (rectangle P Q).card≤P.card*Q.card).trans (Nat.mul_le_mul p.2 q.2)⟩

/-- All full rectangles of the same width have counts within a factor 1.005.
One unit is already reserved on each axis for a possible diagonal. -/
theorem mass_ratio {W : ℕ} (wide : 2^1007≤W) :
    1000*(high W)^2 ≤ 1005*(low W-1)^2 := by
  have enough : 1000000000≤W := (by decide : 1000000000≤2^1007).trans wide
  have ratio : 450*high W ≤ 451*(low W-1) := by dsimp only [high,low]; omega
  have sq := Nat.pow_le_pow_left ratio 2
  rw [mul_pow,mul_pow] at sq
  norm_num only [Nat.reducePow] at sq
  omega

/-- For a cell of width B/4096, BMOR's stated uniform error allowance at B
alone exceeds a tenth of an upper bound for the main cell count. -/
theorem bmor_fine_allowance :
    ((2:ℝ)^1012/709/20)/10 < bmorError25 B := by
  have upper : log (B:ℝ) ≤ 710 := by
    simp only [B,Nat.cast_pow,Nat.cast_ofNat,log_pow]
    linarith only [log_two_lt_d9]
  have pos : 0<log (B:ℝ) := log_pos (by norm_num [B])
  have bound : (B:ℝ)/(840*710^2) ≤ bmorError25 B :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ pos.le upper 2) (by norm_num))
  exact (by norm_num [B] : ((2:ℝ)^1012/709/20)/10 < (B:ℝ)/(840*710^2)).trans_le bound

/-- The unconditional BMOR input at modulus five, where φ(5)=4. -/
structure FiveEndpoints (li : ℕ → ℝ) : Prop where
  integral (z : ℕ) (lo : X≤z) (hi : z≤B) : li B = li z+increment z (B-z)
  pointwise (a : ZMod 5) (ua : IsUnit a) (z : ℕ) (lo : X≤z) (hi : z≤B) :
    |((through 5 a.val z).card:ℝ)-li z/4|≤(z:ℝ)/(840*(log z)^2)

noncomputable abbrev fiveBin (a : ZMod 5) (A W : ℕ) := inBand 5 a.val A W

/-- Class-count bounds for the two meshes with widths B/256 and B/512. -/
abbrev Mesh := Bool
abbrev Mesh.grid256 : Mesh := false
abbrev Mesh.grid512 : Mesh := true

def Mesh.den : Mesh → ℕ | false => 256 | true => 512
def Mesh.lowerDen : Mesh → ℕ | false => 2851 | true => 2861
def Mesh.upperDen : Mesh → ℕ | false => 2826 | true => 2816

theorem bmor_five_bin {li : ℕ → ℝ} (h : FiveEndpoints li) (m : Mesh) {A W : ℕ}
    (lo : X≤A) (hi : A+W≤B) (wide : B≤m.den*W) (a : ZMod 5) (ua : IsUnit a) :
    W/m.lowerDen ≤ (fiveBin a A W).card ∧ (fiveBin a A W).card ≤ W/m.upperDen := by
  have err := interval_error lo hi h.integral (h.pointwise a ua)
  have cap (z : ℕ) (left : X≤z) (right : z≤B) :
      (z:ℝ)/(840*(log z)^2)≤(B:ℝ)/(840*700^2) :=
    (PrimeFactors.UnconditionalPrimePairSumFrequency.endpoint_cap left).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast right) (by norm_num))
  have add := add_le_add (cap A lo ((Nat.le_add_right ..).trans hi))
    (cap (A+W) (lo.trans (Nat.le_add_right ..)) hi)
  have width : (B:ℝ)≤(m.den:ℝ)*W := by exact_mod_cast wide
  have cap₂ {b d : ℝ} (h : b≤d) : b/(840*700^2)+b/(840*700^2)≤2*d/(840*700^2) := by linarith
  have within := abs_le.mp (err.trans (add.trans (cap₂ width)))
  have margins {w t v : ℝ} (w0 : 0≤w) (lo : w/710≤t) (hi : t≤w/709)
      (bounds : -(2*((m.den:ℝ)*w)/(840*700^2))≤v-t/4 ∧ v-t/4≤2*((m.den:ℝ)*w)/(840*700^2)) :
      w≤(m.lowerDen:ℝ)*v ∧ (m.upperDen:ℝ)*v≤w := by
    cases m <;> norm_num only [Mesh.den,Mesh.lowerDen,Mesh.upperDen,Nat.cast_ofNat] at * <;>
      constructor <;> linarith
  have ar := margins (Nat.cast_nonneg W) (increment_lower lo hi) (increment_upper A W lo) within
  have left : W≤m.lowerDen*(fiveBin a A W).card := by exact_mod_cast ar.1
  have right : m.upperDen*(fiveBin a A W).card≤W := by exact_mod_cast ar.2
  cases m <;> simp only [Mesh.lowerDen,Mesh.upperDen] at * <;> omega

/-- Allowing for the diagonal, the worst rectangle mass relative to the
smallest is below 1.018 at width B/256 and 1.033 at width B/512. -/
theorem five_mass_ratios :
    1000*(2^1016/2826)^2 < 1018*(2^1016/2851-1)^2 ∧
    1000*(2^1015/2816)^2 < 1033*(2^1015/2861-1)^2 := by decide +kernel

end PrimeFactors.PrimeGridMass
