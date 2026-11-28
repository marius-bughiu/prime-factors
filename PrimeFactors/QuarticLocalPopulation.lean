import PrimeFactors.ExtendedProductCosts
import PrimeFactors.PrimeGridMass

/-! Population frequencies of the congruences in the local quartic criterion.
The finite census is exact. The prime counts take published analytic estimates
as explicit hypotheses. -/

namespace PrimeFactors.QuarticLocalPopulation

open Finset WideResiduePrimeSupply PrimeResidueRankTransfer
open FullRangeResidueEstimates (X)
open PrimeProductRegion (K)
open MixedPrefixSample (eligible)
open private PrimeFactors.FiveSquareAllPrimeRanks.actual_weighted
  PrimeFactors.FiveSquareAllPrimeRanks.raw
  from PrimeFactors.FiveSquareAllPrimeRanks
open private PrimeFactors.ExtendedProductCosts.unit_of_prime from PrimeFactors.ExtendedProductCosts

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096
attribute [local irreducible] eligible cell

/-- Sorted, distinct 1,024-bit prime pairs with 2,048-bit product satisfying
the congruences at the primes dividing the product and at the prime two. -/
noncomputable def locus := eligible.filter fun v =>
  v.1%4=1 ∧ v.2%4=1 ∧ ((v.1*v.2)%16=1 ∨ (v.1*v.2)%16=5)

theorem mem_locus {p q : ℕ} : (p,q)∈locus ↔ (p,q)∈eligible ∧
    p%4=1 ∧ q%4=1 ∧ ((p*q)%16=1 ∨ (p*q)%16=5) := mem_filter

/-- The condition on the publicly visible product alone. -/
noncomputable def lastBits := eligible.filter fun v => (v.1*v.2)%16=1 ∨ (v.1*v.2)%16=5

theorem mem_lastBits {p q : ℕ} : (p,q)∈lastBits ↔ (p,q)∈eligible ∧
    ((p*q)%16=1 ∨ (p*q)%16=5) := mem_filter

private noncomputable abbrev selected (onlyProduct : Bool) := if onlyProduct then lastBits else locus

private abbrev markProp (onlyProduct : Bool) (a b r : ℕ) :=
  (onlyProduct=true ∨ a%4=1 ∧ b%4=1) ∧ (r=1 ∨ r=5)

def mark (onlyProduct : Bool) (a b : ZMod 16) : ℕ :=
  if markProp onlyProduct a.val b.val (a*b).val then 1 else 0

private theorem sym (k : Bool) (a b : ZMod 16) : mark k a b=mark k b a := by
  simp only [mark,markProp,mul_comm b a,and_comm]

private theorem nat_mark (k : Bool) (a b : ℕ) : mark k a b=
    if markProp k a b ((a*b)%16) then 1 else 0 := by
  simp only [mark,markProp,←Nat.cast_mul,ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 4∣16)]

abbrev Units16 := (ZMod 16)ˣ×(ZMod 16)ˣ

/-- Eight of the 64 ordered unit cells satisfy the full criterion. Sixteen
satisfy its product-only condition. -/
theorem census : (∑ v : Units16, mark false v.1 v.2)=8 ∧
    (∑ v : Units16, mark true v.1 v.2)=16 ∧ Fintype.card Units16=64 := by
  decide +kernel

private theorem share_counts (S : Finset (ℕ×ℕ)) (k : Bool) :
    (∑ v∈S, mark k v.1 v.2) = (if k then S.filter (fun v => (v.1*v.2)%16=1 ∨ (v.1*v.2)%16=5)
      else S.filter (fun v => v.1%4=1 ∧ v.2%4=1 ∧ ((v.1*v.2)%16=1 ∨ (v.1*v.2)%16=5))).card := by
  cases k <;> simp [nat_mark,markProp,and_assoc]

private theorem share_eq (k : Bool) : FiveSquareAllPrimeRanks.actual (mark k) =
    ((selected k).card:ℝ)/eligible.card := by
  unfold FiveSquareAllPrimeRanks.actual
  rw [share_counts]
  cases k <;> rfl

open private PrimeFactors.FiveSquareActualRanks.error_bound from PrimeFactors.FiveSquareActualRanks

/-- A weighted mean of a nonnegative cost differs from the uniform mean by
at most the latter mean times the relative spread of the weights. -/
private theorem relative {α : Type*} [Fintype α] [Nonempty α] (w c : α→ℝ) {l u f : ℝ}
    (lp : 0<l) (fp : 0<f) (scale : f*u≤(f+1)*l)
    (weights : ∀ a,l≤w a ∧ w a≤u) (nn : ∀ a,0≤c a) :
    |(∑ a,w a*c a)/(∑ a,w a)-(∑ a,c a)/Fintype.card α|≤((∑ a,c a)/Fintype.card α)/f := by
  let n : ℝ := Fintype.card α
  have np : 0<n := by dsimp only [n]; exact_mod_cast (Fintype.card_pos : 0<Fintype.card α)
  have up := lp.trans_le ((weights (Classical.choice ‹Nonempty α›)).1.trans (weights _).2)
  have sums (g : α→ℝ) (gn : ∀ a,0≤g a) :
      l*(∑ a,g a)≤∑ a,w a*g a ∧ (∑ a,w a*g a)≤u*(∑ a,g a) := by
    simp only [mul_sum]
    exact ⟨sum_le_sum (fun a _ => mul_le_mul_of_nonneg_right (weights a).1 (gn a)),
      sum_le_sum (fun a _ => mul_le_mul_of_nonneg_right (weights a).2 (gn a))⟩
  have costs := sums c nn
  have mass : l*n≤∑ a,w a ∧ (∑ a,w a)≤u*n := by
    simpa [n] using sums (fun _ => 1) (fun _ => zero_le_one)
  have cp : 0≤∑ a,c a := sum_nonneg (fun a _ => nn a)
  have mp : 0≤∑ a,w a*c a := sum_nonneg (fun a _ => mul_nonneg (lp.le.trans (weights a).1) (nn a))
  have pos := (mul_pos lp np).trans_le mass.1
  exact PrimeFactors.FiveSquareActualRanks.error_bound lp up fp scale (div_nonneg cp np.le)
    (by rw [div_mul_div_comm]; exact div_le_div₀ mp costs.1 pos mass.2)
    (by rw [div_mul_div_comm]; exact div_le_div₀ (mul_nonneg up.le cp) costs.2 (mul_pos lp np) mass.1)

private theorem close_of_cells (k : Bool) {F l u : ℕ} (lp : 0<l) (fp : 0<F) (scale : F*u≤(F+1)*l)
    (weights : ∀ v : Units16, l≤cell X B K (v.1.val,v.2.val) ∧ cell X B K (v.1.val,v.2.val)≤u) :
    |((selected k).card:ℝ)/eligible.card-(if k then 1/4 else 1/8)|≤(if k then 1/4 else 1/8)/(F:ℝ) := by
  let w (v : Units16) : ℝ := cell X B K (v.1.val,v.2.val)
  let c (v : Units16) : ℝ := mark k v.1 v.2
  have cMean : (∑ v,c v)/Fintype.card Units16=(if k then (1:ℝ)/4 else 1/8) := by
    cases k <;> norm_num [c,←Nat.cast_sum,census.1,census.2.1,census.2.2]
  rw [←share_eq,PrimeFactors.FiveSquareAllPrimeRanks.actual_weighted (mark k) (sym k)
    (PrimeFactors.ExtendedProductCosts.unit_of_prime (by decide)),←cMean]
  apply relative w c (l:=(l:ℝ)) (u:=(u:ℝ))
    (by exact_mod_cast lp) (by exact_mod_cast fp) (by exact_mod_cast scale)
  · exact fun v => ⟨Nat.cast_le.mpr (weights v).1,Nat.cast_le.mpr (weights v).2⟩
  · exact fun _ => Nat.cast_nonneg _

/-- EHP Corollary 2 under Dirichlet GRH, applied to modulus 16. -/
theorem close_ehp {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints 16 li) :
    |(locus.card:ℝ)/eligible.card-1/8|≤1/(2:ℝ)^146 := by
  obtain ⟨l,u,lp,scale,weights⟩ := ExtendedModulusPrimeSupply.cell_bounds (by decide) (by decide) h
  have small : |(locus.card:ℝ)/eligible.card-1/8|≤(1/8)/(2:ℝ)^146 := by
    exact_mod_cast close_of_cells false lp (by decide : 0<2^146) scale weights
  exact small.trans (by norm_num)

/-- The two public product remainders together occur on one quarter of all
eligible pairs, to the stated EHP accuracy. -/
theorem last_close_ehp {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints 16 li) :
    |(lastBits.card:ℝ)/eligible.card-1/4|≤1/(2:ℝ)^146 := by
  obtain ⟨l,u,lp,scale,weights⟩ := ExtendedModulusPrimeSupply.cell_bounds (by decide) (by decide) h
  have small : |(lastBits.card:ℝ)/eligible.card-1/4|≤(1/4)/(2:ℝ)^146 := by
    exact_mod_cast close_of_cells true lp (by decide : 0<2^146) scale weights
  exact small.trans (by norm_num)

open private PrimeFactors.PrimeGridMass.interval_error PrimeFactors.PrimeGridMass.increment_upper
  from PrimeFactors.PrimeGridMass
open private PrimeFactors.ExtendedModulusPrimeSupply.equivalent PrimeFactors.ExtendedModulusPrimeSupply.slice
  PrimeFactors.ExtendedModulusPrimeSupply.finite_bounds from PrimeFactors.ExtendedModulusPrimeSupply
open private PrimeFactors.PrimeProductRegion.cutoff from PrimeFactors.PrimeProductRegion
open private PrimeFactors.UnconditionalPrimePairSumFrequency.endpoint_cap
  from PrimeFactors.UnconditionalPrimePairSumFrequency

/-- Bennett–Martin–O'Bryant–Rechnitzer, Theorem 1.3 and equations 1.10–1.11
(https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5).
Its unconditional error bound applies to modulus 16 for x≥8·10⁹.
The logarithmic integral and prime-count estimates are explicit inputs. -/
structure BmorEndpoints (li : ℕ→ℝ) : Prop where
  integral (z : ℕ) (lo : X≤z) (hi : z≤B) : li B=li z+increment z (B-z)
  pointwise (a : ZMod 16) (unit : IsUnit a) (z : ℕ) (lo : X≤z) (hi : z≤B) :
    |((through 16 a.val z).card:ℝ)-li z/8|≤(z:ℝ)/(840*(Real.log z)^2)

theorem bmor_domain {z : ℕ} (lo : X≤z) : 16≤(10000:ℕ) ∧ 8000000000≤z :=
  ⟨by decide,(by decide : 8000000000≤X).trans lo⟩

private abbrev D := FullRangeResidueEstimates.bmorD
private abbrev U := B/11000
private abbrev M := B/23000
private noncomputable abbrev err := (B:ℝ)/(840*700^2)

private theorem bmor_center {li : ℕ→ℝ} (h : BmorEndpoints li) (a : ZMod 16) (unit : IsUnit a)
    {z : ℕ} (lo : X≤z) (hi : z≤B) :
    |((tail B z a).card:ℝ)-increment z (B-z)/8|≤2*err := by
  have bound := PrimeFactors.PrimeGridMass.interval_error (A:=z) (W:=B-z) lo
    (Nat.add_sub_of_le hi).le h.integral (h.pointwise a unit)
  have cap {s : ℕ} (low : X≤s) (high : s≤B) :
      (s:ℝ)/(840*(Real.log s)^2)≤err :=
    (PrimeFactors.UnconditionalPrimePairSumFrequency.endpoint_cap low).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast high) (by norm_num))
  rw [Nat.add_sub_of_le hi] at bound
  rw [PrimeFactors.ExtendedModulusPrimeSupply.equivalent a hi,two_mul]
  exact bound.trans (add_le_add (cap lo hi) (cap (lo.trans hi) le_rfl))

attribute [local irreducible] tail

private theorem bmor_cells {li : ℕ→ℝ} (h : BmorEndpoints li) :
    ∃ l u : ℕ, 0<l ∧ 1040*u≤(1040+1)*l ∧
      ∀ v : Units16,l≤cell X B K (v.1.val,v.2.val) ∧ cell X B K (v.1.val,v.2.val)≤u := by
  have combine {x y t e d : ℝ} (high : x-t≤2*e) (low : -(2*e)≤y-t) (round : 4*e<d+1) :
      x<y+d+1 := by linarith
  have top {v t w e u : ℝ} (high : v-t/8≤2*e) (intgr : t≤w/709) (margin : w/709/8+2*e≤u) :
      v≤u := by linarith
  have bot {v t w e m : ℝ} (low : -(2*e)≤v-t/8) (intgr : w/710≤t) (margin : m≤w/710/8-2*e) :
      m≤v := by linarith
  have suffix (a b : (ZMod 16)ˣ) {z : ℕ} (lo : X≤z) (hi : z≤B) :
      (tail B z a.val).card≤(tail B z b.val).card+D := by
    have right := (abs_le.mp (bmor_center h _ a.isUnit lo hi)).2
    have left := (abs_le.mp (bmor_center h _ b.isUnit lo hi)).1
    have round : 4*err<(D:ℝ)+1 := by norm_num [D,FullRangeResidueEstimates.bmorD,err,B]
    have joined : ((tail B z a.val).card:ℝ)<(tail B z b.val).card+D+1 := combine right left round
    exact Nat.le_of_lt_succ (by exact_mod_cast joined)
  have upper (a : (ZMod 16)ˣ) : (tail B X a.val).card≤U := by
    have right := (abs_le.mp (bmor_center h _ a.isUnit (z:=X) le_rfl (by decide))).2
    have integral := PrimeFactors.PrimeGridMass.increment_upper X (B-X) le_rfl
    have margin : ((B-X:ℕ):ℝ)/709/8+2*err≤U := by norm_num [U,X,B,err]
    exact_mod_cast top right integral margin
  have lower (a : (ZMod 16)ˣ) : M≤(tail B L a.val).card := by
    have left := (abs_le.mp (bmor_center h _ a.isUnit (z:=L) (by decide) (by decide))).1
    have integral := increment_lower (A:=L) (W:=B-L) (by decide) (by decide)
    have margin : (M:ℝ)≤((B-L:ℕ):ℝ)/710/8-2*err := by norm_num [M,L,B,err]
    exact_mod_cast bot left integral margin
  let count (v : Units16) := cell X B K (v.1.val,v.2.val)
  have floor (v : Units16) : M*(M-1)≤count v := by
    have sub (a : ZMod 16) : tail B L a ⊆ tail B X a := by
      intro p hp
      obtain ⟨lo,hi,pr,modp⟩ := mem_tail.mp hp
      exact mem_tail.mpr ⟨(by decide : X≤L).trans_lt lo,hi,pr,modp⟩
    dsimp only [count]
    unfold PrimeResidueRankTransfer.cell
    apply ThresholdPairCount.lower (lower v.1) (lower v.2) (sub _) (sub _)
    intro p hp q hq
    exact (by decide +kernel : K<L*L).trans_le (Nat.mul_le_mul (mem_tail.mp hp).1.le (mem_tail.mp hq).1.le)
  apply PrimeFactors.ExtendedModulusPrimeSupply.finite_bounds (1,1) count (2*D*U+U)
    (fun v => (by decide +kernel : 0<M*(M-1)).trans_le (floor v))
    (fun v => (by decide +kernel : 1040*(2*D*U+U)≤M*(M-1)).trans (floor v))
  intro v w
  dsimp only [count]
  unfold PrimeResidueRankTransfer.cell
  apply ThresholdPairCount.spread _ _ _ _ (upper v.1) (upper w.2) (upper w.1)
  · intro p hp
    obtain ⟨lo,hi,_,_⟩ := mem_tail.mp hp
    rw [PrimeFactors.ExtendedModulusPrimeSupply.slice _ lo hi,PrimeFactors.ExtendedModulusPrimeSupply.slice _ lo hi]
    exact suffix _ _ (PrimeFactors.PrimeProductRegion.cutoff lo hi).1 (PrimeFactors.PrimeProductRegion.cutoff lo hi).2
  · intro p hp
    obtain ⟨lo,hi,_,_⟩ := mem_tail.mp hp
    rw [PrimeFactors.ExtendedModulusPrimeSupply.slice _ lo hi,PrimeFactors.ExtendedModulusPrimeSupply.slice _ lo hi]
    exact suffix _ _ (PrimeFactors.PrimeProductRegion.cutoff lo hi).1 (PrimeFactors.PrimeProductRegion.cutoff lo hi).2

/-- The unconditional progression estimate suffices to place the full local
locus within 1/8320 of one eighth of eligible prime pairs. -/
theorem close_bmor {li : ℕ→ℝ} (h : BmorEndpoints li) :
    |(locus.card:ℝ)/eligible.card-1/8|≤1/8320 := by
  obtain ⟨l,u,lp,scale,weights⟩ := bmor_cells h
  exact (close_of_cells false lp (by decide : 0<1040) scale weights).trans (by norm_num)

/-- The analogous error for the two product remainders is at most 1/4160. -/
theorem last_close_bmor {li : ℕ→ℝ} (h : BmorEndpoints li) :
    |(lastBits.card:ℝ)/eligible.card-1/4|≤1/4160 := by
  obtain ⟨l,u,lp,scale,weights⟩ := bmor_cells h
  exact (close_of_cells true lp (by decide : 0<1040) scale weights).trans (by norm_num)

end PrimeFactors.QuarticLocalPopulation
