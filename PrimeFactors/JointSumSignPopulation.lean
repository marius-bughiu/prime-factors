import PrimeFactors.QuarticLocalPopulation

/-! The joint signs of the two prime factors modulo three and four, conditioned
on their fixed product modulo 48. All counts concern the actual sorted
1,024-bit prime pairs with a 2,048-bit product. -/

namespace PrimeFactors.JointSumSignPopulation

open Finset WideResiduePrimeSupply PrimeResidueRankTransfer
open MixedPrefixSample (eligible)
open FullRangeResidueEstimates (X)
open PrimeProductRegion (K)
open private PrimeFactors.FiveSquareActualRanks.error_bound from PrimeFactors.FiveSquareActualRanks
open private PrimeFactors.ExtendedProductCosts.unit_of_prime from PrimeFactors.ExtendedProductCosts
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

abbrev Units48 := (ZMod 48)ˣ × (ZMod 48)ˣ

/-- The four possible product remainders congruent to one modulo twelve. -/
def productValue (r : Fin 4) : ℕ := 12*r.val+1

/-- Each of 1, 5, 7 and 11 modulo twelve codes one choice of the two signs. -/
def classValue (j : Fin 4) : ℕ := ![1,5,7,11] j

/-- For each class, use a lift whose square is one modulo 48. -/
def sumValue (r j : Fin 4) : ℕ := ((productValue r+1)*(![1,17,7,23] j))%48

private abbrev keep (r : Fin 4) (j : Option (Fin 4)) (a b : ZMod 48) :=
  a*b=(productValue r:ZMod 48) ∧ (match j with
    | none => True | some k => a.val%12=classValue k ∧ b.val%12=classValue k)

private noncomputable instance keepDec (r : Fin 4) (j : Option (Fin 4)) (a b : ZMod 48) : Decidable (keep r j a b) := by
  cases j <;> unfold keep <;> infer_instance

noncomputable def cells (r : Fin 4) (j : Option (Fin 4)) : Finset Units48 :=
  univ.filter fun v => keep r j v.1.val v.2.val

/-- With no label, this is the denominator of the conditional frequency.
A supplied label selects pairs whose primes have that common residue mod 12. -/
noncomputable def population (r : Fin 4) (j : Option (Fin 4)) : Finset (ℕ×ℕ) :=
  eligible.filter fun v => keep r j v.1 v.2

theorem census : ∀ r : Fin 4, (cells r none).card=16 ∧
    ∀ j : Fin 4, (cells r (some j)).card=4 := by decide +kernel

/-- The sum remainder identifies the common pair of signs in every product
cell. Each row uses four distinct sum remainders. -/
theorem sum_residues : (∀ r j : Fin 4, ∀ a b : ZMod 48, a*b=(productValue r:ZMod 48) →
    ((a.val%12=classValue j ∧ b.val%12=classValue j) ↔ (a+b).val=sumValue r j)) ∧
    (∀ r j k : Fin 4, sumValue r j=sumValue r k → j=k) := by decide +kernel

theorem exhaustive : ∀ r : Fin 4, ∀ a b : ZMod 48, a*b=(productValue r:ZMod 48) →
    ∃ j : Fin 4, (a+b).val=sumValue r j := by decide +kernel

/-- These are the two products satisfying both the mod-three sign condition
and the product-only quartic gate modulo sixteen. -/
theorem gate_rows :
    (productValue 0=1 ∧ ∀ j, sumValue 0 j = ![2,34,14,46] j) ∧
    (productValue 3=37 ∧ ∀ j, sumValue 3 j = ![38,22,26,10] j) := by decide +kernel

open private PrimeFactors.PrimeGridMass.interval_error PrimeFactors.PrimeGridMass.increment_upper
  from PrimeFactors.PrimeGridMass
open private PrimeFactors.ExtendedModulusPrimeSupply.equivalent PrimeFactors.ExtendedModulusPrimeSupply.slice
  PrimeFactors.ExtendedModulusPrimeSupply.finite_bounds from PrimeFactors.ExtendedModulusPrimeSupply
open private PrimeFactors.PrimeProductRegion.cutoff from PrimeFactors.PrimeProductRegion
open private PrimeFactors.UnconditionalPrimePairSumFrequency.endpoint_cap
  from PrimeFactors.UnconditionalPrimePairSumFrequency

/-- Bennett–Martin–O'Bryant–Rechnitzer, Theorem 1.3 and equations 1.10–1.11
(https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5).
Its unconditional error bound applies to modulus 48 for x≥8·10⁹.
The logarithmic integral and prime-count estimates are explicit inputs. -/
structure BmorEndpoints (li : ℕ→ℝ) : Prop where
  integral (z : ℕ) (lo : X≤z) (hi : z≤B) : li B=li z+increment z (B-z)
  pointwise (a : ZMod 48) (unit : IsUnit a) (z : ℕ) (lo : X≤z) (hi : z≤B) :
    |((through 48 a.val z).card:ℝ)-li z/16|≤(z:ℝ)/(840*(Real.log z)^2)

theorem bmor_domain {z : ℕ} (lo : X≤z) : 48≤(10000:ℕ) ∧ 8000000000≤z :=
  ⟨by decide,(by decide : 8000000000≤X).trans lo⟩

private abbrev D := FullRangeResidueEstimates.bmorD
private abbrev U := B/22000
private abbrev M := B/46000
private noncomputable abbrev err := (B:ℝ)/(840*700^2)

private theorem bmor_center {li : ℕ→ℝ} (h : BmorEndpoints li) (a : ZMod 48) (unit : IsUnit a)
    {z : ℕ} (lo : X≤z) (hi : z≤B) :
    |((tail B z a).card:ℝ)-increment z (B-z)/16|≤2*err := by
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
    ∃ l u : ℕ, 0<l ∧ 520*u≤(520+1)*l ∧
      ∀ v : Units48,l≤cell X B K (v.1.val,v.2.val) ∧ cell X B K (v.1.val,v.2.val)≤u := by
  have combine {x y t e d : ℝ} (high : x-t≤2*e) (low : -(2*e)≤y-t) (round : 4*e<d+1) :
      x<y+d+1 := by linarith
  have top {v t w e u : ℝ} (high : v-t/16≤2*e) (intgr : t≤w/709) (margin : w/709/16+2*e≤u) :
      v≤u := by linarith
  have bot {v t w e m : ℝ} (low : -(2*e)≤v-t/16) (intgr : w/710≤t) (margin : m≤w/710/16-2*e) :
      m≤v := by linarith
  have suffix (a b : (ZMod 48)ˣ) {z : ℕ} (lo : X≤z) (hi : z≤B) :
      (tail B z a.val).card≤(tail B z b.val).card+D := by
    have right := (abs_le.mp (bmor_center h _ a.isUnit lo hi)).2
    have left := (abs_le.mp (bmor_center h _ b.isUnit lo hi)).1
    have round : 4*err<(D:ℝ)+1 := by norm_num [D,FullRangeResidueEstimates.bmorD,err,B]
    have joined : ((tail B z a.val).card:ℝ)<(tail B z b.val).card+D+1 := combine right left round
    exact Nat.le_of_lt_succ (by exact_mod_cast joined)
  have upper (a : (ZMod 48)ˣ) : (tail B X a.val).card≤U := by
    have right := (abs_le.mp (bmor_center h _ a.isUnit (z:=X) le_rfl (by decide))).2
    have integral := PrimeFactors.PrimeGridMass.increment_upper X (B-X) le_rfl
    have margin : ((B-X:ℕ):ℝ)/709/16+2*err≤U := by norm_num [U,X,B,err]
    exact_mod_cast top right integral margin
  have lower (a : (ZMod 48)ˣ) : M≤(tail B L a.val).card := by
    have left := (abs_le.mp (bmor_center h _ a.isUnit (z:=L) (by decide) (by decide))).1
    have integral := increment_lower (A:=L) (W:=B-L) (by decide) (by decide)
    have margin : (M:ℝ)≤((B-L:ℕ):ℝ)/710/16-2*err := by norm_num [M,L,B,err]
    exact_mod_cast bot left integral margin
  let count (v : Units48) := cell X B K (v.1.val,v.2.val)
  have floor (v : Units48) : M*(M-1)≤count v := by
    have sub (a : ZMod 48) : tail B L a ⊆ tail B X a := by
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
    (fun v => (by decide +kernel : 520*(2*D*U+U)≤M*(M-1)).trans (floor v))
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


private theorem residue (r : Fin 4) (p q : ℕ) :
    (p:ZMod 48)*q=(productValue r:ZMod 48) ↔ (p*q)%48=productValue r := by
  have small : productValue r<48 := by dsimp [productValue]; omega
  rw [←Nat.cast_mul,ZMod.natCast_eq_natCast_iff]
  change _%48=_%48 ↔ _
  rw [Nat.mod_eq_of_lt small]

theorem mem_population {r : Fin 4} {j : Option (Fin 4)} {p q : ℕ} :
    (p,q)∈population r j ↔ (p,q)∈eligible ∧ (p*q)%48=productValue r ∧
      match j with | none => True | some k => p%12=classValue k ∧ q%12=classValue k := by
  cases j <;> simp only [population,mem_filter,keep,residue,ZMod.val_natCast,
    Nat.mod_mod_of_dvd _ (by decide : 12∣48)]

theorem sum_population (r j : Fin 4) : population r (some j)=
    (population r none).filter (fun v => (v.1+v.2)%48=sumValue r j) := by
  ext ⟨p,q⟩
  by_cases hit : (p*q)%48=productValue r
  · have both := sum_residues.1 r j p q ((residue r p q).mpr hit)
    simp only [←Nat.cast_add,ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 12∣48)] at both
    simp only [mem_filter,mem_population,hit,true_and,and_true,both]
  · simp [mem_population,hit]

attribute [local irreducible] eligible cell

private theorem bounds (r : Fin 4) (j : Option (Fin 4)) {l u : ℕ}
    (ws : ∀ v : Units48, l≤cell X B K (v.1.val,v.2.val) ∧ cell X B K (v.1.val,v.2.val)≤u) :
    l*(cells r j).card≤2*(population r j).card ∧
    2*(population r j).card≤u*(cells r j).card := by
  let cost (a b : ZMod 48) := if keep r j a b then 1 else 0
  have sym (a b : ZMod 48) : cost a b=cost b a := by cases j <;> simp only [cost,keep,mul_comm b a,and_comm]
  have w := FiveSquareAllPrimeRanks.twice_cost cost sym (PrimeFactors.ExtendedProductCosts.unit_of_prime (by decide))
  have reduce (S : Finset (ℕ×ℕ)) :
      (∑ z∈S, cost z.1 z.2)=(S.filter (fun v => keep r j v.1 v.2)).card := by
    simp only [cost,sum_boole,Nat.cast_id]
  rw [reduce] at w
  have eq : 2*(population r j).card=∑ v∈cells r j,cell X B K (v.1.val,v.2.val) := by
    simpa only [population,cells,cost,mul_ite,mul_one,mul_zero,sum_filter] using w
  rw [eq]
  have a := sum_le_sum (s:=cells r j) (fun v _ => (ws v).1)
  have b := sum_le_sum (s:=cells r j) (fun v _ => (ws v).2)
  simpa only [sum_const,nsmul_eq_mul,Nat.cast_id,mul_comm l,mul_comm u] using And.intro a b

private theorem transfer {a s l u : ℕ} (lp : 0<l) (scale : 520*u≤521*l)
    (x : l*4≤2*a ∧ 2*a≤u*4) (y : l*16≤2*s ∧ 2*s≤u*16) :
    0<s ∧ |(a:ℝ)/s-1/4|≤1/2080 := by
  have sp : 0<s := by omega
  have up : 0<u := by omega
  have aa : (l:ℝ)*4≤2*a ∧ (2:ℝ)*a≤u*4 := by exact_mod_cast x
  have ss : (l:ℝ)*16≤2*s ∧ (2:ℝ)*s≤u*16 := by exact_mod_cast y
  have us : (520:ℝ)*u≤(520+1)*l := by norm_num; exact_mod_cast scale
  have bound := @PrimeFactors.FiveSquareActualRanks.error_bound (l:ℝ) (u:ℝ) 520 (1/4) ((a:ℝ)/s)
    (by exact_mod_cast lp) (by exact_mod_cast up) (by norm_num) us (by norm_num)
  refine ⟨sp, (bound ?_ ?_).trans (by norm_num)⟩
  · rw [div_mul_div_comm]
    apply (div_le_div_iff₀ (mul_pos (by exact_mod_cast up) (by norm_num)) (by exact_mod_cast sp)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left ss.2 (Nat.cast_nonneg l : (0:ℝ)≤l),
      mul_le_mul_of_nonneg_right aa.1 (Nat.cast_nonneg u : (0:ℝ)≤u)]
  · rw [div_mul_div_comm]
    apply (div_le_div_iff₀ (by exact_mod_cast sp) (mul_pos (by exact_mod_cast lp) (by norm_num))).mpr
    nlinarith only [mul_le_mul_of_nonneg_left ss.1 (Nat.cast_nonneg u : (0:ℝ)≤u),
      mul_le_mul_of_nonneg_right aa.2 (Nat.cast_nonneg l : (0:ℝ)≤l)]

/-- For each prescribed product remainder and joint sign, its true population
share differs from a quarter by at most 1/2080 under the published
unconditional prime-count bounds. Every conditioning class is nonempty. -/
theorem conditional {li : ℕ→ℝ} (h : BmorEndpoints li) (r j : Fin 4) :
    0<(population r none).card ∧
    |((population r (some j)).card:ℝ)/(population r none).card-1/4|≤1/2080 := by
  obtain ⟨l,u,lp,scale,ws⟩ := bmor_cells h
  have good := bounds r (some j) ws
  have full := bounds r none ws
  rw [(census r).2 j] at good
  rw [(census r).1] at full
  exact transfer lp scale good full

theorem sum_frequency {li : ℕ→ℝ} (h : BmorEndpoints li) (r j : Fin 4) :
    let S := population r none
    0<S.card ∧ |((S.filter (fun v => (v.1+v.2)%48=sumValue r j)).card:ℝ)/S.card-1/4|≤1/2080 := by
  dsimp only
  rw [←sum_population]
  exact conditional h r j

/-- Choosing an arbitrary single sum remainder at this fixed public product
remainder can cover at most 1/4 + 1/2080 of the eligible prime pairs. -/
theorem one_sum_upper {li : ℕ→ℝ} (h : BmorEndpoints li) (r : Fin 4) (s : ℕ) :
    let S := population r none
    ((S.filter (fun v => (v.1+v.2)%48=s)).card:ℝ)/S.card≤1/4+1/2080 := by
  dsimp only
  by_cases known : ∃ j, sumValue r j=s
  · obtain ⟨j,rfl⟩ := known
    exact sub_le_iff_le_add'.mp (abs_le.mp (sum_frequency h r j).2).2
  · have empty : (population r none).filter (fun v => (v.1+v.2)%48=s)=∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      rintro ⟨p,q⟩ hit
      obtain ⟨ok,eq⟩ := mem_filter.mp hit
      have prod := (mem_population.mp ok).2.1
      obtain ⟨j,hr⟩ := exhaustive r p q ((residue r p q).mpr prod)
      simp only [←Nat.cast_add,ZMod.val_natCast] at hr
      exact known ⟨j,hr.symm.trans eq⟩
    rw [empty]
    norm_num

end PrimeFactors.JointSumSignPopulation
