import PrimeFactors.QuarticLocalClassification
import PrimeFactors.ExtendedProductCosts

/-! Prime pairs conditioned on one fixed unit product residue. Negating both
coordinates pairs the two possible common residue classes modulo four. The
conditional frequency estimate uses only counts inside the specified fiber. -/
namespace PrimeFactors.QuarticLocalConditionalBits

open Finset
open MixedPrefixSample (eligible)
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open PrimeProductRegion (K)
open PrimeResidueRankTransfer (cell)
open private PrimeFactors.ExtendedProductCosts.unit_of_prime from PrimeFactors.ExtendedProductCosts
open private PrimeFactors.FiveSquareActualRanks.error_bound from PrimeFactors.FiveSquareActualRanks
open private PrimeFactors.FullPopulationFavoredSums.mem_eligible from PrimeFactors.FullPopulationFavoredSums
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

variable {m : ℕ} [NeZero m]

abbrev UnitPair (m : ℕ) := (ZMod m)ˣ × (ZMod m)ˣ

private noncomputable abbrev red (div : 4∣m) := ZMod.castHom div (ZMod 4)
private abbrev sign (div : 4∣m) (a b : ZMod m) := red div a=1 ∧ red div b=1
private abbrev keep (div : 4∣m) (r : (ZMod m)ˣ) (test : Bool) (a b : ZMod m) :=
  a*b=r.val ∧ (test=false ∨ sign div a b)

/-- Ordered unit-coordinate cells with the prescribed product. When test is
true both coordinates must additionally equal one modulo four. -/
noncomputable def cells (div : 4∣m) (r : (ZMod m)ˣ) (test : Bool) : Finset (UnitPair m) :=
  univ.filter fun v => keep div r test v.1.val v.2.val

/-- Actual distinct sorted prime pairs in the full-width region with the
specified product. The true flag additionally imposes the two factor signs. -/
noncomputable def population (div : 4∣m) (r : (ZMod m)ˣ) (test : Bool) : Finset (ℕ×ℕ) :=
  eligible.filter fun v => keep div r test v.1 v.2

private theorem cast_four (p : ℕ) : (p:ZMod 4)=1 ↔ p%4=1 := by
  change (p:ZMod 4)=((1:ℕ):ZMod 4) ↔ _
  rw [ZMod.natCast_eq_natCast_iff]
  rfl

omit [NeZero m] in
theorem mem_population {div : 4∣m} {r : (ZMod m)ˣ} {test : Bool} {p q : ℕ} :
    (p,q)∈population div r test ↔ (p,q)∈eligible ∧ ((p*q:ℕ):ZMod m)=r.val ∧
      (test=false ∨ p%4=1 ∧ q%4=1) := by
  simp only [population,mem_filter,keep,sign,red,map_natCast,cast_four,Nat.cast_mul]

private noncomputable abbrev negPair (v : UnitPair m) : UnitPair m := (-v.1,-v.2)

omit [NeZero m] in
private theorem flip (div : 4∣m) {r : (ZMod m)ˣ} (one : red div r.val=1)
    {a b : ZMod m} (eq : a*b=r.val) : sign div (-a) (-b) ↔ ¬sign div a b := by
  have table : ∀ x y : ZMod 4, x*y=1 → ((-x=1 ∧ -y=1) ↔ ¬(x=1 ∧ y=1)) := by decide
  have prod : red div a*red div b=1 := by rw [←map_mul,eq,one]
  simpa only [sign,map_neg] using table _ _ prod

/-- For each fixed unit product equal to one modulo four, half the cells have
both coordinates equal to one modulo four. -/
theorem half (div : 4∣m) (r : (ZMod m)ˣ) (one : ZMod.castHom div (ZMod 4) r.val=1) :
    2*(cells div r true).card=(cells div r false).card := by
  let S := cells div r false
  let good (v : UnitPair m) := sign div v.1.val v.2.val
  have memS (v : UnitPair m) : v∈S ↔ v.1.val*v.2.val=r.val := by simp [S,cells,keep]
  have fst : S.filter good=cells div r true := by
    ext v
    simp [memS,cells,keep,good]
  have eq : (S.filter good).card=(S.filter (fun v => ¬good v)).card := by
    apply card_nbij' negPair negPair
    · intro v hv
      obtain ⟨prod,g⟩ := mem_filter.mp hv
      have hit := (memS v).mp prod
      refine mem_filter.mpr ⟨(memS _).mpr (by simpa [negPair] using hit),?_⟩
      simpa only [good,negPair,Units.val_neg] using (fun o => (flip div one hit).mp o g)
    · intro v hv
      obtain ⟨prod,g⟩ := mem_filter.mp hv
      have hit := (memS v).mp prod
      refine mem_filter.mpr ⟨(memS _).mpr (by simpa [negPair] using hit),?_⟩
      exact (flip div one hit).mpr g
    all_goals intro v _; simp [negPair]
  have partition := filter_card_add_filter_neg_card_eq_card (s:=S) good
  rw [←eq,fst] at partition
  exact (two_mul _).trans partition

attribute [local irreducible] eligible cell

private theorem count_identity (div : 4∣m) (r : (ZMod m)ˣ) (t : Bool) (cap : m≤2^161) :
    2*(population div r t).card=
      ∑ v∈cells div r t, cell X B K (v.1.val,v.2.val) := by
  let cost (a b : ZMod m) := if keep div r t a b then 1 else 0
  have sym (a b : ZMod m) : cost a b=cost b a := by simp only [cost,keep,sign,mul_comm b a,and_comm]
  have w := FiveSquareAllPrimeRanks.twice_cost cost sym (PrimeFactors.ExtendedProductCosts.unit_of_prime cap)
  have reduce (S : Finset (ℕ×ℕ)) :
      (∑ z∈S, cost z.1 z.2)=(S.filter (fun v => keep div r t v.1 v.2)).card := by
    simp only [cost,sum_boole,Nat.cast_id]
  rw [reduce] at w
  simpa only [population,cells,cost,mul_ite,mul_one,mul_zero,sum_filter] using w

private theorem bounds (div : 4∣m) (r : (ZMod m)ˣ) (t : Bool) (cap : m≤2^161) {l u : ℕ}
    (ws : ∀ v : UnitPair m, l≤cell X B K (v.1.val,v.2.val) ∧ cell X B K (v.1.val,v.2.val)≤u) :
    l*(cells div r t).card≤2*(population div r t).card ∧
    2*(population div r t).card≤u*(cells div r t).card := by
  rw [count_identity div r t cap]
  let S := cells div r t
  have a := sum_le_sum (s:=S) (fun v _ => (ws v).1)
  have b := sum_le_sum (s:=S) (fun v _ => (ws v).2)
  simpa only [S,sum_const,nsmul_eq_mul,Nat.cast_id,mul_comm l,mul_comm u] using And.intro a b

private theorem transfer {a s c d l u f : ℕ} (cp : 0<c) (lp : 0<l) (fp : 0<f)
    (scale : f*u≤(f+1)*l) (half : 2*c=d)
    (x : l*c≤2*a ∧ 2*a≤u*c) (y : l*d≤2*s ∧ 2*s≤u*d) :
    0<s ∧ |(a:ℝ)/s-1/2|≤(1/2)/(f:ℝ) := by
  subst d
  have sp : 0<s := by have := (Nat.mul_pos lp (Nat.mul_pos (by decide : 0<2) cp)).trans_le y.1; omega
  have up : 0<u := Nat.pos_of_mul_pos_right (((Nat.mul_pos lp cp).trans_le x.1).trans_le x.2)
  refine ⟨sp,?_⟩
  have aa : (l:ℝ)*c≤2*a ∧ (2:ℝ)*a≤u*c := by exact_mod_cast x
  have ss : (l:ℝ)*(2*c)≤2*s ∧ (2:ℝ)*s≤u*(2*c) := by exact_mod_cast y
  apply PrimeFactors.FiveSquareActualRanks.error_bound (l:=(l:ℝ)) (u:=(u:ℝ)) (by exact_mod_cast lp) (by exact_mod_cast up)
    (by exact_mod_cast fp) (by exact_mod_cast scale) (by norm_num)
  · rw [div_mul_div_comm]
    apply (div_le_div_iff₀ (mul_pos (by exact_mod_cast up) (by norm_num)) (by exact_mod_cast sp)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left ss.2 (Nat.cast_nonneg l : (0:ℝ)≤l),
      mul_le_mul_of_nonneg_right aa.1 (Nat.cast_nonneg u : (0:ℝ)≤u)]
  · rw [div_mul_div_comm]
    apply (div_le_div_iff₀ (by exact_mod_cast sp) (mul_pos (by exact_mod_cast lp) (by norm_num))).mpr
    nlinarith only [mul_le_mul_of_nonneg_left ss.1 (Nat.cast_nonneg u : (0:ℝ)≤u),
      mul_le_mul_of_nonneg_right aa.2 (Nat.cast_nonneg l : (0:ℝ)≤l)]

/-- Conditional error at a single prescribed unit product residue. Its
conditioning class has positive mass in the full-width prime population. -/
theorem conditional {li : ℕ→ℝ} (div : 4∣m) (low : 3≤m) (cap : m≤2^161)
    (h : ExtendedModulusPrimeSupply.Endpoints m li) (r : (ZMod m)ˣ)
    (one : ZMod.castHom div (ZMod 4) r.val=1) :
    0<(population div r false).card ∧
    |((population div r true).card:ℝ)/(population div r false).card-1/2|≤1/(2:ℝ)^147 := by
  have nonempty : (1,r)∈cells div r true := by
    apply mem_filter.mpr
    exact ⟨mem_univ _,one_mul _,Or.inr ⟨map_one _,one⟩⟩
  obtain ⟨l,u,lp,scale,ws⟩ := ExtendedModulusPrimeSupply.cell_bounds low cap h
  obtain ⟨pos,close⟩ := transfer (card_pos.mpr ⟨_,nonempty⟩) lp (by decide : 0<2^146)
    scale (half div r one) (bounds div r true cap ws) (bounds div r false cap ws)
  exact ⟨pos,close.trans (by norm_num)⟩

open scoped Classical

private theorem mod16_of_mem {r : (ZMod m)ˣ} {z : ℕ} (div : 16∣m)
    (eq : (z:ZMod m)=r.val) : z%16=r.val.val%16 := by
  have p := (ZMod.natCast_eq_natCast_iff z r.val.val m).mp (eq.trans (ZMod.natCast_zmod_val r.val).symm)
  exact p.of_dvd div

/-- The pairs counted in the numerator are exactly those passing all finite
quartic congruence tests when the specified product ends in one or five. -/
theorem passing {div : 4∣m} (sixteen : 16∣m) (r : (ZMod m)ˣ)
    (retain : r.val.val%16=1 ∨ r.val.val%16=5) :
    population div r true = (population div r false).filter
      (fun z => QuarticLocalClassification.Tests (z.1*z.2)) := by
  classical
  ext ⟨p,q⟩
  by_cases ok : (p,q)∈eligible
  · obtain ⟨lo,lt,_,pp,qp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp ok
    by_cases eq : ((p*q:ℕ):ZMod m)=r.val
    · have a := mod16_of_mem sixteen eq
      have product : (p*q)%16=1 ∨ (p*q)%16=5 := a ▸ retain
      have big : 2<X := by decide
      have po := pp.odd_of_ne_two (big.trans_le lo).ne'
      have qo := qp.odd_of_ne_two ((big.trans_le lo).trans lt).ne'
      simp [mem_population,ok,eq,QuarticLocalClassification.semiprime pp qp po qo,product]
    · rw [Nat.cast_mul] at eq
      simp [mem_population,eq]
  · simp [mem_population,ok]

/-- After conditioning on any specified retained unit product remainder,
passing all local tests still has frequency within 2⁻¹⁴⁷ of one half under
the given modulus-specific Dirichlet-GRH prime-count estimates. -/
theorem tests_conditional {li : ℕ→ℝ} (sixteen : 16∣m) (cap : m≤2^161)
    (h : ExtendedModulusPrimeSupply.Endpoints m li) (r : (ZMod m)ˣ)
    (retain : r.val.val%16=1 ∨ r.val.val%16=5) :
    let div := (by decide : 4∣16).trans sixteen
    let S := population div r false
    0<S.card ∧ |((S.filter (fun z => QuarticLocalClassification.Tests (z.1*z.2))).card:ℝ)/S.card-1/2|≤1/(2:ℝ)^147 := by
  dsimp only
  let div := (by decide : 4∣16).trans sixteen
  have one : red div r.val=1 := by
    have nat : r.val.val%4=1 := by omega
    calc
      red div r.val = red div ((r.val.val:ℕ):ZMod m) := by rw [ZMod.natCast_zmod_val]
      _ = (r.val.val:ZMod 4) := map_natCast ..
      _ = 1 := (cast_four _).mpr nat
  rw [←passing sixteen r retain]
  exact conditional div ((by decide : 3≤16).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m)) sixteen)) cap h r one

/-- Specialization to a known string of 160 least significant product bits. -/
theorem low160 {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints (2^160) li)
    (r : (ZMod (2^160))ˣ) (retain : r.val.val%16=1 ∨ r.val.val%16=5) :
    let S := population (by decide +kernel : 4∣2^160) r false
    0<S.card ∧ |((S.filter (fun z => QuarticLocalClassification.Tests (z.1*z.2))).card:ℝ)/S.card-1/2|≤1/(2:ℝ)^147 :=
  tests_conditional (by decide +kernel : 16∣2^160) (by decide +kernel) h r retain

end PrimeFactors.QuarticLocalConditionalBits
