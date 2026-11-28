import PrimeFactors.FiveSquareActualRanks
import PrimeFactors.FullPopulationFavoredSums

/-! Means of bounded symmetric costs on the entire balanced prime population,
including all product residues, at the five-prime modulus. -/
namespace PrimeFactors.FiveSquareAllPrimeRanks

open Finset FiveSquarePrimeSupply PrimeResidueRankTransfer
open FullRangeResidueEstimates (X)
open PrimeProductRegion (K)
open WideResiduePrimeSupply (B)
open MixedPrefixSample (eligible)
open scoped Classical

open private PrimeFactors.PrimeProductRegion.whole PrimeFactors.PrimeProductRegion.pool
  PrimeFactors.PrimeProductRegion.mem_whole PrimeFactors.PrimeProductRegion.mem_pool from PrimeFactors.PrimeProductRegion
open private PrimeFactors.FullPopulationFavoredSums.ordered_card from PrimeFactors.FullPopulationFavoredSums
open private PrimeFactors.FiveSquareActualRanks.error_bound from PrimeFactors.FiveSquareActualRanks

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

abbrev UnitPair := (ZMod m)ˣ × (ZMod m)ˣ
private abbrev raw {d : ℕ} (x : (ZMod d)ˣ × (ZMod d)ˣ) : ZMod d × ZMod d := (x.1,x.2)
private noncomputable abbrev coords {d : ℕ} (v : ℕ×ℕ) : ZMod d × ZMod d := (v.1,v.2)

attribute [local irreducible] PrimeFactors.PrimeProductRegion.whole eligible

private theorem weighted_from_counts {α : Type*} [DecidableEq α] (W S : Finset α) (f : α→ℕ)
    (counts : ∀ k,(W.filter (fun z => f z=k)).card=2*(S.filter (fun z => f z=k)).card) :
    (∑ z∈W,f z)=2*∑ z∈S,f z := by
  let tags := (W∪S).image f
  have mw (z : α) (h : z∈W) : f z∈tags := mem_image_of_mem f (mem_union_left S h)
  have ms (z : α) (h : z∈S) : f z∈tags := mem_image_of_mem f (mem_union_right W h)
  have w := sum_fiberwise_of_maps_to' mw id
  have s := sum_fiberwise_of_maps_to' ms id
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,id_eq] at w s
  rw [←w,←s,mul_sum]
  exact sum_congr rfl (fun k _ => by rw [counts,mul_assoc])

private theorem weighted_twice (f : ℕ×ℕ → ℕ) (sym : ∀ p q, f (p,q)=f (q,p)) :
    (∑ z∈PrimeFactors.PrimeProductRegion.whole,f z)=2*∑ z∈eligible,f z :=
  weighted_from_counts _ _ f (fun k => PrimeFactors.FullPopulationFavoredSums.ordered_card
    (fun z => f z=k) (fun p q h => (sym p q).symm.trans h))

private theorem prime_unit {p : ℕ} (lo : X<p) (P : p.Prime) : IsUnit (p:ZMod m) := by
  apply (ZMod.isUnit_iff_coprime p m).mpr
  apply P.coprime_iff_not_dvd.mpr
  have bound : m≤X := by rw [show m=7239457225 from FiveSquareGuessRanks.modulus_value]; decide +kernel
  exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (NeZero.ne m)) (bound.trans_lt lo)

private theorem fiber {d : ℕ} [NeZero d] (v : ZMod d × ZMod d) :
    ((PrimeFactors.PrimeProductRegion.whole).filter fun z => coords z=v).card=cell X B K v := by
  apply congrArg Finset.card
  ext ⟨p,q⟩
  simp only [mem_filter,PrimeFactors.PrimeProductRegion.mem_whole,PrimeFactors.PrimeProductRegion.mem_pool,
    coords,Prod.mk.injEq,ThresholdPairCount.distinctRegion,ThresholdPairCount.region,mem_product,mem_tail]
  cases v
  simp only [Prod.mk.injEq]
  tauto

attribute [local irreducible] cell CoprimeGuessTables.modulus Fintype.card

private theorem regroup {α β γ : Type*} [Fintype β] [DecidableEq γ] (S : Finset α)
    (g : α→γ) (r : β→γ) (inj : Function.Injective r) (c : β→ℕ) (cost : γ→ℕ)
    (maps : ∀ z∈S,∃ b,r b=g z)
    (fib : ∀ b,(S.filter (fun z => g z=r b)).card=c b) :
    (∑ z∈S,cost (g z))=∑ b,c b*cost (r b) := by
  let U := univ.image r
  have into (z) (h : z∈S) : g z∈U := by
    obtain ⟨b,eq⟩ := maps z h
    exact mem_image.mpr ⟨b,mem_univ b,eq⟩
  have groups := sum_fiberwise_of_maps_to' (s:=S) (t:=U) (g:=g) into cost
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at groups
  rw [←groups]
  unfold U
  rw [sum_image (fun _ _ _ _ h => inj h)]
  simp only [fib]

/-- Exact partition of the whole prime population by ordered unit residue
pairs. Swapping actual primes accounts for the factor two on the left. -/
theorem twice_cost {d : ℕ} [NeZero d] (cost : ZMod d→ZMod d→ℕ) (sym : ∀ a b, cost a b=cost b a)
    (good : ∀ {p : ℕ}, X<p → p.Prime → IsUnit (p:ZMod d)) :
    2*(∑ z∈eligible,cost z.1 z.2)=∑ v : (ZMod d)ˣ×(ZMod d)ˣ, cell X B K (raw v)*cost v.1 v.2 := by
  rw [←weighted_twice (fun z => cost z.1 z.2) (fun p q => sym p q)]
  apply regroup PrimeFactors.PrimeProductRegion.whole (coords (d:=d)) raw _
    (fun v => cell X B K (raw v)) (fun x => cost x.1 x.2)
  · rintro ⟨x,y⟩ h
    obtain ⟨p,q,_⟩ := (PrimeFactors.PrimeProductRegion.mem_whole (p:=x) (q:=y)).mp h
    obtain ⟨lo,_,P⟩ := PrimeFactors.PrimeProductRegion.mem_pool.mp p
    obtain ⟨lo',_,Q⟩ := PrimeFactors.PrimeProductRegion.mem_pool.mp q
    have a := good lo P
    have b := good lo' Q
    exact ⟨(a.unit,b.unit),Prod.ext a.unit_spec b.unit_spec⟩
  · exact fun v => fiber (raw v)
  · exact fun x y eq => Prod.ext (Units.ext (congrArg Prod.fst eq)) (Units.ext (congrArg Prod.snd eq))

/-- Mean over every sorted pair of distinct 1,024-bit primes with 2,048-bit
product. The cost may use both the product and sum residues. -/
noncomputable def actual {d : ℕ} [NeZero d] (cost : ZMod d→ZMod d→ℕ) : ℝ :=
  ((∑ z∈eligible,cost z.1 z.2:ℕ):ℝ)/eligible.card

/-- Mean when both factor residues are uniform, independent units. -/
noncomputable def uniform (cost : ZMod m→ZMod m→ℕ) : ℝ :=
  ((∑ v : UnitPair,cost v.1 v.2:ℕ):ℝ)/Fintype.card UnitPair

private theorem average_eq {α β : Type*} [Fintype β] (S : Finset α) (g : α→ℕ) (w c : β→ℕ)
    (a : 2*(∑ z∈S,g z)=∑ v,w v*c v) (b : 2*S.card=∑ v,w v) :
    ((∑ z∈S,g z:ℕ):ℝ)/S.card=(∑ v,(w v:ℝ)*c v)/(∑ v,(w v:ℝ)) := by
  have a' : (2:ℝ)*((∑ z∈S,g z:ℕ):ℝ)=∑ v,(w v:ℝ)*c v := by exact_mod_cast a
  have b' : (2:ℝ)*(S.card:ℝ)=∑ v,(w v:ℝ) := by exact_mod_cast b
  rw [←a',←b',mul_div_mul_left _ _ (by norm_num : (2:ℝ)≠0)]

private theorem card_of_ones {α β : Type*} [Fintype β] (S : Finset α) (w : β→ℕ)
    (ones : 2*(∑ _z∈S,(1:ℕ))=∑ v,w v*1) : 2*S.card=∑ v,w v := by
  simpa using ones

private theorem actual_weighted {d : ℕ} [NeZero d] (cost : ZMod d→ZMod d→ℕ)
    (sym : ∀ a b, cost a b=cost b a) (good : ∀ {p : ℕ}, X<p → p.Prime → IsUnit (p:ZMod d)) :
    actual cost = (∑ v : (ZMod d)ˣ×(ZMod d)ˣ,(cell X B K (raw v):ℝ)*cost v.1 v.2)/
      ∑ v : (ZMod d)ˣ×(ZMod d)ˣ,(cell X B K (raw v):ℝ) :=
  average_eq (β:=(ZMod d)ˣ×(ZMod d)ˣ) eligible (fun z => cost z.1 z.2) (fun v => cell X B K (raw v))
    (fun v => cost v.1 v.2) (twice_cost cost sym good)
    (card_of_ones eligible (fun v : (ZMod d)ˣ×(ZMod d)ˣ => cell X B K (raw v))
      (twice_cost (d:=d) (fun _ _ => 1) (fun _ _ => rfl) good))

private theorem all_bounds {li : ℕ→ℝ} (h : Endpoints li) :
    ∃ l u : ℕ, 0<l ∧ F*u≤(F+1)*l ∧
      ∀ v : UnitPair, l≤cell X B K (raw v) ∧ cell X B K (raw v)≤u := by
  obtain ⟨v,_,least⟩ := univ.exists_min_image (fun v : UnitPair => cell X B K (raw v)) univ_nonempty
  let l := cell X B K (raw v)
  have floor := lower h (v:=raw v) v.1.isUnit v.2.isUnit
  have fit : F*(2*D*B+B)≤M*(M-1) := by decide +kernel
  have pos : 0<l := (by decide +kernel : 0<M*(M-1)).trans_le floor
  refine ⟨l,l+(2*D*B+B),pos,?_,?_⟩
  · rw [Nat.mul_add,Nat.add_mul,one_mul]
    exact Nat.add_le_add_left (fit.trans floor) _
  intro a
  exact ⟨least _ (mem_univ _),spread h (v:=raw a) (w:=raw v) a.1.isUnit a.2.isUnit v.1.isUnit v.2.isUnit⟩

private theorem reweight {α : Type*} [Fintype α] [Nonempty α] (w c : α→ℝ)
    {l u f T : ℝ} (lp : 0<l) (fp : 0<f) (scale : f*u≤(f+1)*l)
    (weights : ∀ a,l≤w a ∧ w a≤u) (costs : ∀ a,0≤c a ∧ c a≤T) :
    |(∑ a,w a*c a)/(∑ a,w a)-(∑ a,c a)/Fintype.card α|≤T/f := by
  let N : ℝ := Fintype.card α
  have np : 0<N := by dsimp [N]; exact_mod_cast (Fintype.card_pos : 0<Fintype.card α)
  have up : 0<u := lp.trans_le ((weights (Classical.choice ‹Nonempty α›)).1.trans (weights _).2)
  have s0 : 0≤∑ a,c a := sum_nonneg (fun a _ => (costs a).1)
  have m0 : 0≤∑ a,w a*c a := sum_nonneg (fun a _ => mul_nonneg (lp.le.trans (weights a).1) (costs a).1)
  have low : l*(∑ a,c a) ≤ ∑ a,w a*c a := by
    rw [mul_sum]
    exact sum_le_sum (fun a _ => mul_le_mul_of_nonneg_right (weights a).1 (costs a).1)
  have high : (∑ a,w a*c a) ≤ u*(∑ a,c a) := by
    rw [mul_sum]
    exact sum_le_sum (fun a _ => mul_le_mul_of_nonneg_right (weights a).2 (costs a).1)
  have dw : l*N≤∑ a,w a := by
    simpa only [N,sum_const,card_univ,nsmul_eq_mul,mul_comm l] using sum_le_sum (s:=univ) (fun a _ => (weights a).1)
  have uw : (∑ a,w a)≤u*N := by
    simpa only [N,sum_const,card_univ,nsmul_eq_mul,mul_comm u] using sum_le_sum (s:=univ) (fun a _ => (weights a).2)
  have wp := (mul_pos lp np).trans_le dw
  have maxmean : (∑ a,c a)/N ≤ T := by
    apply (div_le_iff₀ np).mpr
    simpa only [N,sum_const,card_univ,nsmul_eq_mul,mul_comm T] using sum_le_sum (s:=univ) (fun a _ => (costs a).2)
  have err := @PrimeFactors.FiveSquareActualRanks.error_bound l u f ((∑ a,c a)/N)
    ((∑ a,w a*c a)/(∑ a,w a)) lp up fp scale (div_nonneg s0 np.le)
    (by rw [div_mul_div_comm]; exact div_le_div₀ m0 low wp uw)
    (by rw [div_mul_div_comm]; exact div_le_div₀ (mul_nonneg up.le s0) high (mul_pos lp np) dw)
  exact err.trans (div_le_div_of_nonneg_right maxmean fp.le)

/-- Absolute uniform-to-prime error for a bounded symmetric cost, retaining
the explicit cell-spread denominator for small differences of means. -/
theorem every_cost_bound {li : ℕ→ℝ} (h : Endpoints li) (cost : ZMod m→ZMod m→ℕ)
    (sym : ∀ a b, cost a b=cost b a) (bound : ∀ a b : (ZMod m)ˣ, cost a b≤2^33) :
    |actual cost-uniform cost|≤(2:ℝ)^33/F := by
  obtain ⟨l,u,lp,ratio,cells⟩ := all_bounds h
  rw [actual_weighted cost sym prime_unit,uniform,Nat.cast_sum]
  have cap (v : UnitPair) : 0≤(cost v.1 v.2:ℝ) ∧ (cost v.1 v.2:ℝ)≤(2:ℝ)^33 :=
    ⟨Nat.cast_nonneg _,by exact_mod_cast bound v.1 v.2⟩
  have lim := reweight (fun v : UnitPair => (cell X B K (raw v):ℝ)) (fun v => (cost v.1 v.2:ℝ))
    (by exact_mod_cast lp : 0<(l:ℝ)) (by positivity : 0<(F:ℝ)) (by exact_mod_cast ratio : (F:ℝ)*u≤((F:ℝ)+1)*l)
    (fun v => ⟨Nat.cast_le.mpr (cells v).1,Nat.cast_le.mpr (cells v).2⟩) cap
  exact lim

/-- The actual and uniform-unit means differ by less than one thousandth
for every symmetric cost bounded by 2^33 on unit residues, under the stated
five-modulus prime-counting endpoint estimates. -/
theorem every_cost {li : ℕ→ℝ} (h : Endpoints li) (cost : ZMod m→ZMod m→ℕ)
    (sym : ∀ a b, cost a b=cost b a) (bound : ∀ a b : (ZMod m)ˣ, cost a b≤2^33) :
    |actual cost-uniform cost|<1/1000 := by
  exact (every_cost_bound h cost sym bound).trans_lt (by norm_num [F])

end PrimeFactors.FiveSquareAllPrimeRanks
