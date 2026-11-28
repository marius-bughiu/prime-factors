import PrimeFactors.FiveSquareSignRanks
import PrimeFactors.FiveSquareAllPrimeRanks

/-! Choosing the order of sum guesses after observing the product residue.
Both factor residues are independent uniform units before the product is read. -/

namespace PrimeFactors.FiveSquarePolicy

open Finset PrimeSquareSumWeights
open FiveSquarePrimeSupply (m)
open FiveSquareSignRanks (Labels sign labels mean baseline meanRank optimum local_units)
open FiveSquareGuessRanks (score)
open FiveSquareAllPrimeRanks (uniform)
open scoped Classical

abbrev U := (ZMod m)ˣ
abbrev Policy := ∀ r : ZMod m, Fin (Fintype.card (Labels r.val)) ≃ Labels r.val

private noncomputable def rank (policy : Policy) (r s : ZMod m) :=
  if h : AdmissibleSum (r.val:ZMod m) s then ((policy r).symm ⟨s,h⟩).val+1 else 0

/-- The observed product selects the list, and the sum selects the rank in it. -/
noncomputable def cost (policy : Policy) (a b : ZMod m) := rank policy (a*b) (a+b)

theorem cost_sym (policy : Policy) (a b : ZMod m) : cost policy a b=cost policy b a := by
  rw [cost,cost,mul_comm a b,add_comm a b]

private theorem card_bound (n : ℕ) : Fintype.card (Labels n)≤m := by
  rw [←ZMod.card m]
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

theorem cost_bound (policy : Policy) (a b : U) : cost policy a b≤2^33 := by
  unfold cost rank
  split_ifs with h
  · exact (Nat.succ_le_of_lt (Fin.isLt _)).trans ((card_bound _).trans
      (FiveSquareGuessRanks.modulus_value.le.trans (by decide : 7239457225≤2^33)))
  · exact Nat.zero_le _

private theorem by_label {d : ℕ} [NeZero d] (n : ℕ) (f : ZMod d→ℕ) :
    (∑ v : Pairs n d,f (sumOf v))=∑ s : CoprimeGuessTables.Labels d n, weight n s.val*f s.val := by
  let label (v : Pairs n d) : CoprimeGuessTables.Labels d n :=
    ⟨sumOf v,v.val.1,v.val.2,v.property,rfl⟩
  have sizes (s : CoprimeGuessTables.Labels d n) :
      (univ.filter (fun v : Pairs n d => label v=s)).card=weight n s.val := by
    rw [weight,Nat.card_eq_fintype_card,Fintype.card_subtype]
    apply congrArg Finset.card
    ext v
    simp only [mem_filter,mem_univ,true_and,Subtype.ext_iff,label]
  have eq := sum_fiberwise_of_maps_to' (s:=univ) (fun v _ => mem_univ (label v))
    (fun s : CoprimeGuessTables.Labels d n => f s.val)
  simpa only [sum_const,nsmul_eq_mul,sizes,label] using eq.symm

private theorem prod_id {d : ℕ} (a u : (ZMod d)ˣ) :
    (a:ZMod d)*((a⁻¹*u : (ZMod d)ˣ):ZMod d)=(u:ZMod d) := by
  rw [←Units.val_mul]
  simp

/-- The first factor determines its partner uniquely once the unit product is given. -/
private noncomputable def fiber {d : ℕ} [NeZero d] (u : (ZMod d)ˣ) : (ZMod d)ˣ ≃ Pairs u.val.val d := by
  let make (a : (ZMod d)ˣ) : Pairs u.val.val d :=
    ⟨(a,(↑(a⁻¹*u) : ZMod d)),(prod_id a u).trans (ZMod.natCast_zmod_val _).symm⟩
  refine Equiv.ofBijective make ⟨fun a b h => Units.ext (congrArg (fun z : Pairs u.val.val d => z.val.1) h),?_⟩
  intro v
  have eq : v.val.1*v.val.2=u := v.property.trans (ZMod.natCast_zmod_val _)
  have unit : IsUnit v.val.1 := ((Commute.all _ _).isUnit_mul_iff.mp (eq ▸ u.isUnit)).1
  refine ⟨unit.unit,Subtype.ext (Prod.ext unit.unit_spec ?_)⟩
  change (↑(unit.unit⁻¹*u) : ZMod d)=v.val.2
  apply unit.mul_left_cancel
  calc v.val.1*↑(unit.unit⁻¹*u) = (u:ZMod d) := by simpa only [unit.unit_spec] using prod_id unit.unit u
       _ = _ := eq.symm

/-- Every unit product has exactly this many ordered unit-pair preimages. -/
theorem unit_count : Fintype.card U=3920716800 ∧ m.totient=3920716800 := by
  have pop : m.totient=3920716800 := by
    rw [show m=7239457225 from FiveSquareGuessRanks.modulus_value,
      show (7239457225:ℕ)=25*(49*(121*(169*289))) by decide,
      Nat.totient_mul (by decide : Nat.Coprime 25 (49*(121*(169*289)))),
      Nat.totient_mul (by decide : Nat.Coprime 49 (121*(169*289))),
      Nat.totient_mul (by decide : Nat.Coprime 121 (169*289)),
      Nat.totient_mul (by decide : Nat.Coprime 169 289)]
    decide +kernel
  exact ⟨(ZMod.card_units_eq_totient m).trans pop,pop⟩

/-- One-based conditional mean under the chosen list for the observed product. -/
noncomputable def localMean (policy : Policy) (u : U) : ℚ :=
  meanRank (fun s : Labels u.val.val => weight u.val.val s.val) (policy u.val)

private theorem row_score (policy : Policy) (u : U) :
    (∑ a : U,cost policy a ↑(a⁻¹*u))=score (fun s : Labels u.val.val => weight u.val.val s.val) (policy u.val) := by
  let r : ZMod m := u
  let e := policy r
  let f := rank policy r
  have point (a : U) : cost policy a ↑(a⁻¹*u)=f (sumOf (fiber u a)) := by
    unfold cost
    rw [prod_id]
    rfl
  have fiber_sum := (fiber u).sum_comp (fun v => f (sumOf v))
  simp_rw [point]
  rw [fiber_sum,by_label]
  have hit (s : Labels r.val) : f s.val=(e.symm s).val+1 := by
    dsimp only [f,rank,e]
    rw [dif_pos s.property]
  simp_rw [hit]
  rw [←e.sum_comp (fun s => weight r.val s.val*((e.symm s).val+1))]
  simp only [Equiv.symm_apply_apply]
  change (∑ i, weight r.val (e i).val*(i.val+1))=∑ i,(i.val+1)*weight r.val (e i).val
  apply sum_congr rfl
  intro i _
  exact Nat.mul_comm ..

private theorem change_product {G : Type*} [CommGroup G] [Fintype G] (f : G→G→ℕ) :
    (∑ v : G×G,f v.1 v.2)=∑ u : G, ∑ a : G, f a (a⁻¹*u) := by
  let e : G×G ≃ G×G := {
    toFun := fun v => (v.2,v.2⁻¹*v.1)
    invFun := fun v => (v.1*v.2,v.1)
    left_inv := fun v => by simp
    right_inv := fun v => by simp }
  rw [←e.sum_comp (fun v => f v.1 v.2),Fintype.sum_prod_type]
  rfl

private theorem val_unit {r : ZMod m} (h : IsUnit r) : IsUnit (r.val:ZMod m) := by
  rwa [ZMod.natCast_zmod_val]

private theorem row_mean (policy : Policy) (u : U) :
    localMean policy u=((∑ a : U, cost policy a ↑(a⁻¹*u) : ℕ):ℚ)/3920716800 := by
  have un : IsUnit (u.val.val:ZMod m) := val_unit u.isUnit
  have cnt := (FiveSquareSignRanks.histogram u.val.val (local_units un) id).trans
    (FiveSquareSignRanks.row_totals (sign u.val.val)).1
  unfold localMean meanRank
  rw [row_score]
  change _ / ((∑ s : Labels u.val.val,weight u.val.val s.val:ℕ):ℚ)=_
  rw [show (∑ s : Labels u.val.val,weight u.val.val s.val)=3920716800 from cnt]
  norm_num

private theorem normalize {α : Type*} [Fintype α] {N : ℕ} (pop : Fintype.card α=N)
    (work : α→ℕ) (mean0 : α→ℚ) (row : ∀ a, mean0 a=(work a:ℚ)/N) :
    ((∑ a,work a:ℕ):ℝ)/Fintype.card (α×α)=(((∑ a,mean0 a)/(N:ℚ):ℚ):ℝ) := by
  simp only [row,←sum_div,Fintype.card_prod,pop,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast,Nat.cast_sum,Nat.cast_mul]
  ring

/-- Uniform unit factors correspond to a uniform product and then a
uniform first factor at that product. -/
theorem uniform_eq (policy : Policy) :
    uniform (cost policy)=(((∑ u : U,localMean policy u)/3920716800:ℚ):ℝ) := by
  unfold uniform
  rw [change_product (fun a b : U => cost policy a b)]
  exact normalize unit_count.1 _ _ (row_mean policy)

private theorem product_unit (u : U) : ∀ i, ¬FiveSquareGuessRanks.primes i∣u.val.val :=
  local_units (val_unit u.isUnit)

theorem local_lower (policy : Policy) (u : U) :
    mean (sign u.val.val)≤localMean policy u :=
  (optimum u.val.val (product_unit u)).2.2 ⟨policy u.val,rfl⟩

/-- A single policy attains all the local optima simultaneously. -/
theorem optimal_family : ∃ policy : Policy, ∀ u : U, localMean policy u=mean (sign u.val.val) := by
  classical
  let e : Policy := fun r => if h : IsUnit r then
    Classical.choose (optimum r.val (local_units (val_unit h))).2.1
    else (Fintype.equivFin _).symm
  refine ⟨e,fun u => ?_⟩
  unfold localMean
  dsimp only [e]
  rw [dif_pos u.isUnit]
  exact Classical.choose_spec (optimum u.val.val (product_unit u)).2.1

/-- For each target the mean one-based rank in a random permutation is
(card+1)/2. Scaling by two keeps this symmetric cost natural-valued. -/
noncomputable def twiceRandom (a b : ZMod m) := Fintype.card (Labels (a*b).val)+1

theorem random_sym (a b : ZMod m) : twiceRandom a b=twiceRandom b a := by rw [twiceRandom,twiceRandom,mul_comm]

theorem random_bound (a b : U) : twiceRandom a b≤2^33 :=
  (Nat.add_le_add_right (card_bound _) 1).trans
    ((Nat.add_le_add_right (show m≤7239457225 from FiveSquareGuessRanks.modulus_value.le) 1).trans
      (by decide : 7239457225+1≤2^33))

theorem uniform_twiceRandom :
    uniform twiceRandom=(((2*(∑ u : U,baseline (sign u.val.val)))/3920716800:ℚ):ℝ) := by
  unfold uniform
  rw [change_product (fun a b : U => twiceRandom a b)]
  have each (u : U) : (∑ a : U, twiceRandom a ↑(a⁻¹*u))=
      3920716800*(labels (sign u.val.val)+1) := by
    simp only [twiceRandom,prod_id,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,unit_count.1,
      (optimum u.val.val (product_unit u)).1]
  have row (u : U) : 2*baseline (sign u.val.val)=
      ((∑ a : U,twiceRandom a ↑(a⁻¹*u):ℕ):ℚ)/3920716800 := by
    rw [each]
    simp only [baseline,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    ring
  rw [mul_sum]
  exact normalize unit_count.1 _ _ row

end PrimeFactors.FiveSquarePolicy
