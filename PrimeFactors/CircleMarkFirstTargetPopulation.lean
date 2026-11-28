import PrimeFactors.ExtendedProductCosts
import PrimeFactors.CircleMarkFirstTarget
import PrimeFactors.CircleMarkTargetFrequency

/-! Density of square unit residues and their negatives on the modulus used
for the first six prime Jacobi tests. Actual prime products are counted in
the canonical full-width population under explicit prime-count estimates. -/
namespace PrimeFactors.CircleMarkFirstTargetPopulation

open Finset
open MixedPrefixSample (eligible)
open private PrimeFactors.FullPopulationFavoredSums.mem_eligible from PrimeFactors.FullPopulationFavoredSums
open private PrimeFactors.ExtendedProductCosts.lift from PrimeFactors.ExtendedProductCosts

set_option maxRecDepth 4096
set_option exponentiation.threshold 2048

abbrev m : ℕ := CircleMarkFirstTarget.modulus

noncomputable def squares (d : ℕ) [NeZero d] : Finset (ZMod d)ˣ :=
  univ.image fun z : (ZMod d)ˣ => z^2

private theorem mem_squares {d : ℕ} [NeZero d] (z : (ZMod d)ˣ) :
    z∈squares d ↔ IsSquare z := by
  simp [squares,isSquare_iff_exists_sq,eq_comm]

private theorem square_val {d : ℕ} {z : (ZMod d)ˣ} : IsSquare z ↔ IsSquare z.val := by
  rw [isSquare_iff_exists_sq,isSquare_iff_exists_sq]
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨u.val,Units.val_pow_eq_pow_val ..⟩
  · rintro ⟨u,eqn⟩
    have unit : IsUnit u := (isUnit_pow_iff (by decide : 2≠0)).mp (eqn ▸ z.isUnit)
    exact ⟨unit.unit,Units.ext (by simpa only [Units.val_pow_eq_pow_val,IsUnit.unit_spec] using eqn)⟩

private theorem square_count_crt {a b : ℕ} [NeZero a] [NeZero b] (cop : a.Coprime b) :
    (squares (a*b)).card=(squares a).card*(squares b).card := by
  let e := (Units.mapEquiv (ZMod.chineseRemainder cop).toMulEquiv).trans MulEquiv.prodUnits
  have image : (squares (a*b)).map e.toEquiv.toEmbedding=(squares a)×ˢ(squares b) := by
    ext v
    obtain ⟨x,rfl⟩ := e.surjective v
    simp only [mem_map_equiv,Equiv.symm_apply_apply,MulEquiv.symm_apply_apply,mem_product,mem_squares,isSquare_iff_exists_sq]
    change (∃ r, e.symm (e x)=r^2) ↔ _
    rw [e.symm_apply_apply]
    constructor
    · rintro ⟨u,rfl⟩
      rw [map_pow]
      exact ⟨⟨(e u).1,rfl⟩,(e u).2,rfl⟩
    · rintro ⟨⟨l,hl⟩,r,hr⟩
      refine ⟨e.symm (l,r),e.injective ?_⟩
      rw [map_pow,e.apply_symm_apply]
      exact Prod.ext hl hr
  simpa only [card_map,card_product] using congrArg Finset.card image

private theorem square_total : (squares m).card=180 := by
  change (squares (((((8*3)*5)*7)*11)*13)).card=_
  repeat rw [square_count_crt (by decide)]
  decide +kernel

private theorem unit_total : Fintype.card (ZMod m)ˣ=23040 := by
  rw [ZMod.card_units_eq_totient]
  change (((((8*3)*5)*7)*11)*13).totient=_
  repeat rw [Nat.totient_mul (by decide)]
  decide +kernel

noncomputable def signed (d : ℕ) [NeZero d] : Finset (ZMod d)ˣ :=
  squares d ∪ (squares d).map (Equiv.neg _).toEmbedding

theorem mem_signed {d : ℕ} [NeZero d] (u : (ZMod d)ˣ) :
    u∈signed d ↔ IsSquare u.val ∨ IsSquare (-u.val) := by
  simp only [signed,mem_union,mem_map_equiv,Equiv.neg_symm,Equiv.neg_apply,mem_squares,square_val,
    Units.val_neg]

private theorem disjoint_halves {d : ℕ} [NeZero d] (div : 8∣d) :
    Disjoint (squares d) ((squares d).map (Equiv.neg _).toEmbedding) := by
  refine disjoint_left.mpr ?_
  intro u yes no
  have first := square_val.mp ((mem_squares u).mp yes)
  have second : IsSquare (-u.val) := by
    simpa only [mem_map_equiv,Equiv.neg_symm,Equiv.neg_apply,mem_squares,square_val,Units.val_neg] using no
  let f := ZMod.castHom div (ZMod 8)
  have eight : ∀ z : ZMod 8, IsUnit z → IsSquare z → ¬IsSquare (-z) := by decide +kernel
  exact eight (f u.val) (u.isUnit.map f) (first.map f)
    (by simpa only [map_neg] using second.map f)

theorem residue_count : (squares m).card=180 ∧ (signed m).card=360 ∧
    Fintype.card (ZMod m)ˣ=23040 := by
  refine ⟨square_total,?_,unit_total⟩
  rw [signed,card_union_of_disjoint (disjoint_halves (by decide)),card_map,square_total]

private noncomputable def mark {d : ℕ} [NeZero d] (u v : (ZMod d)ˣ) : ℕ :=
  if u*v∈signed d then 1 else 0

private theorem pair_sum (d : ℕ) [NeZero d] :
    (∑ z : (ZMod d)ˣ×(ZMod d)ˣ,mark z.1 z.2)=Fintype.card (ZMod d)ˣ*(signed d).card := by
  have each (u : (ZMod d)ˣ) : (∑ v : (ZMod d)ˣ,mark u v)=(signed d).card := by
    calc _ = ∑ v : (ZMod d)ˣ, if v∈signed d then 1 else 0 :=
             Equiv.sum_comp (Equiv.mulLeft u) (fun v => if v∈signed d then 1 else 0)
         _ = _ := by simp
  rw [Fintype.sum_prod_type]
  simp only [each,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id]

private theorem uniform_eq (d : ℕ) [NeZero d] :
    ExtendedProductCosts.uniform (@mark d _)=(signed d).card/(Fintype.card (ZMod d)ˣ:ℝ) := by
  rw [ExtendedProductCosts.uniform,pair_sum,Fintype.card_prod]
  push_cast
  exact mul_div_mul_left _ _ (by exact_mod_cast (Fintype.card_pos.ne' : Fintype.card (ZMod d)ˣ≠0))

theorem uniform : ExtendedProductCosts.uniform (@mark m _)=1/64 := by
  rw [uniform_eq,residue_count.2.1,residue_count.2.2]
  norm_num

/-- Canonical pairs of distinct 1,024-bit primes with a full-width product
whose residue or its negative is square. -/
noncomputable def population : Finset (ℕ×ℕ) := by
  classical
  exact eligible.filter fun v => IsSquare ((v.1*v.2:ℕ):ZMod m) ∨ IsSquare (-((v.1*v.2:ℕ):ZMod m))

theorem mem_population {p q : ℕ} : (p,q)∈population ↔
    (p,q)∈eligible ∧ (IsSquare ((p*q:ℕ):ZMod m) ∨ IsSquare (-((p*q:ℕ):ZMod m))) := by
  classical
  exact mem_filter

attribute [local irreducible] eligible

private theorem coprime_pair {p q : ℕ} (member : (p,q)∈eligible) :
    p.Coprime m ∧ q.Coprime m := by
  obtain ⟨lo,lt,_,pp,qp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp member
  have pl : m<p := (by decide +kernel : m<FullRangeResidueEstimates.X).trans_le lo
  exact ⟨pp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) pl),
    qp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) (pl.trans lt))⟩

private theorem lift_at {d : ℕ} [NeZero d] (x y : ZMod d) (ux : IsUnit x) (uy : IsUnit y) :
    PrimeFactors.ExtendedProductCosts.lift (@mark d _) x y=
      (if IsSquare (x*y) ∨ IsSquare (-(x*y)) then 1 else 0) := by
  simp only [PrimeFactors.ExtendedProductCosts.lift,dif_pos ux,dif_pos uy,mark,mem_signed,
    Units.val_mul,IsUnit.unit_spec]

private theorem actual_share :
    ExtendedProductCosts.actual (@mark m _)=(population.card:ℝ)/eligible.card := by
  classical
  have sums : (∑ z∈eligible,PrimeFactors.ExtendedProductCosts.lift (@mark m _) z.1 z.2)=population.card := by
    unfold population
    rw [card_filter]
    apply sum_congr rfl
    rintro ⟨p,q⟩ mem
    obtain ⟨pp,qp⟩ := coprime_pair mem
    rw [lift_at _ _ ((ZMod.isUnit_iff_coprime p m).mpr pp) ((ZMod.isUnit_iff_coprime q m).mpr qp)]
    simp only [Nat.cast_mul]
  unfold ExtendedProductCosts.actual FiveSquareAllPrimeRanks.actual
  rw [sums]

/-- The complete-product population frequency uses the EHP prime-count
endpoint bounds at this modulus. The uniform residue frequency is exact. -/
theorem close_ehp {li : ℕ→ℝ} (h : ExtendedModulusPrimeSupply.Endpoints m li) :
    |(population.card:ℝ)/eligible.card-1/64|≤1/(2:ℝ)^146 := by
  rw [←actual_share,←uniform]
  have sym (x y : (ZMod m)ˣ) : mark x y=mark y x := by rw [mark,mark,mul_comm x y]
  have bound (x y : (ZMod m)ˣ) : mark x y≤1 := by unfold mark; split <;> decide
  simpa only [Nat.cast_one] using ExtendedProductCosts.close (by decide : 3≤m)
    (by decide +kernel : m≤2^161) h _ sym bound

private theorem first_exists {p q : ℕ} (member : (p,q)∈eligible) :
    ∃ a, CircleMarkFirstTarget.First (p*q) a := by
  classical
  obtain ⟨lo,lt,_,pp,qp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp member
  letI : Fact p.Prime := ⟨pp⟩
  letI : Fact q.Prime := ⟨qp⟩
  have pl : 2<p := (by decide +kernel : 2<FullRangeResidueEstimates.X).trans_le lo
  have ql := pl.trans lt
  have count := (CircleMarkTargetFrequency.counts lt.ne pl.ne' ql.ne' ∅).1
  have nonempty : 0<(CircleMarkTargetFrequency.targets (p*q)).card := by
    rw [count]
    exact Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)
  obtain ⟨z,hz⟩ := card_pos.mp nonempty
  have ex : ∃ a : ℕ, jacobiSym (a:ℤ) (p*q)= -1 := ⟨z.val,(mem_filter.mp hz).2⟩
  exact ⟨Nat.find ex,Nat.find_spec ex,fun _ h => Nat.find_min' ex h⟩

/-- Membership means the least positive target giving Jacobi symbol minus
one actually exceeds 13. Such a target exists at every eligible product. -/
theorem mem_late {p q : ℕ} : (p,q)∈population ↔ (p,q)∈eligible ∧
    ∃ a, CircleMarkFirstTarget.First (p*q) a ∧ 13<a := by
  rw [mem_population]
  apply and_congr_right
  intro member
  obtain ⟨lo,lt,_,pp,qp,_⟩ := PrimeFactors.FullPopulationFavoredSums.mem_eligible.mp member
  obtain ⟨cp,cq⟩ := coprime_pair member
  have cop : (p*q).Coprime m := Nat.coprime_mul_iff_left.mpr ⟨cp,cq⟩
  have pl : 2<p := (by decide +kernel : 2<FullRangeResidueEstimates.X).trans_le lo
  have odd := (pp.odd_of_ne_two pl.ne').mul (qp.odd_of_ne_two (pl.trans lt).ne')
  have large : 1<p*q := (by omega : 1<p).trans_le (Nat.le_mul_of_pos_right p qp.pos)
  rw [←CircleMarkFirstTarget.quiet_iff_signed_square odd cop]
  constructor
  · intro quiet
    obtain ⟨a,first⟩ := first_exists member
    exact ⟨a,first,(CircleMarkFirstTarget.late_iff large cop first).mpr quiet⟩
  · rintro ⟨a,first,late⟩
    exact (CircleMarkFirstTarget.late_iff large cop first).mp late

end PrimeFactors.CircleMarkFirstTargetPopulation
