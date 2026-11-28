import PrimeFactors.PrimePowerPairWeight
import Mathlib.Data.ZMod.Units

/-! Count collisions of the sum of two ordered local factors at a fixed square
unit product modulo an odd prime power. -/

namespace PrimeFactors.PrimePowerSumCollisions

open Finset PrimeSquareSumWeights
open scoped Classical

private abbrev U (p e : ℕ) := (ZMod (p^e))ˣ

private def partner {p e : ℕ} (n : ℕ) (x : U p e) : ZMod (p^e) := ↑x⁻¹*n

private theorem product_eq {p e n : ℕ} (x : U p e) : (x : ZMod (p^e))*partner n x=n := by
  simp [partner,←mul_assoc]

noncomputable def layer (p e n j : ℕ) [NeZero p] :=
  univ.filter fun x : U p e => p^j ∣ ((x : ZMod (p^e))-partner n x).val

private noncomputable def mass (p e n j : ℕ) [NeZero p] :=
  ∑ x ∈ layer p e n j, weight n ((x : ZMod (p^e))+partner n x)

variable {p : ℕ} [Fact p.Prime]

private theorem full_unit {n : ℕ} (unit : ¬p∣n) (e : ℕ) : IsUnit (n : ZMod (p^e)) :=
  (ZMod.isUnit_iff_coprime _ _).mpr (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr unit).symm.pow_right _)

private theorem card_lift {e j : ℕ} (jp : 0<j) (le : j≤e) (v : U p j) :
    (univ.filter fun x : U p e => ZMod.unitsMap (pow_dvd_pow p le) x=v).card = p^(e-j) := by
  let f := ZMod.unitsMap (pow_dvd_pow p le)
  have onto := ZMod.unitsMap_surjective (pow_dvd_pow p le)
  let m := (univ.filter fun x : U p e => f x=v).card
  have fibers (y : U p j) : (univ.filter fun x : U p e => f x=y).card = m :=
    MonoidHom.card_fiber_eq_of_mem_range f (onto y) (onto v)
  have counts : Fintype.card (U p e) = Fintype.card (U p j)*m := by
    simpa only [card_univ,fibers,sum_const,smul_eq_mul] using card_eq_sum_card_fiberwise
      (show Set.MapsTo f (univ : Finset (U p e)) (univ : Finset (U p j)) from fun _ _ => mem_univ _)
  change m=_
  apply Nat.eq_of_mul_eq_mul_left (Fintype.card_pos (α:=U p j))
  rw [←counts,ZMod.card_units_eq_totient,ZMod.card_units_eq_totient,
    Nat.totient_prime_pow (Fact.out : p.Prime) (by omega : 0<e),
    Nat.totient_prime_pow (Fact.out : p.Prime) jp]
  rw [Nat.mul_right_comm,←pow_add,show j-1+(e-j)=e-1 by omega]

private theorem deep_iff {e j n : ℕ} (le : j≤e) (x : U p e) :
    p^j ∣ ((x : ZMod (p^e))-partner n x).val ↔
      ((ZMod.unitsMap (pow_dvd_pow p le) x : U p j) : ZMod (p^j))^2=n := by
  let f := ZMod.castHom (pow_dvd_pow p le) (ZMod (p^j))
  have zero (d : ZMod (p^e)) : p^j∣d.val ↔ f d=0 := by
    rw [←ZMod.natCast_zmod_eq_zero_iff_dvd,←map_natCast f,ZMod.natCast_zmod_val]
  rw [zero,map_sub,sub_eq_zero]
  change f x.val = f (partner n x) ↔ (f x.val)^2=n
  have mul : f x.val * f (partner n x) = n := by rw [←map_mul,product_eq,map_natCast]
  rw [pow_two,←mul]
  exact ⟨fun eq => congrArg (f x.val * ·) eq, (x.isUnit.map f).mul_left_cancel⟩

private theorem root_count (odd : p≠2) {n : ℕ} (unit : ¬p∣n) (sq : IsSquare (n : ZMod p))
    {j : ℕ} (pos : 0<j) :
    (univ.filter fun x : U p j => (x : ZMod (p^j))^2=n).card = 2 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  let R := ZMod (p^(k+1))
  let f (x : {x : Rˣ // (x.val:R)^2=n}) : {x : R // x^2=n} := ⟨x.val.val,x.property⟩
  have bij : Function.Bijective f := by
    constructor
    · intro x y eq
      exact Subtype.ext (Units.ext (congrArg Subtype.val eq))
    · rintro ⟨x,hx⟩
      have u : IsUnit x := (isUnit_pow_iff (by decide : 2≠0)).mp (hx ▸ full_unit unit _)
      exact ⟨⟨u.unit,by simpa only [IsUnit.unit_spec] using hx⟩,Subtype.ext u.unit_spec⟩
  rw [←Fintype.card_subtype,←Nat.card_eq_fintype_card,Nat.card_congr (Equiv.ofBijective f bij)]
  have nz : (n : ZMod p) ≠ 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd n p).mp.mt unit
  simpa only [Int.cast_natCast,if_pos sq] using
    primitiveNorm_odd_root_count odd (n : ℤ) (by simpa only [Int.cast_natCast] using nz) k

/-- The number of ordered pairs whose two coordinates agree through j
base-p digits. Each of the two lower-precision roots has the same number of lifts. -/
theorem layer_card (odd : p≠2) {n : ℕ} (unit : ¬p∣n) (sq : IsSquare (n : ZMod p))
    {e j : ℕ} (jp : 0<j) (le : j≤e) : (layer p e n j).card = 2*p^(e-j) := by
  let roots := univ.filter fun x : U p j => (x : ZMod (p^j))^2=n
  let f := ZMod.unitsMap (pow_dvd_pow p le)
  have same : layer p e n j = univ.filter (fun x => f x∈roots) := by
    ext x
    simp only [layer,roots,mem_filter,mem_univ,true_and,deep_iff le]
    rfl
  rw [same,←sum_card_fiberwise_eq_card_filter]
  simp only [f,card_lift jp le,sum_const,smul_eq_mul,roots,root_count odd unit sq jp]

private theorem base_card {e n : ℕ} (ep : 0<e) :
    (layer p e n 0).card = p^(e-1)*(p-1) := by
  simp [layer,ZMod.card_units_eq_totient,Nat.totient_prime_pow (Fact.out : p.Prime) ep]

private theorem split_mass {n e j : ℕ} (odd : p≠2) (small : 2*j<e) :
    mass p e n j = ((layer p e n j).card - (layer p e n (j+1)).card)*(2*p^j) +
      mass p e n (j+1) := by
  have sub : layer p e n (j+1) ⊆ layer p e n j := by
    intro x hx
    simp only [layer,mem_filter,mem_univ,true_and] at hx ⊢
    exact (pow_dvd_pow p (Nat.le_succ j)).trans hx
  have val : ∑ x ∈ layer p e n j \ layer p e n (j+1),
      weight n ((x : ZMod (p^e))+partner n x) =
      (layer p e n j \ layer p e n (j+1)).card*(2*p^j) := by
    apply sum_const_nat
    intro x hx
    simp only [mem_sdiff,layer,mem_filter,mem_univ,true_and] at hx
    exact PrimePowerPairWeight.weight_of_shell odd (product_eq x) hx.1 hx.2 small
  rw [card_sdiff sub] at val
  unfold mass
  rw [←val,sum_sdiff sub]

private theorem first_mass {e n : ℕ} (ep : 0<e) (odd : p≠2) (unit : ¬p∣n)
    (sq : IsSquare (n : ZMod p)) :
    mass p e n 0 = 2*(p-3)*p^(e-1)+mass p e n 1 := by
  have prime := (Fact.out : p.Prime).two_le
  rw [split_mass odd (by omega : 2*0<e),base_card ep,
    layer_card odd unit sq (by decide : 0<1) (by omega : 1≤e),pow_zero]
  have id : p^(e-1)*(p-1) = 2*p^(e-1) + (p-3)*p^(e-1) := by
    rw [←Nat.add_mul,show 2+(p-3)=p-1 by omega,Nat.mul_comm]
  rw [id,Nat.add_sub_cancel_left]
  ring

private theorem middle_mass {e n j : ℕ} (jp : 0<j) (small : 2*j<e) (odd : p≠2)
    (unit : ¬p∣n) (sq : IsSquare (n : ZMod p)) :
    mass p e n j = 4*(p-1)*p^(e-1)+mass p e n (j+1) := by
  rw [split_mass odd small,layer_card odd unit sq jp (by omega),
    layer_card odd unit sq (Nat.succ_pos j) (by omega)]
  have power : p^(e-j) = p*p^(e-(j+1)) := by
    rw [←pow_succ',show e-(j+1)+1=e-j by omega]
  have prime := (Fact.out : p.Prime).pos
  have id : 2*(p*p^(e-(j+1))) = 2*p^(e-(j+1))+2*(p-1)*p^(e-(j+1)) := by
    have mul := congrArg (· * p^(e-(j+1))) (show 1+(p-1)=p by omega)
    nlinarith only [mul]
  rw [power,id,Nat.add_sub_cancel_left,show e-1=(e-(j+1))+j by omega,pow_add]
  ring

private theorem middle_total {e n : ℕ} (odd : p≠2) (unit : ¬p∣n) (sq : IsSquare (n : ZMod p))
    (k : ℕ) (bound : 2*k<e) :
    mass p e n 1 = k*(4*(p-1)*p^(e-1))+mass p e n (k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih (by omega),middle_mass (Nat.succ_pos k) bound odd unit sq]
    ring

private theorem last_mass {e n : ℕ} (ep : 0<e) (odd : p≠2) (unit : ¬p∣n)
    (sq : IsSquare (n : ZMod p)) :
    mass p e n ((e+1)/2) = 2*p^(e-((e+1)/2)+e/2) := by
  have constant : mass p e n ((e+1)/2) = (layer p e n ((e+1)/2)).card*p^(e/2) := by
    apply sum_const_nat
    intro x hx
    exact PrimePowerPairWeight.weight_of_deep odd (product_eq x) (mem_filter.mp hx).2
  rw [constant,layer_card odd unit sq (by omega) (by omega),pow_add]
  ring

/-- Each ordered pair contributes the number of ordered draws,
including itself, with its same sum. -/
noncomputable def collisions (n m : ℕ) [NeZero m] := ∑ s : ZMod m, weight n s ^ 2

/-- The second moment counts ordered pairs of draws with equal sums. -/
theorem count_equal_sums (n m : ℕ) [NeZero m] :
    Nat.card {v : Pairs n m × Pairs n m // sumOf v.1 = sumOf v.2} = collisions n m := by
  let fiber (s : ZMod m) := {x : Pairs n m // sumOf x = s}
  let split : {v : Pairs n m × Pairs n m // sumOf v.1 = sumOf v.2} ≃
      (Σ s : ZMod m, fiber s × fiber s) := {
    toFun := fun v => ⟨sumOf v.val.1,⟨v.val.1,rfl⟩,⟨v.val.2,v.property.symm⟩⟩
    invFun := fun v => ⟨(v.2.1.val,v.2.2.val),v.2.1.property.trans v.2.2.property.symm⟩
    left_inv := fun _ => rfl
    right_inv := by rintro ⟨_,⟨x,rfl⟩,⟨y,h⟩⟩; rfl }
  rw [Nat.card_congr split,Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp only [Fintype.card_prod,collisions,weight,Nat.card_eq_fintype_card,pow_two,fiber]

private theorem as_mass {e n : ℕ} (unit : ¬p∣n) : collisions n (p^e) = mass p e n 0 := by
  let f (x : U p e) : Pairs n (p^e) := ⟨(x,partner n x),product_eq x⟩
  have bij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card _).mpr ⟨
    (fun x y h => Units.ext (congrArg (fun z : Pairs n (p^e) => z.val.1) h)),by
      rw [ZMod.card_units_eq_totient,←Nat.card_eq_fintype_card,total (full_unit unit e)]⟩
  let equiv := Equiv.ofBijective f bij
  have sums := equiv.sum_comp (fun z : Pairs n (p^e) => weight n (sumOf z))
  have fiber (s : ZMod (p^e)) :
      (univ.filter (fun z : Pairs n (p^e) => sumOf z=s)).card = weight n s := by
    rw [weight,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have mass_zero : mass p e n 0 = ∑ z : Pairs n (p^e), weight n (sumOf z) := by
    simpa only [mass,layer,pow_zero,one_dvd,filter_True] using sums
  rw [mass_zero,collisions,←sum_fiberwise univ sumOf]
  apply sum_congr rfl
  intro s _
  rw [pow_two,←fiber s]
  symm
  exact sum_const_nat (fun z hz => (congrArg (weight n) (mem_filter.mp hz).2).trans (fiber s).symm)

private theorem combine {p e k : ℕ} (pmin : 3≤p) (pos : 0<e) (half : k=(e-1)/2) :
    2*(p-3)*p^(e-1) + (k*(4*(p-1)*p^(e-1)) + 2*p^(e-(e+1)/2+e/2)) =
      (2*e*(p-1)-2)*p^(e-1) := by
  have budget : 2≤2*e*(p-1) := by nlinarith only [Nat.mul_le_mul pos (show 1≤p-1 by omega)]
  apply Nat.add_right_cancel (m:=2*p^(e-1))
  rw [←Nat.add_mul,Nat.sub_add_cancel budget]
  obtain ⟨c,pc⟩ : ∃ c, p-1=c+2 ∧ p-3=c := ⟨p-3,by omega,rfl⟩
  rcases (show e=2*k+1 ∨ e=2*k+2 by omega) with odd | even
  · rw [show e-(e+1)/2+e/2=e-1 by omega,pc.1,pc.2,odd]
    ring
  · rw [show e-(e+1)/2+e/2=(e-1)+1 by omega,pow_succ,pc.1,pc.2]
    have base : p=c+3 := by omega
    rw [base,even]
    ring

/-- Exact second moment for every positive precision and every square unit
product, with each ordered factor pair receiving equal weight. -/
theorem second_moment {e n : ℕ} (ep : 0<e) (odd : p≠2) (unit : ¬p∣n)
    (sq : IsSquare (n : ZMod p)) :
    collisions n (p^e) = (2*e*(p-1)-2)*p^(e-1) := by
  let k := (e-1)/2
  have km : 2*k<e := by dsimp [k]; omega
  have half : k+1=(e+1)/2 := by dsimp [k]; omega
  rw [as_mass unit,first_mass ep odd unit sq,middle_total odd unit sq k km,half,last_mass ep odd unit sq]
  exact combine (by have := (Fact.out : p.Prime).two_le; omega) ep rfl

/-- The expected number of ordered local pairs in the sum class of a single
uniformly drawn pair, including the drawn pair itself. -/
theorem expected_weight {e n : ℕ} (ep : 0<e) (odd : p≠2) (unit : ¬p∣n)
    (sq : IsSquare (n : ZMod p)) :
    (collisions n (p^e) : ℚ)/Nat.card (Pairs n (p^e)) = 2*(e:ℚ)-2/((p:ℚ)-1) := by
  have prime := (Fact.out : p.Prime)
  have two : 2 ≤ 2*e*(p-1) := by
    nlinarith only [Nat.mul_le_mul ep (show 1≤p-1 by have := prime.two_le; omega)]
  have pp : (0:ℚ)<p := by exact_mod_cast prime.pos
  have one : (1:ℚ)<p := by exact_mod_cast prime.one_lt
  rw [second_moment ep odd unit sq,total (full_unit unit e),Nat.totient_prime_pow prime ep]
  push_cast [Nat.cast_sub two,Nat.cast_sub prime.one_le]
  field_simp [pp.ne',(sub_pos.mpr one).ne']
  ring

/-- Modulo 125 there are 550 equal-sum collisions among the 100 ordered
local pairs with product one. -/
theorem control125 : collisions 1 125 = 550 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact second_moment (p:=5) (n:=1) (e:=3) (by decide) (by decide) (by decide) (by norm_num)

end PrimeFactors.PrimePowerSumCollisions
