import PrimeFactors.FactorClueSumPrecision
import PrimeFactors.FactorSum

/-! The exact set of admissible modular sums, using the product alone when
it is one modulo twelve. The four labels encode an unknown factor residue. -/
namespace PrimeFactors.FourSumResidueMenu

def modulus (N : ℕ) := if N%8=1 then 144 else 288
def label (j : Fin 4) : ℕ := ![1,5,7,11] j

instance (N : ℕ) : NeZero (modulus N) := ⟨by unfold modulus; split <;> decide⟩

private theorem label_unit (N : ℕ) (j : Fin 4) : IsUnit (label j : ZMod (modulus N)) := by
  apply (ZMod.isUnit_iff_coprime ..).mpr
  unfold modulus
  split
  · exact (by decide +kernel : ∀ i : Fin 4,(label i).Coprime 144) j
  · exact (by decide +kernel : ∀ i : Fin 4,(label i).Coprime 288) j

/-- The four entries use modular inversion only at 144 or 288. -/
noncomputable def residue (N : ℕ) (j : Fin 4) : ZMod (modulus N) :=
  (label j:ZMod (modulus N)) + (label j:ZMod (modulus N))⁻¹*N

theorem attained (N : ℕ) (j : Fin 4) : AdmissibleSum (N:ZMod (modulus N)) (residue N j) := by
  refine ⟨label j,(label j:ZMod (modulus N))⁻¹*N,?_,rfl⟩
  rw [←mul_assoc,ZMod.mul_inv_of_unit _ (label_unit N j),one_mul]

theorem equation (N : ℕ) (j : Fin 4) (s : ZMod (modulus N)) :
    (label j:ZMod (modulus N))*s=(label j:ZMod (modulus N))^2+N ↔ s=residue N j := by
  have eq : (label j:ZMod (modulus N))*residue N j=(label j:ZMod (modulus N))^2+N := by
    rw [residue,mul_add,←mul_assoc,ZMod.mul_inv_of_unit _ (label_unit N j),one_mul,pow_two]
  rw [←eq]
  exact ⟨(label_unit N j).mul_left_cancel,congrArg _⟩

private theorem divides (N : ℕ) : 24∣modulus N := by unfold modulus; split <;> decide

/-- Every modular factor pair receives a canonical label from its first
coordinate, which fixes its sum at the full modulus. -/
theorem exhaustive {N : ℕ} (gate : N%12=1) {x y : ZMod (modulus N)} (prod : x*y=N) :
    ∃ j : Fin 4, x.val%12=label j ∧ x+y=residue N j := by
  have eq : ((x.val*y.val:ℕ):ZMod (modulus N))=N := by simpa only [Nat.cast_mul,ZMod.natCast_zmod_val] using prod
  have small := ((ZMod.natCast_eq_natCast_iff ..).mp eq).of_dvd ((by decide : 12∣24).trans (divides N))
  have s : (x.val:ZMod 12)*y.val=1 := by
    rw [←Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff (x.val*y.val) 1 12).mpr
    exact small.trans (show N ≡ 1 [MOD 12] from gate)
  have table : ∀ u v : ZMod 12, u*v=1 → ∃ j : Fin 4,u.val=label j := by decide +kernel
  obtain ⟨j,hj⟩ := table _ _ s
  rw [ZMod.val_natCast] at hj
  have cop := (by decide +kernel : ∀ j : Fin 4,(label j).Coprime 12) j
  have pin := (FactorClueSumPrecision.at_greatest (N:=N) cop).1
  rw [FactorClueSumPrecision.twelve gate cop] at pin
  change FactorClueSumPrecision.Pinned (modulus N) N (label j) 12 at pin
  have repr : label j+12*(x.val/12)=x.val := hj ▸ Nat.mod_add_div x.val 12
  refine ⟨j,hj,(equation N j _).mp ?_⟩
  simpa only [repr,ZMod.natCast_zmod_val] using pin (x.val/12) y (by simpa only [repr,ZMod.natCast_zmod_val] using prod)

private theorem distinguish : ∀ n s : ZMod 24, ∀ j k : Fin 4, n.val%12=1 →
    (label j:ZMod 24)*s=(label j:ZMod 24)^2+n →
    (label k:ZMod 24)*s=(label k:ZMod 24)^2+n → j=k := by decide +kernel

/-- Reduction modulo 24 already separates the four entries, even though their
values at full precision can depend on more bits of the product. -/
theorem injective {N : ℕ} (gate : N%12=1) : Function.Injective (residue N) := by
  intro j k same
  let red := ZMod.castHom (divides N) (ZMod 24)
  have applyEq {i : Fin 4} {s : ZMod (modulus N)} (eq : s=residue N i) :
      (label i:ZMod 24)*red s=(label i:ZMod 24)^2+(N:ZMod 24) := by
    simpa only [map_mul,map_add,map_pow,map_natCast] using congrArg red ((equation N i s).mpr eq)
  exact distinguish (N:ZMod 24) (red (residue N j)) j k
    (by simpa only [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 12∣24)] using gate)
    (applyEq rfl) (applyEq same)

theorem iff_unique {N : ℕ} (gate : N%12=1) (s : ZMod (modulus N)) :
    AdmissibleSum (N:ZMod (modulus N)) s ↔
    ∃! j : Fin 4, (label j:ZMod (modulus N))*s=(label j:ZMod (modulus N))^2+N := by
  constructor
  · rintro ⟨x,y,prod,rfl⟩
    obtain ⟨j,_,eq⟩ := exhaustive gate prod
    exact ⟨j,(equation N j _).mpr eq,fun k hk => injective gate (((equation N k _).mp hk).symm.trans eq)⟩
  · rintro ⟨j,eq,_⟩
    rw [(equation N j _).mp eq]
    exact attained N j

noncomputable def menu (N : ℕ) := Finset.univ.image (residue N)

/-- This product-only menu has exactly four entries and is exactly the
support of the modular factor model. -/
theorem exact_menu {N : ℕ} (gate : N%12=1) : (menu N).card=4 ∧
    ∀ s : ZMod (modulus N), s∈menu N ↔ AdmissibleSum (N:ZMod (modulus N)) s := by
  constructor
  · rw [menu,Finset.card_image_of_injective _ (injective gate),Finset.card_univ,Fintype.card_fin]
  · intro s
    constructor
    · rintro h
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
      exact attained N j
    · rintro ⟨x,y,prod,rfl⟩
      obtain ⟨j,_,eq⟩ := exhaustive gate prod
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,eq.symm⟩

end PrimeFactors.FourSumResidueMenu
