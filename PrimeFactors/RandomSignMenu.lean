import PrimeFactors.FourDiscriminants
import PrimeFactors.CubicLocalCharacters
import PrimeFactors.GeometricOrderFailure

/-! A public negative-Jacobi anchor and independent uniform units give an exact
finite count for coverage of the four local quadratic signs. -/
namespace PrimeFactors.RandomSignMenu
open Finset

abbrev Signs := ℤˣ × ℤˣ

/-- The signs realized by one anchor and one unit together with their product. -/
noncomputable def pair (a b : Signs) : Finset Signs := {1, a, b, a*b}

private theorem finite_cases : ∀ a b : Signs, a.1*a.2 = -1 →
    (pair a b = univ ↔ (a.1=1 ∧ b.1= -1) ∨ (a.2=1 ∧ b.2= -1)) ∧
    (pair a b ≠ univ → (-1,-1) ∉ pair a b) := by decide +kernel

/-- The two hidden characters, evaluated on units of the original modulus. -/
noncomputable def signs {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q) :
    (ZMod (p*q))ˣ →* Signs :=
  (((quadraticChar (ZMod p)).toUnitHom).prodMap (quadraticChar (ZMod q)).toUnitHom).comp
    (GeometricOrderFailure.localPair cop).toMonoidHom

private theorem surjective {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) : Function.Surjective (signs cop) := by
  rintro ⟨s,t⟩
  obtain ⟨x,hx⟩ := CubicLocalCharacters.sign_surjective (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n]) s
  obtain ⟨y,hy⟩ := CubicLocalCharacters.sign_surjective (F := ZMod q) (by rwa [ZMod.ringChar_zmod_n]) t
  obtain ⟨b,hb⟩ := (GeometricOrderFailure.localPair cop).surjective (x,y)
  refine ⟨b, ?_⟩
  change (_,_) = (s,t)
  exact Prod.ext (by change (quadraticChar (ZMod p)).toUnitHom ((GeometricOrderFailure.localPair cop b).1) = s; rw [hb]; exact hx)
    (by change (quadraticChar (ZMod q)).toUnitHom ((GeometricOrderFailure.localPair cop b).2) = t; rw [hb]; exact hy)

/-- The product of the hidden signs is the Jacobi symbol of any public representative. -/
theorem jacobi_signs {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (cop : p.Coprime q)
    (a : (ZMod (p*q))ˣ) (A : ℤ) (rep : (A : ZMod (p*q)) = a.val) :
    jacobiSym A (p*q) = (((signs cop a).1 * (signs cop a).2 : ℤˣ) : ℤ) := by
  rw [jacobiSym.mul_right' A hp.out.ne_zero hq.out.ne_zero,
    ← jacobiSym.legendreSym.to_jacobiSym, ← jacobiSym.legendreSym.to_jacobiSym]
  have cast := congrArg (ZMod.chineseRemainder cop) rep
  rw [map_intCast] at cast
  exact congrArg₂ (·*·) (congrArg (quadraticChar (ZMod p)) (congrArg Prod.fst cast))
    (congrArg (quadraticChar (ZMod q)) (congrArg Prod.snd cast))

/-- For a desired public Jacobi sign j, exactly one member of each generated pair is relevant. -/
theorem select_sign : ∀ a b : Signs, ∀ j : ℤˣ, a.1*a.2 = -1 →
    let picked := if b.1*b.2=j then b else a*b
    picked.1*picked.2=j ∧ ∀ t : Signs, t.1*t.2=j → (t ∈ ({b,a*b} : Finset Signs) ↔ t=picked) := by
  decide +kernel

/-- All signs realized by the entries 1, a, and bᵢ, a*bᵢ for every i. -/
noncomputable def menu {G : Type*} [Group G] (f : G →* Signs) {k : ℕ} (a : G) (bs : Fin k → G) : Finset Signs :=
  {1,f a} ∪ univ.biUnion (fun i => pair (f a) (f (bs i)))

/-- Even when the failed pairs are combined, the all-negative sign is still missing. -/
theorem fails_iff {G : Type*} [Group G] (f : G →* Signs) {k : ℕ} (a : G) (bs : Fin k → G)
    (ha : (f a).1*(f a).2 = -1) : menu f a bs ≠ univ ↔ ∀ i, pair (f a) (f (bs i)) ≠ univ := by
  constructor
  · intro fail i hit
    apply fail
    apply eq_univ_of_forall
    intro s
    have h : s ∈ pair (f a) (f (bs i)) := hit ▸ mem_univ s
    exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,h⟩)
  · intro h full
    have missing (i : Fin k) := (finite_cases _ _ ha).2 (h i)
    have anchor : ∀ v : Signs, v.1*v.2 = -1 → (-1,-1) ∉ ({1,v} : Finset Signs) := by decide +kernel
    have mem : (-1,-1) ∈ menu f a bs := full ▸ mem_univ _
    rcases mem_union.mp mem with hm|hm
    · exact anchor _ ha hm
    · obtain ⟨i,_,hi⟩ := mem_biUnion.mp hm
      exact missing i hi

/-- One pair covers precisely when its sampled unit is a nonsquare at the anchor's square prime. -/
theorem pair_covers_iff (a b : Signs) (ha : a.1*a.2 = -1) :
    pair a b = univ ↔ (a.1=1 ∧ b.1= -1) ∨ (a.2=1 ∧ b.2= -1) := (finite_cases a b ha).1

/-- Full coverage is equivalent to covering the two patterns of any one prescribed Jacobi sign.
`select_sign` shows only one candidate per generated pair needs a downstream test to do this. -/
theorem target_iff {G : Type*} [Group G] (f : G →* Signs) {k : ℕ} (a : G) (bs : Fin k → G)
    (ha : (f a).1*(f a).2= -1) (j : ℤˣ) :
    (∀ t : Signs, t.1*t.2=j → t ∈ menu f a bs) ↔ menu f a bs = univ := by
  let missing (v : Signs) (j : ℤˣ) : Signs := if j=1 then (-1,-1) else (-v.1,-v.2)
  have absent : ∀ v : Signs, ∀ h : ℤˣ, v.1*v.2= -1 →
      (missing v h).1*(missing v h).2=h ∧ missing v h ∉ ({1,v} : Finset Signs) ∧
      ∀ b : Signs, pair v b ≠ univ → missing v h ∉ pair v b := by decide +kernel
  constructor
  · intro ht
    by_contra bad
    obtain ⟨eq,anchor,abs⟩ := absent _ j ha
    rcases mem_union.mp (ht _ eq) with h|h
    · exact anchor h
    · obtain ⟨i,_,hi⟩ := mem_biUnion.mp h
      exact abs _ ((fails_iff f a bs ha).mp bad i) hi
  · intro full t _
    rw [full]; exact mem_univ t

private theorem fiber_count {G : Type*} [Group G] [Finite G] (f : G →* Signs)
    (hf : Function.Surjective f) (P : Signs → Prop) :
    Nat.card {x : G // P (f x)} = Nat.card {s : Signs // P s} * Nat.card f.ker := by
  let group : {x : G // P (f x)} ≃ Σ s : {s : Signs // P s}, {x : G // f x = s.val} := {
    toFun := fun x => ⟨⟨f x,x.property⟩,x,rfl⟩
    invFun := fun x => ⟨x.2.val,(congrArg P x.2.property).mpr x.1.property⟩
    left_inv := fun _ => rfl
    right_inv := by rintro ⟨⟨s,hs⟩,⟨x,hx⟩⟩; change f x = s at hx; subst s; rfl }
  let e := group.trans ((Equiv.sigmaCongrRight (fun s : {v : Signs // P v} => MonoidHom.fiberEquivKerOfSurjective hf s.val)).trans
    (Equiv.sigmaEquivProd _ _))
  exact (Nat.card_congr e).trans (Nat.card_prod _ _)

/-- With k independent draws, exactly one in 2^k ordered lists misses a sign. -/
theorem failure_fraction {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (a : (ZMod (p*q))ˣ) (ha : (signs cop a).1*(signs cop a).2= -1)
    (k : ℕ) : 2^k * Nat.card {bs : Fin k → (ZMod (p*q))ˣ // menu (signs cop) a bs ≠ univ} =
      Nat.card (Fin k → (ZMod (p*q))ˣ) := by
  classical
  let f := signs cop
  have hf := surjective cop hp hq
  let P := fun b : Signs => pair (f a) b ≠ univ
  have small : ∀ v : Signs, v.1*v.2= -1 → (univ.filter (fun b => pair v b ≠ univ)).card = 2 := by decide +kernel
  have sz : Nat.card {b : Signs // P b} = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact small _ ha
  have bad := fiber_count f hf P
  rw [sz] at bad
  let total := ((Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight (fun s =>
    MonoidHom.fiberEquivKerOfSurjective hf s))).trans (Equiv.sigmaEquivProd _ _)
  have all := (Nat.card_congr total).trans (Nat.card_prod _ _)
  have four : Nat.card Signs = 4 := by simp [Nat.card_eq_fintype_card,Fintype.card_units_int]
  rw [four] at all
  let e := (Equiv.subtypeEquivRight (fun bs : Fin k → (ZMod (p*q))ˣ => fails_iff f a bs ha)).trans
    (Equiv.subtypePiEquivPi (p := fun (_ : Fin k) x => P (f x)))
  have positions : Nat.card (Fin k)=k := by simp [Nat.card_eq_fintype_card]
  rw [Nat.card_congr e,Nat.card_fun,Nat.card_fun,positions,←mul_pow]
  change (2 * Nat.card {x // P (f x)}) ^ k = _
  rw [bad,all]; ring

/-- An integer with the public Jacobi symbol −1 supplies the anchor hypothesis directly. -/
theorem jacobi_failure_fraction {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p≠2) (hq : q≠2) (a : (ZMod (p*q))ˣ) (A : ℤ) (rep : (A : ZMod (p*q)) = a.val)
    (ja : jacobiSym A (p*q) = -1) (k : ℕ) :
    2^k * Nat.card {bs : Fin k → (ZMod (p*q))ˣ // menu (signs cop) a bs ≠ univ} =
      Nat.card (Fin k → (ZMod (p*q))ˣ) :=
  failure_fraction cop hp hq a (Units.ext ((jacobi_signs cop a A rep).symm.trans ja)) k

/-- Two signs have already been supplied by the fixed entries. The independent comparison
fails precisely when at least one of the other two is absent from its m uniform signs. -/
theorem independent_two_missing (m : ℕ) (u v : Signs) (h : u ≠ v) :
    let words (s : Finset Signs) := Fintype.piFinset (fun _ : Fin m => univ \ s)
    (words {u} ∪ words {v}).card + 2^m = 2 * 3^m := by
  intro words
  have size : Fintype.card Signs = 4 := by simp [Fintype.card_units_int]
  have count (s : Finset Signs) : (words s).card = (4-s.card)^m := by
    simp [words,Fintype.card_piFinset_const,card_sdiff (subset_univ s),size]
  have inter : words {u} ∩ words {v} = words {u,v} := by
    ext x
    simp only [words,mem_inter,Fintype.mem_piFinset,mem_sdiff,mem_univ,true_and,
      mem_singleton,mem_insert,not_or]
    exact forall_and.symm
  have sum := card_union_add_card_inter (words {u}) (words {v})
  rw [inter,count,count,count] at sum
  simpa [h,two_mul] using sum

end PrimeFactors.RandomSignMenu
