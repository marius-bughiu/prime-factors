import PrimeFactors.ProjectiveFixedLines

/-! The CRT model for the projective line at distinct primes is the pair of
local lines used by `ProjectiveFixedLines.both`. In each component `some z`
denotes [z:1] and `none` denotes [1:0]. -/

namespace PrimeFactors.ProjectiveChartComplement

open Finset

abbrev Point (p q : ℕ) := Option (ZMod p) × Option (ZMod q)

private noncomputable def side (p : ℕ) [NeZero p] : Bool → Finset (Option (ZMod p))
  | false => univ.map ⟨some, Option.some_injective _⟩
  | true => {none}

/-- A true flag requires denominator zero in the corresponding component. -/
noncomputable def chart (p q : ℕ) [NeZero p] [NeZero q] (ip iq : Bool) : Finset (Point p q) :=
  side p ip ×ˢ side q iq

private theorem mem_side {p : ℕ} [NeZero p] (x : Option (ZMod p)) (i : Bool) :
    x ∈ side p i ↔ x.isNone=i := by
  cases i <;> cases x <;> simp [side]

/-- Each local-denominator pattern specifies exactly one of the four disjoint
strata, and each point belongs to the stratum with its pattern. -/
theorem mem_chart {p q : ℕ} [NeZero p] [NeZero q] (v : Point p q) (ip iq : Bool) :
    v∈chart p q ip iq ↔ (v.1.isNone,v.2.isNone)=(ip,iq) := by
  simp [chart,mem_side]

/-- The public coordinate z gives the point [z:1] at both primes. -/
noncomputable def fromAffine {p q : ℕ} (cop : p.Coprime q) (z : ZMod (p*q)) : Point p q :=
  let v := ZMod.chineseRemainder cop z
  (some v.1,some v.2)

/-- A given global affine coordinate has a unique image in the CRT model. -/
theorem fromAffine_injective {p q : ℕ} (cop : p.Coprime q) :
    Function.Injective (fromAffine cop) := by
  intro x y h
  apply (ZMod.chineseRemainder cop).injective
  exact Prod.ext (Option.some.inj (congrArg Prod.fst h))
    (Option.some.inj (congrArg Prod.snd h))

/-- The common affine chart consists precisely of the points reached by
ordinary affine coordinates modulo the product. -/
theorem affine_range {p q : ℕ} [NeZero p] [NeZero q] (cop : p.Coprime q) :
    (univ : Finset (ZMod (p*q))).image (fromAffine cop)=chart p q false false := by
  classical
  ext ⟨a,b⟩
  constructor
  · rintro h
    obtain ⟨z,_,eq⟩ := mem_image.mp h
    rw [←eq,mem_chart]
    rfl
  · intro h
    rw [mem_chart] at h
    cases a with
    | none => simp at h
    | some x =>
      cases b with
      | none => simp at h
      | some y =>
        refine mem_image.mpr ⟨(ZMod.chineseRemainder cop).symm (x,y),mem_univ _,?_⟩
        simp [fromAffine]

/-- Each mixed stratum has as many points as the field where the denominator
is nonzero. The point at infinity at both primes occurs once. -/
theorem chart_sizes (p q : ℕ) [NeZero p] [NeZero q] :
    (chart p q false false).card=p*q ∧
    (chart p q false true).card=p ∧ (chart p q true false).card=q ∧
    (chart p q true true).card=1 := by
  simp [chart,side,ZMod.card]

theorem common_infinity (p q : ℕ) [NeZero p] [NeZero q] :
    chart p q true true={(none,none)} := by
  ext ⟨a,b⟩
  cases a <;> cases b <;> simp [mem_chart]

/-- The complement of the image of the global affine chart consists of the
two mixed strata and the common point at infinity. -/
theorem boundary_eq (p q : ℕ) [NeZero p] [NeZero q] :
    (chart p q false false)ᶜ = chart p q false true ∪ chart p q true false ∪ {(none,none)} := by
  ext ⟨a,b⟩
  cases a <;> cases b <;> simp [mem_chart]

theorem boundary_card (p q : ℕ) [NeZero p] [NeZero q] :
    (chart p q false false)ᶜ.card=p+q+1 := by
  rw [card_compl,Fintype.card_prod,Fintype.card_option,Fintype.card_option,
    ZMod.card,ZMod.card,(chart_sizes p q).1]
  rw [show (p+1)*(q+1)=p*q+(p+q+1) by ring]
  omega

end PrimeFactors.ProjectiveChartComplement
