import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring

namespace PrimeFactors.SeedGapSieve

/-- Distinct squares modulo M, including zero. -/
noncomputable def squares (M : ℕ) [NeZero M] : Finset (ZMod M) :=
  Finset.univ.image (fun a : ZMod M => a^2)

private theorem mem_squares {M : ℕ} [NeZero M] {y : ZMod M} :
    y ∈ squares M ↔ ∃ a : ZMod M, a^2=y := by simp [squares]

/-- All multiplier classes for one gap. Shifting a precomputed scaled square
table by -v²*J is equivalent to multiplying (s-v²) by J. -/
noncomputable def multipliers {M : ℕ} [NeZero M] (J v : ZMod M) : Finset (ZMod M) :=
  (squares M).image (fun s => (s-v^2)*J)

theorem mem_multipliers {M : ℕ} [NeZero M] {n J v h : ZMod M} (inverse : n*J=1) :
    h ∈ multipliers J v ↔ ∃ u : ZMod M, h*n+v^2=u^2 := by
  constructor
  · intro hh
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨u,rfl⟩ := mem_squares.mp hs
    refine ⟨u,?_⟩
    calc
      _ = (u^2-v^2)*(n*J)+v^2 := by ring
      _ = _ := by rw [inverse]; ring
  · rintro ⟨u,hu⟩
    refine Finset.mem_image.mpr ⟨u^2,mem_squares.mpr ⟨u,rfl⟩,?_⟩
    rw [←hu,add_sub_cancel_right,mul_assoc,inverse,mul_one]

/-- Every exact integer solution is kept by the modular filter. -/
theorem keeps_square {M n u v h : ℕ} [NeZero M] {J : ZMod M} (inverse : (n : ZMod M)*J=1)
    (root : h*n+v^2=u^2) : (h : ZMod M) ∈ multipliers J (v : ZMod M) := by
  apply (mem_multipliers inverse).mpr
  exact ⟨u, by exact_mod_cast congrArg (fun k : ℕ => (k : ZMod M)) root⟩

/-- Each complete residue period contains the same number of candidates as
there are distinct square residues, for every shift and every unit input. -/
theorem count_per_period {M : ℕ} [NeZero M] {n J : ZMod M} (inverse : n*J=1) (v : ZMod M) :
    (multipliers J v).card=(squares M).card := by
  apply Finset.card_image_of_injective
  intro x y eqn
  have cancel (a : ZMod M) : (a-v^2)*J*n = a-v^2 := by
    rw [mul_assoc,mul_comm J n,inverse,mul_one]
  have h := congrArg (·*n) eqn
  exact sub_left_inj.mp ((cancel x).symm.trans (h.trans (cancel y)))

/-- The CRT identifies squares modulo a coprime product with independently
chosen squares in the two components, including nonunits. -/
theorem count_crt {a b : ℕ} [NeZero a] [NeZero b] (cop : a.Coprime b) :
    (squares (a*b)).card=(squares a).card*(squares b).card := by
  let e := ZMod.chineseRemainder cop
  have image : (squares (a*b)).image e = (squares a).product (squares b) := by
    ext p
    constructor
    · intro h
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨t,rfl⟩ := mem_squares.mp hs
      rw [map_pow]
      exact Finset.mem_product.mpr ⟨mem_squares.mpr ⟨(e t).1,rfl⟩,mem_squares.mpr ⟨(e t).2,rfl⟩⟩
    · intro h
      obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp h
      obtain ⟨u,hu⟩ := mem_squares.mp h₁
      obtain ⟨v,hv⟩ := mem_squares.mp h₂
      refine Finset.mem_image.mpr ⟨(e.symm (u,v))^2,mem_squares.mpr ⟨_,rfl⟩,?_⟩
      rw [map_pow,e.apply_symm_apply]
      exact Prod.ext hu hv
  calc
    _ = ((squares (a*b)).image e).card := (Finset.card_image_of_injective _ e.injective).symm
    _ = ((squares a).product (squares b)).card := congrArg Finset.card image
    _ = _ := Finset.card_product ..

/-- Cardinality of the wheel ending at 19, counted componentwise by CRT. -/
theorem wheel19 : (squares 77597520).card=362880 := by
  change (squares (((((((16*3)*5)*7)*11)*13)*17)*19)).card=_
  repeat rw [count_crt (by decide)]
  decide +kernel

/-- The arithmetic bound used for at most 2^48 row height, with the split
point D = floor sqrt(K/R). It counts exact square tests. -/
theorem budget48 :
    let K : ℕ := 2^47-1
    let R : ℕ := 362880
    let M : ℕ := 77597520
    let D := (K/R).sqrt
    let bound := 5*K*R/(3*M)+D*R+K/D
    D=19693 ∧ bound=1111209694287 ∧ 126*bound<K := by
  have h : 19693=( (2^47-1)/362880 : ℕ).sqrt := Nat.eq_sqrt'.mpr (by decide)
  dsimp only
  rw [←h]
  decide

end PrimeFactors.SeedGapSieve
