import PrimeFactors.CompleteOffsetWork
import Mathlib.Tactic.NormNum.Prime

namespace PrimeFactors.CompleteOffsetExample
open CompleteOffsetSearch CompleteOffsetWork

/-- The three public digits are independently checked by bounding the floor
square roots between successive integer squares. -/
theorem digits : (117449:ℕ).sqrt=342 ∧ 117449-342^2=485 ∧ height 485=25 := by
  refine ⟨(Nat.eq_sqrt.mpr (by decide +kernel)).symm, by decide, ?_⟩
  exact (Nat.eq_sqrt.mpr (by decide +kernel)).symm

attribute [local irreducible] slots rawSlots height

private def moduli : List ℕ := [3,5,7,11,13,17,19]

private def squareResidue (p m : ℕ) : Bool :=
  (List.range p).any fun x => x*x%p == m%p

private theorem square_passes (p d m : ℕ) (pos : 0<p) (eq : d^2=m) :
    squareResidue p m = true := by
  refine List.any_eq_true.mpr ⟨d%p,List.mem_range.mpr (Nat.mod_lt _ pos),?_⟩
  simp only [beq_iff_eq, ← Nat.mul_mod, ←eq,pow_two]

/-- A true probe hit must pass every listed finite modular square test. -/
private def survives (j k : ℕ) : Bool :=
  let S := j+2*342*k
  let target := 4*k^2*117449
  decide (0<j ∧ 0<k ∧ k≤342*j/485+1 ∧ j.Coprime k ∧ target≤S^2) &&
    moduli.all (fun p => squareResidue p (S^2-target))

private theorem passed {j k f : ℕ} (inside : (j,k) ∈ slots 342 485)
    (found : probe 117449 342 j k=some f) : survives j k=true := by
  obtain ⟨⟨jp,_⟩,⟨kp,limit⟩,cop⟩ := (mem_slots (T:=342) (h:=485) (j:=j) (k:=k)).mp inside
  unfold probe at found
  dsimp only at found
  split at found
  next good =>
    obtain ⟨nonneg,sq,_,_⟩ := good
    rw [survives,Bool.and_eq_true]
    refine ⟨decide_eq_true ⟨jp,kp,limit,cop,nonneg⟩,?_⟩
    apply List.all_eq_true.mpr
    intro p mem
    have positive : 0<p := by simp only [moduli,List.mem_cons,List.not_mem_nil,or_false] at mem; omega
    exact square_passes p _ _ positive sq
  next => contradiction

private theorem table : ∀ j : Fin 26, ∀ k : Fin 19,
    survives j.val k.val=true → j.val=17 ∧ k.val=12 := by decide +kernel

/-- Exactly one primitive slot in the public, sharp schedule can return a
proper factor. The integer 257 is the actual output of the signed probe. -/
theorem only_hit (j k f : ℕ) :
    let T := (117449:ℕ).sqrt
    let h := 117449-T^2
    ((j,k) ∈ slots T h ∧ probe 117449 T j k=some f) ↔ j=17 ∧ k=12 ∧ f=257 := by
  dsimp only
  rw [digits.1,digits.2.1]
  have hit : probe 117449 342 17 12=some 257 := by decide +kernel
  constructor
  · rintro ⟨inside,found⟩
    obtain ⟨⟨_,hj⟩,⟨_,hk⟩,_⟩ := (mem_slots (T:=342) (h:=485) (j:=j) (k:=k)).mp inside
    rw [digits.2.2] at hj
    have jlt : j<26 := by omega
    have klt : k<19 := by omega
    obtain ⟨rj,rk⟩ := table ⟨j,jlt⟩ ⟨k,klt⟩ (passed inside found)
    change j=17 at rj
    change k=12 at rk
    subst j
    subst k
    exact ⟨rfl,rfl,Option.some.inj (found.symm.trans hit)⟩
  · rintro ⟨rfl,rfl,rfl⟩
    refine ⟨(mem_slots (T:=342) (h:=485) (j:=17) (k:=12)).mpr ?_,hit⟩
    rw [digits.2.2]
    decide

/-- Deleting the extra multiplier leaves this entire bounded scan unsuccessful. -/
theorem no_hit_without_endpoint {j k f : ℕ} (inside : (j,k) ∈ slots 342 485)
    (ordinary : k≤342*j/485) : probe 117449 342 j k ≠ some f := by
  intro found
  have unique := only_hit j k f
  dsimp only at unique
  rw [digits.1,digits.2.1] at unique
  obtain ⟨rfl,rfl,_⟩ := unique.mp ⟨inside,found⟩
  omega

/-- At offset 17 the public quotient is 11. The extra slot has signed
residual −6 and square discriminant 1. Its output and cofactor are prime. -/
theorem endpoint_and_factors :
    (342:ℕ)*17/485=11 ∧ (342:ℤ)*17-485*12= -6 ∧
    (17:ℤ)^2+4*12*(342*17-485*12)=1 ∧
    Nat.Prime 257 ∧ Nat.Prime 457 ∧ (257:ℕ)*457=117449 := by norm_num

end PrimeFactors.CompleteOffsetExample
