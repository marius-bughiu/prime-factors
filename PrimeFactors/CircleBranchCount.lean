import PrimeFactors.SphereCircleIdentity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! Nonunit differences on a circle whose target has opposite quadratic
characters at the two prime factors. -/
namespace PrimeFactors.CircleBranchCount

open Finset ThreeSquareRadiusCounts SphereCircleIdentity
open scoped Classical

/-- The public test on one residue uses a gcd with the modulus. -/
noncomputable def marked (n : ℕ) [NeZero n] (a : ℤ) : Finset (ZMod n) :=
  univ.filter fun x => ¬ IsUnit ((a : ZMod n)-x^2)

/-- A negative Jacobi symbol certifies exactly one local square. -/
theorem opposite {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] {a : ℤ}
    (neg : jacobiSym a (p*q)= -1) :
    (legendreSym p a=1 ∧ legendreSym q a= -1) ∨
    (legendreSym p a= -1 ∧ legendreSym q a=1) := by
  have product : legendreSym p a * legendreSym q a= -1 := by
    simpa only [jacobiSym.mul_right' a hp.out.ne_zero hq.out.ne_zero,
      ← jacobiSym.legendreSym.to_jacobiSym] using neg
  have pn : (a : ZMod p)≠0 := fun h => by
    simp [(legendreSym.eq_zero_iff p a).mpr h] at product
  have qn : (a : ZMod q)≠0 := fun h => by
    simp [(legendreSym.eq_zero_iff q a).mpr h] at product
  rcases legendreSym.eq_one_or_neg_one p pn with h|h <;>
    rcases legendreSym.eq_one_or_neg_one q qn with g|g <;> simp_all

noncomputable def roots (p : ℕ) [NeZero p] (a : ℤ) : Finset (ZMod p) :=
  univ.filter fun x => x^2=(a : ZMod p)

theorem roots_count {p : ℕ} [Fact p.Prime] (odd : p≠2) (a : ℤ) :
    ((roots p a).card : ℤ)=legendreSym p a+1 := by
  simpa only [roots,Set.toFinset_setOf] using legendreSym.card_sqrts p odd a

/-- Inclusion–exclusion on the product of the two local root sets. This also
handles unit targets with equal local signs. -/
theorem union_count {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (a : ℤ) :
    (marked (p*q) a).card + (roots p a).card*(roots q a).card =
      (roots p a).card*q+p*(roots q a).card := by
  let e := ZMod.chineseRemainder cop
  let A := roots p a ×ˢ (univ : Finset (ZMod q))
  let B := (univ : Finset (ZMod p)) ×ˢ roots q a
  have eqn : (marked (p*q) a).map e.toEquiv.toEmbedding=A∪B := by
    ext z
    obtain ⟨x,rfl⟩ := e.surjective z
    simp only [mem_map_equiv,Equiv.symm_apply_apply,marked,mem_filter,mem_univ,true_and]
    rw [← isUnit_map_iff e, map_sub, map_pow, map_intCast, Prod.isUnit_iff]
    simp [A,B,roots,isUnit_iff_ne_zero,sub_eq_zero,eq_comm]
    have leftEq : (0:ZMod p)=(a : ZMod p)-(e x).1^2 ↔ (a : ZMod p)=(e x).1^2 :=
      eq_comm.trans sub_eq_zero
    have rightEq : (0:ZMod q)=(a : ZMod q)-(e x).2^2 ↔ (a : ZMod q)=(e x).2^2 :=
      eq_comm.trans sub_eq_zero
    rw [leftEq,rightEq]
    tauto
  have inter : A∩B=roots p a ×ˢ roots q a := by
    ext z
    simp [A,B]
  have h := card_union_add_card_inter A B
  rw [←eqn,card_map,inter] at h
  simpa only [A,B,card_product,card_univ,ZMod.card] using h

/-- Half the count gives one prime exactly. Every counted residue has a
proper, publicly checkable gcd, since the other local target is a nonsquare. -/
theorem half_count {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a : ℤ} (neg : jacobiSym a (p*q)= -1) :
    ((marked (p*q) a).card=2*q ∧ legendreSym p a=1 ∧ legendreSym q a= -1) ∨
    ((marked (p*q) a).card=2*p ∧ legendreSym p a= -1 ∧ legendreSym q a=1) := by
  have h := union_count ((Nat.coprime_primes hp.out hq.out).mpr diff) a
  have P := roots_count op a
  have Q := roots_count oq a
  rcases opposite neg with ⟨s,t⟩|⟨s,t⟩
  · left
    rw [s] at P
    rw [t] at Q
    rw [show (roots p a).card=2 by omega,show (roots q a).card=0 by omega] at h
    exact ⟨by simpa using h,s,t⟩
  · right
    rw [s] at P
    rw [t] at Q
    rw [show (roots p a).card=0 by omega,show (roots q a).card=2 by omega] at h
    exact ⟨by simpa [Nat.mul_comm] using h,s,t⟩

theorem never_square {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) {a : ℤ} (neg : jacobiSym a (p*q)= -1) (x : ZMod (p*q)) :
    (a : ZMod (p*q))-x^2≠0 := by
  let e := ZMod.chineseRemainder ((Nat.coprime_primes hp.out hq.out).mpr diff)
  intro zero
  have eqn := congrArg e (sub_eq_zero.mp zero)
  rw [map_intCast,map_pow] at eqn
  rcases opposite neg with h|h
  · apply ((legendreSym.eq_neg_one_iff q).mp h.2)
    exact (isSquare_iff_exists_sq _).mpr ⟨(e x).2,congrArg Prod.snd eqn⟩
  · apply ((legendreSym.eq_neg_one_iff p).mp h.1)
    exact (isSquare_iff_exists_sq _).mpr ⟨(e x).1,congrArg Prod.fst eqn⟩

/-- Every public mark gives a proper factor immediately by a gcd. -/
theorem proper_gcd {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) {a : ℤ} (neg : jacobiSym a (p*q)= -1) (x : ZMod (p*q)) :
    let z := ((a : ZMod (p*q))-x^2).val
    x∈marked (p*q) a ↔ 1<z.gcd (p*q) ∧ z.gcd (p*q)<p*q := by
  let w := (a : ZMod (p*q))-x^2
  have nz : w.val≠0 := fun zero => never_square diff neg x (ZMod.val_injective _ (zero.trans ZMod.val_zero.symm))
  have small := (Nat.gcd_le_left (p*q) (Nat.pos_of_ne_zero nz)).trans_lt (ZMod.val_lt w)
  have pos := Nat.gcd_pos_of_pos_right w.val (Nat.mul_pos hp.out.pos hq.out.pos)
  have unit : IsUnit w ↔ w.val.gcd (p*q)=1 := by
    simpa only [ZMod.natCast_zmod_val,Nat.Coprime] using ZMod.isUnit_iff_coprime w.val (p*q)
  change x∈marked (p*q) a ↔ 1<w.val.gcd (p*q) ∧ w.val.gcd (p*q)<p*q
  simp only [marked,mem_filter,mem_univ,true_and]
  change (¬ IsUnit w) ↔ _
  rw [unit]
  omega

end PrimeFactors.CircleBranchCount
