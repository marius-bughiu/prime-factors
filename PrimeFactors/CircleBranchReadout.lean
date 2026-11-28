import PrimeFactors.CircleBranchCount
import PrimeFactors.CircleCoordinateFibers

/-! For a publicly certified negative-Jacobi target, the projection of a
modular circle distinguishes one prime even though its total size is constant. -/
namespace PrimeFactors.CircleBranchReadout

open Finset CircleBranchCount CircleCoordinateFibers SphereCircleIdentity ThreeSquareRadiusCounts
open scoped Classical

theorem single_count {p : ℕ} [Fact p.Prime] (op : p≠2) (a : ℤ) :
    ((level (ZMod p) (a : ZMod p) 1).card : ℤ)=legendreSym p a+1 := by
  have odd : (2:ZMod p)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have eqn : level (ZMod p) (a : ZMod p) 1=roots p a := by
    ext x
    simp [roots,one_iff odd]
  rw [eqn,roots_count op]

/-- If the Jacobi symbol of the target is negative, the number of first
coordinates with exactly two lifts is the local circle size at the prime
where the target is a nonsquare. -/
theorem readout {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a : ℤ} (neg : jacobiSym a (p*q)= -1) :
    let T := (level (ZMod (p*q)) (a : ZMod (p*q)) 2).card
    (legendreSym p a=1 ∧ legendreSym q a= -1 ∧ (T:ℤ)=q-sign q) ∨
    (legendreSym p a= -1 ∧ legendreSym q a=1 ∧ (T:ℤ)=p-sign p) := by
  dsimp only
  have cop := (Nat.coprime_primes hp.out hq.out).mpr diff
  have hist := (histogram cop (a : ZMod (p*q))).2.1
  simp only [map_intCast,Prod.fst_intCast,Prod.snd_intCast] at hist
  have P := single_count op a
  have Q := single_count oq a
  rcases opposite neg with ⟨s,t⟩|⟨s,t⟩
  · refine Or.inl ⟨s,t,?_⟩
    rw [s] at P
    rw [t] at Q
    have localQ := local_counts (a : ZMod q)
    rw [show (level (ZMod q) (a : ZMod q) 1).card=0 by omega] at localQ hist
    rw [show (level (ZMod p) (a : ZMod p) 1).card=2 by omega] at hist
    simp only [Nat.zero_add] at localQ
    simp only [mul_zero,add_zero,←localQ] at hist
    rw [hist]
    apply prime_unit oq
    intro h
    rw [(legendreSym.eq_zero_iff q a).mpr h] at t
    contradiction
  · refine Or.inr ⟨s,t,?_⟩
    rw [s] at P
    rw [t] at Q
    have localP := local_counts (a : ZMod p)
    rw [show (level (ZMod p) (a : ZMod p) 1).card=0 by omega] at localP hist
    rw [show (level (ZMod q) (a : ZMod q) 1).card=2 by omega] at hist
    simp only [Nat.zero_add] at localP
    simp only [zero_mul,zero_add,mul_comm _ 2,←localP] at hist
    rw [hist]
    apply prime_unit op
    intro h
    rw [(legendreSym.eq_zero_iff p a).mpr h] at s
    contradiction

/-- One of the two integers adjacent to the supplied count is a factor. -/
theorem adjacent {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a : ℤ} (neg : jacobiSym a (p*q)= -1) :
    let T : ℤ := (level (ZMod (p*q)) (a : ZMod (p*q)) 2).card
    ∃ r : ℕ, (r=p ∨ r=q) ∧ ((r:ℤ)=T-1 ∨ (r:ℤ)=T+1) := by
  rcases readout diff op oq neg with h|h
  · refine ⟨q,Or.inr rfl,?_⟩
    dsimp only
    rw [h.2.2]
    unfold sign
    split <;> omega
  · refine ⟨p,Or.inl rfl,?_⟩
    dsimp only
    rw [h.2.2]
    unfold sign
    split <;> omega

end PrimeFactors.CircleBranchReadout
