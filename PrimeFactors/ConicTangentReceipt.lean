import PrimeFactors.ConicTangentLattice
import Mathlib.Tactic.NormNum.LegendreSymbol

/-! Public arithmetic checks for a complete, positive-coordinate signed
conic chart. The two full-size fixture products use M=N in every chart. -/
namespace PrimeFactors.ConicTangentReceipt

/-- Candidate order used by the signed chart selector. -/
noncomputable def targets (n : ℕ) : List ℤ :=
  (([-1,2,-2,3,-3,6,-6] : List ℤ).filter fun d => jacobiSym d n=1).take 3

/-- Absolute coefficients, height numerator, absolute multiplier and
sign of the quadratic term in each unit-reduced chart. -/
abbrev Shape := ℕ × ℕ × ℕ × ℕ × ℤ

def shapes (n : ℕ) (d : ℤ) : List Shape :=
  if d<0 then
    let m := if d = -6 ∧ n%3≠1 then 2 else 1
    [(1,d.natAbs,m,m,-1),(d.natAbs,1,m,m,-1)]
  else
    let height := if d=2 then 2 else if d=3 then 1 else 4
    if d=2 ∨ n%3=1 then [(d.natAbs,1,height,1,1)] else [(1,d.natAbs,height,1,1)]

theorem physical_count {h : ℕ} [NeZero h] {a b M t c : ZMod h}
    (h2 : IsUnit (2 : ZMod h)) (hb : IsUnit b) (ht : IsUnit t) (hc : IsUnit c)
    (slope : b*t^2=a) (total : b*c=M) :
    Nat.card {v : ZMod h × ZMod h // b*v.2^2-a*v.1^2=M}=Nat.totient h := by
  classical
  rw [Nat.card_eq_fintype_card]
  apply (Fintype.card_congr (Equiv.subtypeEquivRight (q:=fun v : ZMod h × ZMod h =>
      v.2^2-t^2*v.1^2=c) ?_)).trans (ConicTangentLattice.split_count h2 ht hc)
  intro v
  rw [←slope,←total,mul_assoc b (t^2),←mul_sub,hb.mul_right_inj]

theorem totient_step {a p s : ℕ} (h : Nat.totient a=s) (prime : p.Prime) (cop : a.Coprime p) :
    Nat.totient (a*p)=s*(p-1) := by rw [Nat.totient_mul cop, h, Nat.totient_prime prime]

/-- The height and radius inequalities determine the two integer roots
used by the chart scanner. The physical count identifies how many
affine classes the finite block bound must cover. -/
structure Chart (n a b numerator X W h phi ordinary upper : ℕ) (sign : ℤ) : Prop where
  modulus : 0<h ∧ h≤W
  range : 2*a*X^2 ≤ numerator*n ∧ numerator*n < 2*a*(X+1)^2
  radius : (8*a*W^3)^2 ≤ b*n ∧ b*n < (8*a*(W+1)^3)^2
  ordinaryCount : ordinary=(X-1)/W+1
  upperCount : upper=phi*((X-1)/(h*(W-h+1))+1)
  classes : Nat.card {v : ZMod h × ZMod h //
    (b:ZMod h)*v.2^2-(sign:ZMod h)*a*v.1^2=(n:ZMod h)}=phi

theorem Chart.budget {n a b num X W h phi ordinary upper : ℕ} {sign : ℤ}
    (cert : Chart n a b num X W h phi ordinary upper sign) {ι : Type*} (cls : Finset ι)
    (size : cls.card=phi) (start stride blocks : ι → ℕ) (sp : ∀ v ∈ cls, 0<start v)
    (st : ∀ v ∈ cls, h*(W-h+1)≤stride v)
    (last : ∀ v ∈ cls, blocks v≠0 → start v+(blocks v-1)*stride v≤X) :
    ∑ v ∈ cls, blocks v ≤ upper := by
  rw [cert.upperCount,←size]
  exact ConicTangentLattice.block_count_bound cls start stride blocks (Nat.mul_pos cert.modulus.1
    (Nat.zero_lt_succ _)) sp st last

/-- Each physical residue class is indexed once. Its first block starts
at a positive position. Subsequent starts have the actual integer stride
hg⌊W/g⌋, including rounding. The last start must lie in the chart. -/
def Counted (X W h phi actual : ℕ) : Prop :=
  ∃ start g blocks : Fin phi → ℕ, actual=∑ v, blocks v ∧
    (∀ v, 0<start v) ∧ (∀ v, 0<g v ∧ g v≤h) ∧
    (∀ v, blocks v≠0 → start v+(blocks v-1)*(h*g v*(W/g v))≤X)

theorem Chart.counted {n a b num X W h phi ordinary upper actual : ℕ} {sign : ℤ}
    (cert : Chart n a b num X W h phi ordinary upper sign)
    (run : Counted X W h phi actual) : actual≤upper := by
  obtain ⟨start,g,blocks,rfl,positive,bounds,last⟩ := run
  exact cert.budget Finset.univ (by simp) start (fun v => h*g v*(W/g v)) blocks
    (fun v _ => positive v) (fun v _ =>
      ConicTangentLattice.stride_lower (bounds v).1 (bounds v).2 cert.modulus.2)
    (fun v _ => last v)

end PrimeFactors.ConicTangentReceipt
