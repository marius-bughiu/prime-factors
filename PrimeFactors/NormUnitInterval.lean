import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Reduce an indefinite norm representation while retaining its prescribed
modular root. The two neighboring norm-one units give the interval endpoint. -/
namespace PrimeFactors.NormUnitInterval

/-- In each represented root class there is a point with
x²+D y² ≤ uN for any positive integral unit u+v√D of norm one. -/
theorem reduce {N : ℕ} {D m u v x y : ℤ} {r : ZMod N} (dp : 0<D) (up : 0<u) (vp : 0<v)
    (pell : u^2-D*v^2=1) (unitNorm : m=1 ∨ m= -1) (root : r^2=D)
    (norm : x^2-D*y^2=m*N) (point : (x:ZMod N)=r*y) :
    ∃ a b : ℤ, a^2-D*b^2=m*N ∧ (a:ZMod N)=r*b ∧ a^2+D*b^2≤u*N := by
  classical
  let E (a b : ℤ) := a^2+D*b^2
  let P (j : ℕ) := ∃ a b : ℤ, a^2-D*b^2=m*N ∧ (a:ZMod N)=r*b ∧ E a b=j
  have pos (a b : ℤ) : 0≤E a b := by dsimp [E]; positivity
  have existsP : ∃ j, P j :=
    ⟨(E x y).toNat,x,y,norm,point,(Int.toNat_of_nonneg (pos x y)).symm⟩
  obtain ⟨a,b,na,pt,least⟩ := Nat.find_spec existsP
  have best {A B : ℤ} (nb : A^2-D*B^2=m*N) (pb : (A:ZMod N)=r*B) : E a b≤E A B := by
    have bound := Nat.find_min' existsP (show P (E A B).toNat from
      ⟨A,B,nb,pb,(Int.toNat_of_nonneg (pos A B)).symm⟩)
    simpa only [least,Int.toNat_of_nonneg (pos A B)] using (Int.ofNat_le.mpr bound)
  have neighbor (t : ℤ) (unit : u^2-D*t^2=1) :
      E a b ≤ (u^2+D*t^2)*E a b+4*D*u*t*a*b := by
    let A := u*a+D*t*b
    let B := u*b+t*a
    have nb : A^2-D*B^2=m*N := calc
      _ = (u^2-D*t^2)*(a^2-D*b^2) := by dsimp [A,B]; ring
      _ = _ := by rw [unit,na,one_mul]
    have pb : (A:ZMod N)=r*B := by dsimp [A,B]; push_cast; rw [pt,←root]; ring
    calc
      _ ≤ E A B := best nb pb
      _ = _ := by dsimp [E,A,B]; ring
  have plus := neighbor v pell
  have minus := neighbor (-v) (by simpa using pell)
  have scale : 0<2*D*v := by positivity
  have lower : -(v*E a b)≤2*u*a*b := by
    apply (mul_le_mul_left scale).mp
    nlinarith only [plus,congrArg (· * E a b) pell]
  have upper : 2*u*a*b≤v*E a b := by
    apply (mul_le_mul_left scale).mp
    nlinarith only [minus,congrArg (· * E a b) pell]
  have sq := mul_le_mul_of_nonneg_left (sq_le_sq' lower upper) dp.le
  have identity : u^2*(E a b)^2=D*(2*u*a*b)^2+(u*(m*N))^2 := by rw [← na]; dsimp [E]; ring
  have unitSq : (u*(m*N))^2=(u*(N:ℤ))^2 := by rcases unitNorm with e|e <;> simp [e]
  rw [unitSq] at identity
  have squared : (E a b)^2≤(u*(N:ℤ))^2 := by
    nlinarith only [sq,identity,congrArg (· * (E a b)^2) pell]
  exact ⟨a,b,na,pt, (sq_le_sq₀ (pos a b) (mul_nonneg up.le (Int.natCast_nonneg N))).mp squared⟩

end PrimeFactors.NormUnitInterval
