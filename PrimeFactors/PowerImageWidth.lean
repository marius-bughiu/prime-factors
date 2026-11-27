import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Nat

/-! Finite size estimates for the denominator in a power-image count. -/
namespace PrimeFactors.PowerImageWidth

set_option exponentiation.threshold 4096

/-- The difference between the product and the product of its predecessors
is exactly the sum of the two inputs less one. -/
theorem offset {p q : ℕ} (hp : 0<p) (hq : 0<q) :
    p*q=(p-1)*(q-1)+(p+q-1) := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  rw [Nat.succ_sub_one,Nat.succ_sub_one,show a.succ+b.succ-1=a+b+1 by omega]
  simp only [Nat.succ_eq_add_one]
  ring

/-- A count and its rate imply the stated bound on the product of the two image sizes. -/
theorem image_cap {X Y count : ℕ} (cap : count≤48) (rate : X*Y≤count*2^503) :
    X*Y≤48*2^503 := rate.trans (Nat.mul_le_mul_right _ cap)

/-- Full-width bound with the actual denominator divisor and local image sizes.
Positivity prevents divisibility by a zero upper bound. -/
theorem full {p q X Y b : ℕ} (hp : 2≤p) (hq : 2≤q) (wp : p<2^1024) (wq : q<2^1024)
    (width : 2^2047≤p*q) (gcd_two : (p-1).gcd (q-1)=2)
    (xp : 0<X) (yp : 0<Y) (images : X*Y≤48*2^503)
    (den : b∣(p-1).gcd (q-1)*X*Y) :
    2*b^2*(p*q-(p-1)*(q-1)) < (p-1)*(q-1) := by
  rw [gcd_two,Nat.mul_assoc] at den
  have bc := (Nat.le_of_dvd (Nat.mul_pos (by decide : 0<2) (Nat.mul_pos xp yp)) den).trans
    (Nat.mul_le_mul_left 2 images)
  have s := offset (p:=p) (q:=q) (by omega) (by omega)
  have dist : p*q-(p-1)*(q-1)≤2^1025 := by omega
  have floor : 2^2046≤(p-1)*(q-1) := by omega
  calc
    _ ≤ (2*(2*(48*2^503))^2)*2^1025 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left bc 2)) dist
    _ < 2^2046 := by decide +kernel
    _ ≤ _ := floor

/-- Entry point for a count of at most 48 with the finite per-count image bound. -/
theorem from_rate {p q X Y b count : ℕ} (hp : 2≤p) (hq : 2≤q) (wp : p<2^1024)
    (wq : q<2^1024) (width : 2^2047≤p*q) (gcd_two : (p-1).gcd (q-1)=2)
    (xp : 0<X) (yp : 0<Y) (cap : count≤48) (rate : X*Y≤count*2^503)
    (den : b∣(p-1).gcd (q-1)*X*Y) :
    2*b^2*(p*q-(p-1)*(q-1)) < (p-1)*(q-1) :=
  full hp hq wp wq width gcd_two xp yp (image_cap cap rate) den

end PrimeFactors.PowerImageWidth
