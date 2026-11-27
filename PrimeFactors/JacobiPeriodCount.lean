import PrimeFactors.ReducedSlopes
import PrimeFactors.SingleBaseRepeat

/-! Exact number of units passing a single public power test with exponent
`(N−1)t`. The count is for all units; applying it as a probability requires
a uniform choice of a unit. -/

namespace PrimeFactors.JacobiPeriodCount

open Finset

/-- Number of units passing the test at the candidate multiplier `t`. -/
noncomputable def passing (N t : ℕ) [NeZero N] : ℕ :=
  (univ.filter fun x : (ZMod N)ˣ => x^((N-1)*t)=1).card

/-- Product of the two coprime quotients left after removing the common
divisor of the prime predecessors. -/
def residualProduct (p q : ℕ) : ℕ :=
  let g := (p-1).gcd (q-1)
  ((p-1)/g)*((q-1)/g)

private theorem local_gcd (P D t : ℕ) (pos : 0<P) :
    (D*t).gcd P = P.gcd D * (t.gcd (P / P.gcd D)) := by
  let g := P.gcd D
  let r := P/g
  let c := D/g
  have gp : 0<g := Nat.gcd_pos_of_pos_left D pos
  have eqP : g*r=P := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have eqD : g*c=D := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have cop : c.Coprime r := (Nat.coprime_div_gcd_div_gcd gp).symm
  calc
    _ = (g*(c*t)).gcd (g*r) := by rw [←mul_assoc,eqD,eqP]
    _ = _ := by rw [Nat.gcd_mul_left,Nat.Coprime.gcd_mul_left_cancel t cop]

/-- A candidate multiplier passes for exactly `g² gcd(t,R)` units.
This includes t=0 and all distinct prime pairs. -/
theorem exact_count {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) (t : ℕ) :
    passing (p*q) t = ((p-1).gcd (q-1))^2 * (t.gcd (residualProduct p q)) := by
  let g := (p-1).gcd (q-1)
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ (Nat.sub_pos_of_lt pp.one_lt)
  have cop : ((p-1)/g).Coprime ((q-1)/g) := Nat.coprime_div_gcd_div_gcd gp
  have m : (q-1).gcd (p*q-1)=g := by
    rw [Nat.mul_comm p q,gcd_predecessor_product qp.pos pp.pos,Nat.gcd_comm]
  rw [passing,SingleBaseRepeat.gap_count pp qp ne,
    local_gcd (p-1) (p*q-1) t (Nat.sub_pos_of_lt pp.one_lt),
    local_gcd (q-1) (p*q-1) t (Nat.sub_pos_of_lt qp.one_lt),m,gcd_predecessor_product pp.pos qp.pos]
  change g * t.gcd ((p-1)/g) * (g * t.gcd ((q-1)/g)) = g^2 * t.gcd (((p-1)/g)*((q-1)/g))
  rw [cop.gcd_mul]
  ring

/-- The fraction passing a single public power test is `gcd(R,t)/R`,
expressed as an integer equality. -/
theorem exact_fraction {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) (t : ℕ) :
    passing (p*q) t * residualProduct p q =
      (p*q).totient * ((residualProduct p q).gcd t) := by
  let g := (p-1).gcd (q-1)
  have pg : g*((p-1)/g)=p-1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have qg : g*((q-1)/g)=q-1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have size : g^2*residualProduct p q = (p*q).totient := by
    rw [Nat.totient_mul ((Nat.coprime_primes pp qp).mpr ne),Nat.totient_prime pp,Nat.totient_prime qp]
    calc
      _ = (g*((p-1)/g))*(g*((q-1)/g)) := by unfold residualProduct; dsimp only [g]; ring
      _ = _ := by rw [pg,qg]
  rw [exact_count pp qp ne t,Nat.gcd_comm t (residualProduct p q),←size]
  change g^2 * _ * _ = g^2 * _ * _
  ring

/-- At 221 = 13 × 17, the candidate 6 passes for half of all units
and its double passes for all 192. -/
theorem control_221 : passing 221 6 = 96 ∧ passing 221 12 = 192 := by
  change passing (13*17) 6 = 96 ∧ passing (13*17) 12 = 192
  rw [exact_count (p:=13) (q:=17) (by decide) (by decide) (by decide) 6,
    exact_count (p:=13) (q:=17) (by decide) (by decide) (by decide) 12]
  decide

end PrimeFactors.JacobiPeriodCount
