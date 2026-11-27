import PrimeFactors.Certificate
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-! Both mixed products (p−1)(q+1) and (p+1)(q−1) lie at the same
distance from pq−1. If a positive scale times a square equals either product,
two neighboring roots suffice to recover that distance. -/

namespace PrimeFactors.MixedSquareScale

/-- Floor of the square root after division by the supplied scale. -/
def root (n t : ℕ) := (n/t).sqrt

/-- Distance from N−1 to the nearer of the two scaled squares. -/
def gap (n t : ℕ) :=
  min (Nat.dist (n-1) (t*(root n t)^2)) (Nat.dist (n-1) (t*(root n t+1)^2))

private theorem geometry {p q : ℕ} (hp : 1<p) (order : p<q) (bal : q<2*p) :
    (p-1)*(q+1)+(q-p)+1=p*q ∧
    (p+1)*(q-1)=(p-1)*(q+1)+2*(q-p) ∧
    (q-p)^2 < (p-1)*(q+1) := by
  obtain ⟨a,pa⟩ := Nat.exists_eq_add_of_le (show 1≤p by omega)
  obtain ⟨g,qg⟩ := Nat.exists_eq_add_of_le order.le
  have pg : q-p=g := by omega
  have pl : p-1=a := by omega
  have ql : q-1=a+g := by omega
  rw [pg,pl,ql,qg,pa]
  constructor
  · ring
  constructor
  · ring
  · have ga : g≤a := by omega
    have ap : 0<a := by omega
    have h := Nat.mul_lt_mul_of_le_of_lt ga (show g<1+a+g+1 by omega) ap
    simpa only [pow_two] using h

/-- Distinct scaled squares cannot both lie between L and L+2G if L>G². -/
private theorem impossible_pair {l g t a b : ℕ} (tp : 0<t) (large : g^2<l)
    (ab : a<b) (lo : l≤t*a^2) (hi : t*b^2≤l+2*g) : False := by
  have amplified : t*a^2 ≤ (t*a)^2 := calc
    _ ≤ t*(t*a^2) := Nat.le_mul_of_pos_left _ tp
    _ = _ := by ring
  have ga : g<t*a := by
    by_contra! fail
    have sq := Nat.pow_le_pow_left fail 2
    omega
  have spacing : t*a^2+2*g < t*(a+1)^2 := by nlinarith only [ga,tp]
  have mono := Nat.mul_le_mul_left t (Nat.pow_le_pow_left (show a+1≤b by omega) 2)
  omega

/-- At most one scaled square can lie in the whole interval between the mixed products. -/
theorem band_unique {p q t a b : ℕ} (hp : 1<p) (order : p<q) (bal : q<2*p) (tp : 0<t)
    (a_lo : (p-1)*(q+1) ≤ t*a^2) (a_hi : t*a^2 ≤ (p+1)*(q-1))
    (b_lo : (p-1)*(q+1) ≤ t*b^2) (b_hi : t*b^2 ≤ (p+1)*(q-1)) : a=b := by
  obtain ⟨_,upper,large⟩ := geometry hp order bal
  rw [upper] at a_hi b_hi
  rcases lt_trichotomy a b with lt | eq | gt
  · exact False.elim (impossible_pair tp large lt a_lo b_hi)
  · exact eq
  · exact False.elim (impossible_pair tp large gt b_lo a_hi)

/-- Every root of either mixed product is the public floor or its successor.
This includes scale one and does not require primality or parity. -/
theorem root_correct {p q t z : ℕ} (hp : 1<p) (order : p<q) (bal : q<2*p) (tp : 0<t)
    (square : t*z^2=(p-1)*(q+1) ∨ t*z^2=(p+1)*(q-1)) :
    z=root (p*q) t ∨ z=root (p*q) t+1 := by
  obtain ⟨center,upper,large⟩ := geometry hp order bal
  let r := root (p*q) t
  have lo : (p-1)*(q+1) ≤ t*z^2 := by omega
  have hi : t*z^2 ≤ (p-1)*(q+1)+2*(q-p) := by omega
  have floor : t*r^2 ≤ p*q := by
    rw [Nat.mul_comm]
    exact (Nat.le_div_iff_mul_le tp).mp (Nat.sqrt_le' _)
  have ceil : p*q < t*(r+1)^2 := by
    rw [Nat.mul_comm t]
    exact (Nat.div_lt_iff_lt_mul tp).mp (Nat.lt_succ_sqrt' _)
  by_cases low : z<r
  · exact False.elim (impossible_pair tp large low lo (by omega))
  by_cases high : r+1<z
  · exact False.elim (impossible_pair tp large high (by omega) hi)
  change z=r ∨ z=r+1
  omega

/-- Taking the nearer distance recovers the true gap precisely at the
positive scales for which at least one of the mixed products is a square times the scale. -/
theorem gap_iff {p q t : ℕ} (hp : 1<p) (order : p<q) (bal : q<2*p) (tp : 0<t) :
    gap (p*q) t=q-p ↔ ∃ z : ℕ, t*z^2=(p-1)*(q+1) ∨ t*z^2=(p+1)*(q-1) := by
  obtain ⟨center,upper,_⟩ := geometry hp order bal
  let D (i : ℕ) := Nat.dist (p*q-1) (t*i^2)
  let r := root (p*q) t
  have eqv (i : ℕ) : D i=q-p ↔ t*i^2=(p-1)*(q+1) ∨ t*i^2=(p+1)*(q-1) := by
    simp only [D,Nat.dist]
    omega
  change min (D r) (D (r+1))=q-p ↔ _
  constructor
  · intro dist
    rcases le_total (D r) (D (r+1)) with le | le
    · exact ⟨r,(eqv r).mp ((min_eq_left le).symm.trans dist)⟩
    · exact ⟨r+1,(eqv (r+1)).mp ((min_eq_right le).symm.trans dist)⟩
  · rintro ⟨z,square⟩
    have found := (eqv z).mpr square
    have best (b : ℕ) : q-p ≤ D b := by
      by_contra! below
      have near := below.le
      simp only [D,Nat.dist] at near
      have equal : z=b := band_unique hp order bal tp (by omega) (by omega) (by omega) (by omega)
      rw [←equal,found] at below
      exact (lt_irrefl _ below)
    apply le_antisymm _ (le_min (best r) (best (r+1)))
    rcases root_correct hp order bal tp square with h | h
    · change z=r at h
      rw [h] at found
      exact (min_le_left ..).trans found.le
    · change z=r+1 at h
      rw [h] at found
      exact (min_le_right ..).trans found.le

/-- The opposite endpoints at level 187 give the same prime gap. At 35
the upper mixed product is a perfect square, testing scale one explicitly. -/
theorem controls :
    ExactFactorization 187 [11,17] ∧ 5*6^2=(11-1)*(17+1) ∧ root 187 5=6 ∧ gap 187 5=6 ∧
    3*8^2=(11+1)*(17-1) ∧ root 187 3+1=8 ∧ gap 187 3=6 ∧
    ExactFactorization 35 [5,7] ∧ root 35 1+1=6 ∧ gap 35 1=2 := by
  refine ⟨by norm_num [ExactFactorization],by decide,by decide,by decide,by decide,by decide,by decide,
    by norm_num [ExactFactorization],by decide,by decide⟩

end PrimeFactors.MixedSquareScale
