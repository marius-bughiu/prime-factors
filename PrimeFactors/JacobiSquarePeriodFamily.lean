import PrimeFactors.JacobiPeriodSquareClass

/-! Fifty admissible linear forms separate the first successful square scale from
the least shared Jacobi period. The final unboundedness statement takes the
prime-hitting assertion for the forms as an explicit hypothesis. -/

namespace PrimeFactors.JacobiSquarePeriodFamily

open JacobiPeriodCount JacobiPeriodProbe JacobiMomentPeriod

/-- The slope of the linear form is a square and its constant term is one. -/
def form (A i t : ℕ) := (A+i)^2*t+1

instance (A i t : ℕ) : NeZero (form A i t) := ⟨Nat.succ_ne_zero _⟩

/-- One residue simultaneously avoids every prime at every one of the forms. -/
theorem admissible (A l : ℕ) (prime : l.Prime) :
    ∃ t : ℕ, ∀ i < 50, ¬ l ∣ form A i t := by
  exact ⟨0,fun i _ => by simpa [form] using prime.not_dvd_one⟩

/-- The slopes are strictly ordered, so the determinants of forms with the
common constant coefficient one are nonzero. -/
theorem slopes_lt {A i j : ℕ} (ij : i<j) : (A+i)^2 < (A+j)^2 :=
  Nat.pow_lt_pow_left (by omega) (by decide)

theorem balanced {A i j t : ℕ} (a : 150≤A) (ij : i<j) (stop : j<50) (tp : 0<t) :
    7 ≤ form A i t ∧ form A i t < form A j t ∧ form A j t < 2*form A i t := by
  have u : 150 ≤ A+i := by omega
  have near : 3*(A+j) ≤ 4*(A+i) := by omega
  have squares := Nat.pow_le_pow_left near 2
  have uu : 0 < (A+i)^2 := by positivity
  have ratio : (A+j)^2 ≤ 2*(A+i)^2 := by nlinarith only [squares,uu]
  have lower : 6 ≤ (A+i)^2 := (by decide : 6≤150^2).trans (Nat.pow_le_pow_left u 2)
  have first : 6 ≤ (A+i)^2*t :=
    lower.trans (by simpa using Nat.mul_le_mul_left ((A+i)^2) tp)
  dsimp only [form]
  exact ⟨by omega,Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right (slopes_lt ij) tp) _,
    by have h := Nat.mul_le_mul_right t ratio; rw [Nat.mul_assoc] at h; omega⟩

/-- The product of the two predecessors is a square for every parameter. -/
theorem predecessor_product (A i j t : ℕ) :
    (form A i t-1)*(form A j t-1) = (t*(A+i)*(A+j))^2 := by
  simp only [form,Nat.add_sub_cancel]
  ring

/-- Remove the common factor of the two slopes' square roots before squaring. -/
theorem period_formula {u v t : ℕ} (upos : 0<u) (tp : 0<t) :
    residualProduct (u^2*t+1) (v^2*t+1) = ((u/u.gcd v)*(v/u.gcd v))^2 := by
  let d := u.gcd v
  let a := u/d
  let b := v/d
  have dp : 0<d := Nat.gcd_pos_of_pos_left _ upos
  have da : d*a=u := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have db : d*b=v := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have cop : (a^2).Coprime (b^2) :=
    (((Nat.coprime_div_gcd_div_gcd dp).pow_left 2).pow_right 2)
  let g := t*d^2
  have gp : 0<g := Nat.mul_pos tp (pow_pos dp 2)
  have pa : u^2*t=g*a^2 := by rw [←da]; dsimp only [g]; ring
  have qb : v^2*t=g*b^2 := by rw [←db]; dsimp only [g]; ring
  change residualProduct (u^2*t+1) (v^2*t+1) = (a*b)^2
  unfold residualProduct
  dsimp only
  rw [Nat.add_sub_cancel,Nat.add_sub_cancel,pa,qb,Nat.gcd_mul_left,cop.gcd_eq_one,mul_one,
    Nat.mul_div_cancel_left _ gp,Nat.mul_div_cancel_left _ gp,mul_pow]

/-- The common factor of the roots divides their positive index gap. -/
theorem gcd_le_gap {A i j : ℕ} (ij : i<j) :
    (A+i).gcd (A+j) ≤ j-i := by
  have h := Nat.dvd_sub (Nat.gcd_dvd_right (A+i) (A+j)) (Nat.gcd_dvd_left (A+i) (A+j))
  rw [show A+j-(A+i)=j-i by omega] at h
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt ij) h

private theorem floor_bound {u v t W : ℕ} (up : 0<u) (tp : 0<t)
    (small : u.gcd v≤49) (wu : W≤u) (wv : W≤v) :
    (W/49)^4 ≤ residualProduct (u^2*t+1) (v^2*t+1) := by
  let d := u.gcd v
  have dp : 0<d := Nat.gcd_pos_of_pos_left _ up
  have atMost : W/49*d ≤ W :=
    (Nat.mul_le_mul_left (W/49) small).trans (Nat.div_mul_le_self W 49)
  have x : W/49 ≤ u/d := (Nat.le_div_iff_mul_le dp).mpr (atMost.trans wu)
  have y : W/49 ≤ v/d := (Nat.le_div_iff_mul_le dp).mpr (atMost.trans wv)
  rw [period_formula up tp,show (W/49)^4=((W/49)*(W/49))^2 by ring]
  exact Nat.pow_le_pow_left (Nat.mul_le_mul x y) 2

/-- The least period grows at least quartically in A/49, uniformly over the
index pair and over all positive parameters. -/
theorem period_lower {A i j t : ℕ} (a : 150≤A) (ij : i<j) (stop : j<50) (tp : 0<t) :
    (A/49)^4 ≤ residualProduct (form A i t) (form A j t) :=
  floor_bound (by omega) tp ((gcd_le_gap (A:=A) ij).trans (by omega)) (by omega) (by omega)

/-- The direct square search succeeds at its very first scale, even before
one asks whether the two values of the forms are prime. -/
theorem direct_first {A i j t : ℕ} (a : 150≤A) (ij : i<j) (stop : j<50) (tp : 0<t) :
    IsLeast {r : ℕ | 0<r ∧ predecessorSquareSum (form A i t*form A j t) r =
      form A i t+form A j t} 1 := by
  obtain ⟨lo,lt,bal⟩ := balanced a ij stop tp
  have pu : 0<A+i := by omega
  exact JacobiPeriodSquareClass.first_scale (by omega : 1<form A i t) lt.le bal.le
    (c:=1) (z:=((A+i)/((A+i).gcd (A+j)))*((A+j)/((A+i).gcd (A+j)))) squarefree_one
    (by simpa only [one_mul,form] using period_formula (v:=A+j) pu tp)

/-- At a prime hit, the product has square totient, the least positive
successful direct scale is one, and R is the least shared stride period. -/
theorem prime_hit {A i j t : ℕ} (a : 150≤A) (ij : i<j) (stop : j<50) (tp : 0<t)
    (pp : (form A i t).Prime) (qp : (form A j t).Prime) :
    let p := form A i t
    let q := form A j t
    let R := (((A+i)/((A+i).gcd (A+j)))*((A+j)/((A+i).gcd (A+j))))^2
    (p*q).totient = (t*(A+i)*(A+j))^2 ∧
    IsLeast {r : ℕ | 0<r ∧ predecessorSquareSum (p*q) r=p+q} 1 ∧
    IsLeast {r : ℕ | 0<r ∧ AllOffsets (completeEven (p*q)) ((p*q-1)/2) r} R := by
  dsimp only
  letI : Fact (form A i t).Prime := ⟨pp⟩
  letI : Fact (form A j t).Prime := ⟨qp⟩
  obtain ⟨lo,lt,bal⟩ := balanced a ij stop tp
  have cop := (Nat.coprime_primes pp qp).mpr lt.ne
  have pu : 0<A+i := by omega
  have eq := period_formula (v:=A+j) pu tp
  change residualProduct (form A i t) (form A j t) = _ at eq
  have positive : 0 < residualProduct (form A i t) (form A j t) := by
    have lower := period_lower a ij stop tp
    have : 0<A/49 := Nat.div_pos (by omega) (by decide)
    exact (pow_pos this _).trans_le lower
  refine ⟨?_,direct_first a ij stop tp,?_,?_⟩
  · rw [Nat.totient_mul cop,Nat.totient_prime pp,Nat.totient_prime qp,predecessor_product]
  · rw [←eq]
    exact ⟨positive,(canonical_period cop lo (lo.trans lt.le) _).mpr dvd_rfl⟩
  · rintro r ⟨rp,works⟩
    rw [←eq]
    exact Nat.le_of_dvd rp ((canonical_period cop lo (lo.trans lt.le) _).mp works)

/-- If each of the fifty-form systems has a positive parameter with two prime
values, the first direct scale is one on balanced prime products with
arbitrarily large least shared period. -/
theorem unbounded_of_prime_hits
    (hits : ∀ A, 150≤A → ∃ i j t, i<j ∧ j<50 ∧ 0<t ∧
      (form A i t).Prime ∧ (form A j t).Prime) (B : ℕ) :
    ∃ p q, p.Prime ∧ q.Prime ∧ 7≤p ∧ p<q ∧ q<2*p ∧
      predecessorSquareSum (p*q) 1=p+q ∧ B<residualProduct p q := by
  let A := 150+49*(B+1)
  have minimum : 150≤A := by dsimp [A]; omega
  obtain ⟨i,j,t,ij,stop,tp,pp,qp⟩ := hits A minimum
  obtain ⟨lo,lt,bal⟩ := balanced minimum ij stop tp
  have first := (prime_hit minimum ij stop tp pp qp).2.1.1.2
  have grows : B < A/49 := by dsimp [A]; omega
  have pos : 0<A/49 := by omega
  have power : A/49 ≤ (A/49)^4 := by
    simpa using Nat.pow_le_pow_right pos (by decide : 1≤4)
  exact ⟨_,_,pp,qp,lo,lt,bal,first,
    grows.trans_le (power.trans (period_lower minimum ij stop tp))⟩

/-- A=150, indices 0 and 6, t=1. The period value follows from the checked
prime factorization and the canonical period theorem, without a period scan. -/
theorem control :
    ExactFactorization 547606837 [22501,24337] ∧
    predecessorSquareSum 547606837 1 = 46838 ∧
    residualProduct 22501 24337 = 422500 := by
  refine ⟨?_,?_,by decide +kernel⟩
  · norm_num [ExactFactorization]
  · exact predecessorSquareSum_correct (a:=22500) (b:=24336) (d:=1) (y:=23400)
      (by decide) (by decide) (by decide) (by decide) (by decide)

/-- A=490, indices 0 and 6, t=1 gives the second scale-one benchmark. -/
theorem second_control : ExactFactorization 59068927717 [240101,246017] ∧
    predecessorSquareSum 59068927717 1 = 486118 ∧
    residualProduct 240101 246017 = 3691777600 := by
  refine ⟨?_,?_,by decide +kernel⟩
  · norm_num [ExactFactorization]
  · exact predecessorSquareSum_correct (a:=240100) (b:=246016) (d:=1) (y:=243040)
      (by decide) (by decide) (by decide) (by decide) (by decide)
/-- Spacing the roots by A keeps the relative gap between distinct forms
bounded below as A grows. -/
def spacedRoot (A i : ℕ) := (200+i)*A+1

def spacedForm (A i t : ℕ) := (spacedRoot A i)^2*t+1

instance (A i t : ℕ) : NeZero (spacedForm A i t) := ⟨Nat.succ_ne_zero _⟩

/-- The zero residue works simultaneously for every index. -/
theorem spaced_admissible (A l : ℕ) (prime : l.Prime) :
    ∃ t : ℕ, ∀ i < 50, ¬ l ∣ spacedForm A i t :=
  ⟨0,fun i _ => by simpa [spacedForm] using prime.not_dvd_one⟩

theorem spaced_slopes_lt {A i j : ℕ} (ap : 0<A) (ij : i<j) :
    (spacedRoot A i)^2 < (spacedRoot A j)^2 := by
  exact Nat.pow_lt_pow_left
    (Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right (Nat.add_lt_add_left ij 200) ap) 1)
    (by decide)

/-- The common divisor of two roots divides j−i by the determinant identity,
even though their difference as integers is now A*(j−i). -/
theorem spaced_gcd_le_gap {A i j : ℕ} (ij : i<j) :
    (spacedRoot A i).gcd (spacedRoot A j) ≤ j-i := by
  let u := spacedRoot A i
  let v := spacedRoot A j
  have identity : (200+j)*u+i=(200+i)*v+j := by dsimp [u,v,spacedRoot]; ring
  have dvd := Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_left u v) (200+j))
    (dvd_mul_of_dvd_right (Nat.gcd_dvd_right u v) (200+i))
  rw [show (200+j)*u-(200+i)*v=j-i by omega] at dvd
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt ij) dvd

/-- Every pair lies strictly within a factor of two and the relative gap
(q−p)/p is at least 1/300. -/
theorem spaced_balanced {A i j t : ℕ} (ap : 0<A) (ij : i<j) (stop : j<50) (tp : 0<t) :
    let p := spacedForm A i t
    let q := spacedForm A j t
    7≤p ∧ p<q ∧ q<2*p ∧ p≤300*(q-p) := by
  let u := spacedRoot A i
  let v := spacedRoot A j
  have low : 200≤u := by
    have h := Nat.mul_le_mul_left (200+i) ap
    dsimp [u,spacedRoot]
    omega
  have ratio : 3*v≤4*u := by
    have h := Nat.mul_le_mul_right A (show 3*(200+j)≤4*(200+i) by omega)
    dsimp [u,v,spacedRoot]
    nlinarith only [h]
  have width : u+A≤v := by
    have h := Nat.mul_le_mul_right A (show (200+i)+1≤200+j by omega)
    dsimp [u,v,spacedRoot]
    nlinarith only [h]
  have high : u≤250*A := by
    have h := Nat.mul_le_mul_right A (show 200+i≤249 by omega)
    dsimp [u,spacedRoot]
    omega
  have upper : v^2≤2*u^2 := by nlinarith only [Nat.pow_le_pow_left ratio 2]
  have lower : 301*u^2+1≤300*v^2 := by
    nlinarith only [Nat.pow_le_pow_left width 2,Nat.mul_le_mul_left u high,
      pow_pos ap 2,Nat.zero_le (u*A)]
  have pbig : 6≤u^2*t :=
    ((by decide : 6≤200^2).trans (Nat.pow_le_pow_left low 2)).trans
      (by simpa using Nat.mul_le_mul_left (u^2) tp)
  have less : u^2*t<v^2*t := Nat.mul_lt_mul_of_pos_right (spaced_slopes_lt ap ij) tp
  have ub := Nat.mul_le_mul_right t upper
  have lb := Nat.mul_le_mul_right t lower
  rw [Nat.mul_assoc] at ub
  rw [Nat.add_mul,Nat.mul_assoc,Nat.mul_assoc,one_mul] at lb
  change 7≤u^2*t+1 ∧ u^2*t+1<v^2*t+1 ∧ v^2*t+1<2*(u^2*t+1) ∧
    u^2*t+1≤300*(v^2*t+1-(u^2*t+1))
  omega

theorem spaced_period_lower {A i j t : ℕ} (ij : i<j) (stop : j<50) (tp : 0<t) :
    (200*A/49)^4 ≤ residualProduct (spacedForm A i t) (spacedForm A j t) := by
  have lo (k) : 200*A≤spacedRoot A k := by
    dsimp [spacedRoot]
    have h := Nat.mul_le_mul_right A (show 200≤200+k by omega)
    omega
  exact floor_bound (Nat.succ_pos _) tp ((spaced_gcd_le_gap (A:=A) ij).trans (by omega)) (lo i) (lo j)

/-- Under the fifty-form prime-hitting assertion, the ratio stays separated
from one even when the first shared period exceeds an arbitrary threshold. -/
theorem spaced_unbounded_of_prime_hits
    (hits : ∀ A, 0<A → ∃ i j t, i<j ∧ j<50 ∧ 0<t ∧
      (spacedForm A i t).Prime ∧ (spacedForm A j t).Prime) (B : ℕ) :
    ∃ p q, p.Prime ∧ q.Prime ∧ 7≤p ∧ p<q ∧ q<2*p ∧ p≤300*(q-p) ∧
      predecessorSquareSum (p*q) 1=p+q ∧ B<residualProduct p q := by
  let A := B+1
  have ap : 0<A := Nat.succ_pos _
  obtain ⟨i,j,t,ij,stop,tp,pp,qp⟩ := hits A ap
  obtain ⟨lo,lt,bal,gap⟩ := spaced_balanced ap ij stop tp
  have u : 0<spacedRoot A i := Nat.succ_pos _
  have eq := period_formula (v:=spacedRoot A j) u tp
  let z := (spacedRoot A i)/((spacedRoot A i).gcd (spacedRoot A j)) *
    ((spacedRoot A j)/((spacedRoot A i).gcd (spacedRoot A j)))
  have first := JacobiPeriodSquareClass.first_scale (by omega : 1<spacedForm A i t) lt.le bal.le
    (c:=1) (z:=z) squarefree_one (by simpa only [z,one_mul,spacedForm] using eq)
  have grows : B<200*A/49 := by dsimp [A]; omega
  have power : 200*A/49≤(200*A/49)^4 := by
    simpa using Nat.pow_le_pow_right (by omega : 0<200*A/49) (by decide : 1≤4)
  exact ⟨_,_,pp,qp,lo,lt,bal,gap,first.1.2,
    grows.trans_le (power.trans (spaced_period_lower ij stop tp))⟩

end PrimeFactors.JacobiSquarePeriodFamily
