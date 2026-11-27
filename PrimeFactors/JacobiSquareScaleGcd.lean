import PrimeFactors.JacobiPeriodSquareClass

/-! A necessary gcd check on a squarefree candidate for the first successful
scale. It only uses the product and the proposed square root. -/
namespace PrimeFactors.JacobiSquareScaleGcd

/-- If t is squarefree and t*y² is the predecessor product, every prime power
in N−1 supported on t must divide y in full. -/
theorem forced_part {p q t y : ℕ} (hp : 1 < p) (hq : 1 < q)
    (free : Squarefree t) (hit : t*y^2 = (p-1)*(q-1)) :
    t.Coprime ((p*q-1)/((p*q-1).gcd y)) := by
  let g := (p-1).gcd (q-1)
  let a := (p-1)/g
  let b := (q-1)/g
  let k := a+b+g*(a*b)
  have gp : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.sub_pos_of_lt hp)
  have ga : g*a=p-1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have gb : g*b=q-1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have ab : a.Coprime b := Nat.coprime_div_gcd_div_gcd gp
  have primeTo : (a*b).Coprime k := by
    apply (Nat.coprime_add_mul_right_right (a*b) (a+b) g).mpr
    exact ((Nat.coprime_self_add_right).mpr ab).mul ((Nat.coprime_add_self_right).mpr ab.symm)
  have total : p*q-1 = g*k := by
    have eq : p*q = g*k+1 := by
      rw [show p = g*a+1 by omega, show q = g*b+1 by omega]
      dsimp only [k]; ring
    omega
  have same : t*y^2 = (a*b)*g^2 := by rw [hit,←ga,←gb]; ring
  obtain ⟨w,yw,scale⟩ := JacobiPeriodSquareClass.square_class free gp same
  rw [total,yw,Nat.gcd_mul_left,Nat.mul_div_mul_left _ _ gp]
  exact primeTo.of_dvd ⟨w^2,scale⟩ (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left k w))

/-- The decoder's proposed root can be computed before the discriminant test. -/
def proposedRoot (n t : ℕ) : ℕ :=
  if t = 1 then n.sqrt-1 else (n/t).sqrt

/-- A failing gcd rules out this squarefree scale without the discriminant root. -/
theorem first_scale_check {p q t : ℕ} (hp : 1 < p) (hq : 1 < q) (free : Squarefree t)
    (good : predecessorSquareSum (p*q) t = p+q) :
    t.Coprime ((p*q-1)/((p*q-1).gcd (proposedRoot (p*q) t))) := by
  apply forced_part hp hq free
  change p*q+1-t*(proposedRoot (p*q) t)^2 = p+q at good
  have sum : (p-1)*(q-1)+(p+q)=p*q+1 := by
    obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero (show p ≠ 0 by omega)
    obtain ⟨b,hb⟩ := Nat.exists_eq_succ_of_ne_zero (show q ≠ 0 by omega)
    rw [ha,hb]
    simp only [Nat.succ_sub_one,Nat.succ_eq_add_one]; ring
  omega

/-- Every divisor of N−1 supported on the candidate's primes divides the
square root in the predecessor product. An arbitrary witness d ∣ t^k suffices. -/
theorem divides_root {p q t y d k : ℕ} (hp : 1 < p) (hq : 1 < q) (free : Squarefree t)
    (hit : t*y^2 = (p-1)*(q-1)) (dn : d ∣ p*q-1) (dt : d ∣ t^k) : d ∣ y := by
  let n := p*q-1
  let h := n.gcd y
  have hd : h ∣ n := Nat.gcd_dvd_left ..
  have cop : d.Coprime (n/h) := Nat.Coprime.of_dvd_left dt ((forced_part hp hq free hit).pow_left k)
  have whole : d ∣ n/h*h := (Nat.div_mul_cancel hd).symm ▸ dn
  exact (cop.dvd_of_dvd_mul_left whole).trans (Nat.gcd_dvd_right ..)

/-- The whole class of multiples of a selected support can be excluded above
a public cutoff, before taking a scaled square root. -/
theorem before_root {p q t d k : ℕ} (hp : 1 < p) (hq : 1 < q) (free : Squarefree t)
    (good : predecessorSquareSum (p*q) t = p+q) (dn : d ∣ p*q-1) (dt : d ∣ t^k) :
    t*d^2 < p*q := by
  let y := proposedRoot (p*q) t
  have sum : (p-1)*(q-1)+(p+q)=p*q+1 := by
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show p ≠ 0 by omega)
    obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show q ≠ 0 by omega)
    simp only [Nat.succ_sub_one,Nat.succ_eq_add_one]; ring
  change p*q+1-t*y^2 = p+q at good
  have eq : t*y^2 = (p-1)*(q-1) := by omega
  have yp : y ≠ 0 := by
    intro zero
    have positive := Nat.mul_pos (Nat.sub_pos_of_lt hp) (Nat.sub_pos_of_lt hq)
    simp [zero] at eq
    omega
  have le := Nat.le_of_dvd (Nat.pos_of_ne_zero yp) (divides_root hp hq free eq dn dt)
  exact (Nat.mul_le_mul_left t (Nat.pow_le_pow_left le 2)).trans_lt (by omega)

/-- For 3713 the public predecessor is divisible by 128. A successful
squarefree scale cannot be even, at any search budget. -/
theorem control_3713 {t : ℕ} (free : Squarefree t)
    (good : predecessorSquareSum 3713 t=47+79) : ¬ 2 ∣ t := by
  intro even
  have d : 128 ∣ t^7 := by simpa using (pow_dvd_pow_of_dvd even 7)
  have short := before_root (p:=47) (q:=79) (by decide) (by decide) free good (by decide : 128 ∣ 47*79-1) d
  have pos := Nat.pos_of_ne_zero free.ne_zero
  omega

theorem control_3713_factors : ExactFactorization 3713 [47,79] := by
  norm_num [ExactFactorization]

end PrimeFactors.JacobiSquareScaleGcd
