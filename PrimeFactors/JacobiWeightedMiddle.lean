import PrimeFactors.JacobiMiddleDegree
import PrimeFactors.JacobiTwoMomentPeriod

/-! At an index obtained from the product's square root, the consecutive
central-binomial recurrence holds in just one component of a balanced
semiprime. This gives a weighted character sum with a specified gcd. -/
namespace PrimeFactors.JacobiWeightedMiddle

open JacobiTwoMomentPeriod JacobiMiddleDegree ProjectiveWordMoments

/-- Positive even degrees are indexed by half their degree. -/
def index (n : ℕ) : ℕ := n.sqrt/2

theorem midpoint_bounds {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : 7 ≤ p)
    (gap : p+6 ≤ q) (balanced : q < 2*p) :
    let a := (p-1)/2
    let b := (q-1)/2
    let j := index (p*q)
    a < j ∧ j+1 < b ∧ j-a+1 < a := by
  obtain ⟨a,pa⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨b,qb⟩ := (Fact.out : q.Prime).odd_of_ne_two (by omega)
  have lower : p+1 ≤ (p*q).sqrt := Nat.le_sqrt.mpr (by
    nlinarith only [Nat.mul_le_mul_left p gap,hp])
  obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le gap
  have upperQ : (p*q).sqrt < q-3 := Nat.sqrt_lt.mpr (by
    rw [hv,show p+6+v-3 = p+v+3 by omega]
    nlinarith only [Nat.zero_le (p*v),Nat.zero_le (v^2),Nat.zero_le p,Nat.zero_le v])
  have bound := Nat.mul_lt_mul_of_pos_left balanced (show 0<p by omega)
  have upperP : (p*q).sqrt < 2*p-4 := Nat.sqrt_lt.mpr (by
    apply bound.trans_le
    obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le hp
    rw [hu,show 2*(7+u)-4 = 10+2*u by omega]
    nlinarith only [Nat.zero_le u,Nat.zero_le (u^2)])
  dsimp only [index]
  omega

/-- The difference between the two sides of the ordinary recurrence. -/
noncomputable def discrepancy (n : ℕ) [NeZero n] (j : ℕ) : ZMod n :=
  ((j : ZMod n)+1)*moment n (2*(j+1)) - (4*(j : ZMod n)+2)*moment n (2*j)

/-- The two readings combine into one sum with the same Jacobi signs. -/
theorem discrepancy_eq_sum (n j : ℕ) [NeZero n] :
    discrepancy n j = ∑ x : ZMod n, x^(2*j)*(((j:ZMod n)+1)*x^2-(4*(j:ZMod n)+2))*
      ((jacobiSym ((x.val:ℤ)^2-4) n : ℤ) : ZMod n) := by
  simp only [discrepancy,moment,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [show 2*(j+1) = 2*j+2 by omega,pow_add]
  ring

private noncomputable def localDifference (p : ℕ) [Fact p.Prime] (j : ℕ) : ZMod p :=
  ((j : ZMod p)+1)*halfMoment p (j+1) - (4*(j : ZMod p)+2)*halfMoment p j

private theorem coordinates {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (op : p ≠ 2) (oq : q ≠ 2) (j : ℕ) :
    ZMod.chineseRemainder cop (discrepancy (p*q) j) = (localDifference p j, localDifference q j) := by
  simp only [discrepancy,map_sub,map_mul,map_add,map_one,map_ofNat,map_natCast,components cop op oq]
  rfl

private theorem past_first_period {p j : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (past : (p-1)/2 < j) (interior : j-(p-1)/2+1 < (p-1)/2) :
    localDifference p j ≠ 0 := by
  let a := (p-1)/2
  let i := j-a
  obtain ⟨b,pb⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have pa : p-1=2*a := by dsimp only [a]; omega
  have reduce (u : ℕ) (hu : a<u) : halfMoment p u=halfMoment p (u-a) := by
    unfold halfMoment
    rw [component_subtract_period (p:=p) (k:=2*u) (by omega), show 2*u-(p-1)=2*(u-a) by omega]
  have ij : j = i + a := (Nat.sub_add_cancel (Nat.le_of_lt past)).symm
  have ip : 0 < i := Nat.sub_pos_of_lt past
  have j1 : j+1-a=i+1 := by omega
  have ap : (a : ZMod p) ≠ 0 := by
    rw [ne_eq,ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have recu := interior_recurrence hp ip interior
  have nonzero := interior_difference_ne_zero hp ip interior
  calc
    localDifference p j = (a : ZMod p)*(halfMoment p (i+1)-4*halfMoment p i) := by
      rw [localDifference,reduce (j+1) (by omega),j1,reduce j past]
      change ((j:ZMod p)+1)*_ - (4*(j:ZMod p)+2)*halfMoment p i = _
      rw [show (j:ZMod p)=(i:ZMod p)+(a:ZMod p) by
        simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ZMod p)) ij]
      linear_combination recu
    _ ≠ 0 := mul_ne_zero ap nonzero

/-- For gaps at least six the weighted sum at the public index has gcd q. -/
theorem midpoint_gcd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : 7 ≤ p)
    (gap : p+6 ≤ q) (balanced : q < 2*p) :
    (p*q).gcd (discrepancy (p*q) (index (p*q))).val = q := by
  let j := index (p*q)
  have pp : p.Prime := Fact.out
  have qp : q.Prime := Fact.out
  have cop := (Nat.coprime_primes pp qp).mpr (by omega)
  obtain ⟨low,uq,up⟩ := midpoint_bounds hp gap balanced
  have jp : 0<j := (Nat.zero_le _).trans_lt low
  have first := past_first_period hp low up
  have second : localDifference q j=0 := sub_eq_zero.mpr (interior_recurrence (by omega) jp uq)
  let z := discrepancy (p*q) j
  have coords : ((z.val:ZMod p),(z.val:ZMod q))=(localDifference p j,0) := calc
    _ = ZMod.chineseRemainder cop (z.val : ZMod (p*q)) := by rw [map_natCast]; rfl
    _ = _ := by rw [ZMod.natCast_zmod_val,coordinates cop (by omega) (by omega),second]
  have qd := (ZMod.natCast_zmod_eq_zero_iff_dvd z.val q).mp (congrArg Prod.snd coords)
  have pd : ¬ p ∣ z.val := fun h => first
    ((congrArg Prod.fst coords).symm.trans ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr h))
  exact Nat.gcd_mul_of_coprime_of_dvd (pp.coprime_iff_not_dvd.mpr pd) qd

/-- Gaps two and four have a public square test before evaluating any moments. -/
theorem balanced_alternatives {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : 7 ≤ p)
    (order : p < q) (balanced : q < 2*p) :
    p*q+1=(p+1)^2 ∨ p*q+4=(p+2)^2 ∨
      (p*q).gcd (discrepancy (p*q) (index (p*q))).val = q := by
  obtain ⟨a,pa⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨b,qb⟩ := (Fact.out : q.Prime).odd_of_ne_two (by omega)
  by_cases gap : p+6 ≤ q
  · exact Or.inr (Or.inr (midpoint_gcd hp gap balanced))
  · rcases (show q=p+2 ∨ q=p+4 by omega) with h | h
    · exact Or.inl (by rw [h]; ring)
    · exact Or.inr (Or.inl (by rw [h]; ring))

/-- Factor certificate for the control whose first Fermat midpoint misses. -/
theorem control2627_factors : ExactFactorization 2627 [37,71] := by
  norm_num [ExactFactorization]

end PrimeFactors.JacobiWeightedMiddle
