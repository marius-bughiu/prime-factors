import PrimeFactors.JacobiPeriodScales
import Mathlib.Data.Nat.Squarefree

/-! All positive scales at which the balanced predecessor-square search
recovers the true factor sum. -/

namespace PrimeFactors.JacobiPeriodSquareClass

open JacobiPeriodCount

/-- When a squarefree coefficient times a square is written as `t*v²`,
the alternate square root divides the original one. The coefficient changes
by the square of their quotient. -/
theorem square_class {c U t v : ℕ} (free : Squarefree c) (vp : 0 < v)
    (same : c*U^2 = t*v^2) : ∃ w, U=v*w ∧ t=c*w^2 := by
  let d := U.gcd v
  let a := U/d
  let b := v/d
  have dp : 0 < d := Nat.gcd_pos_of_pos_right U vp
  have da : d*a=U := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have db : d*b=v := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have cop : a.Coprime b := Nat.coprime_div_gcd_div_gcd dp
  have eq : c*a^2=t*b^2 := Nat.eq_of_mul_eq_mul_left (pow_pos dp 2) <| calc
    d^2*(c*a^2) = c*(d*a)^2 := by ring
    _ = t*(d*b)^2 := by rw [da,db,same]
    _ = d^2*(t*b^2) := by ring
  have bg : b^2 ∣ c := ((cop.symm.pow_left 2).pow_right 2).dvd_of_dvd_mul_right
    (show b^2 ∣ c*a^2 by rw [eq]; exact dvd_mul_left ..)
  have one : b=1 := Nat.isUnit_iff.mp (free b (by simpa only [←sq] using bg))
  have dv : d=v := by simpa [one] using db
  exact ⟨a,by rw [←dv,da],by simpa [one] using eq.symm⟩

/-- All successful positive scales are the squarefree part of the period times
a divisor-square of the square root of the remaining predecessor product. -/
theorem successful_scales {p q c z t : ℕ} (hp : 1 < p) (le : p ≤ q) (bal : q ≤ 2*p)
    (free : Squarefree c) (period : residualProduct p q=c*z^2) (tp : 0 < t) :
    predecessorSquareSum (p*q) t=p+q ↔
      ∃ w : ℕ, w ∣ (p-1).gcd (q-1)*z ∧ t=c*w^2 := by
  let g := (p-1).gcd (q-1)
  have recP : g*((p-1)/g)=p-1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have recQ : g*((q-1)/g)=q-1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have total : (p-1)*(q-1) = c*(g*z)^2 := calc
    _ = (g*((p-1)/g))*(g*((q-1)/g)) := by rw [recP,recQ]
    _ = g^2*residualProduct p q := by change _ = g^2*(((p-1)/g)*((q-1)/g)); ring
    _ = _ := by rw [period]; ring
  have p1 : 1 ≤ p := hp.le
  have q1 : 1 ≤ q := p1.trans le
  have pg : 0 < p-1 := Nat.sub_pos_of_lt hp
  have qg : 0 < q-1 := Nat.sub_pos_of_lt (hp.trans_le le)
  have h := JacobiPeriodScales.sum_iff_square (P:=p-1) (Q:=q-1)
    pg (Nat.sub_le_sub_right le 1) (by simpa only [Nat.sub_add_cancel p1,Nat.sub_add_cancel q1] using bal) tp
  simp only [Nat.sub_add_cancel p1,Nat.sub_add_cancel q1] at h
  rw [h]
  constructor
  · rintro ⟨v,hv⟩
    have good : t*v^2 ≠ 0 := hv.trans_ne (Nat.mul_pos pg qg).ne'
    have vp : 0 < v := Nat.pos_of_ne_zero (by intro zv; simp [zv] at good)
    obtain ⟨w,hw,et⟩ := square_class free vp (total.symm.trans hv.symm)
    exact ⟨w,⟨v,hw.trans (Nat.mul_comm v w)⟩,et⟩
  · rintro ⟨w,⟨v,hv⟩,et⟩
    change g*z=w*v at hv
    exact ⟨v,by rw [total,hv,et]; ring⟩

/-- The first true sum in an increasing search appears at c, including c=1. -/
theorem first_scale {p q c z : ℕ} (hp : 1 < p) (le : p ≤ q) (bal : q ≤ 2*p)
    (free : Squarefree c) (period : residualProduct p q=c*z^2) :
    IsLeast {t : ℕ | 0 < t ∧ predecessorSquareSum (p*q) t=p+q} c := by
  have cp := Nat.pos_of_ne_zero free.ne_zero
  refine ⟨⟨cp,(successful_scales hp le bal free period cp).mpr ⟨1,one_dvd _,by simp⟩⟩,?_⟩
  rintro t ⟨tp,hit⟩
  obtain ⟨w,_,tw⟩ := (successful_scales hp le bal free period tp).mp hit
  exact Nat.le_of_dvd tp ⟨_,tw⟩

/-- Every balanced eligible prime pair has both minima. The least shift is
the residual product, and the least successful square scale is its squarefree part. -/
theorem two_minima {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 7 ≤ p) (le : p ≤ q) (bal : q ≤ 2*p) :
    let R := residualProduct p q
    ∃ c z : ℕ, Squarefree c ∧ 0 < z ∧ R=c*z^2 ∧
      IsLeast {t : ℕ | 0 < t ∧ predecessorSquareSum (p*q) t=p+q} c ∧
      IsLeast {t : ℕ | 0 < t ∧
        JacobiPeriodProbe.AllOffsets (JacobiMomentPeriod.completeEven (p*q)) ((p*q-1)/2) t} R := by
  dsimp only
  have pg : 0 < p-1 := by omega
  have qg : 0 < q-1 := by omega
  have gpos := Nat.gcd_pos_of_pos_left (q-1) pg
  have positive : 0 < residualProduct p q := Nat.mul_pos
    (Nat.div_pos (Nat.gcd_le_left _ pg) gpos) (Nat.div_pos (Nat.gcd_le_right _ qg) gpos)
  obtain ⟨c,z,_,zp,eq,free⟩ := Nat.sq_mul_squarefree_of_pos positive
  have factor : residualProduct p q=c*z^2 := eq.symm.trans (Nat.mul_comm ..)
  refine ⟨c,z,free,zp,factor,first_scale (by omega) le bal free factor,⟨positive,?_⟩,?_⟩
  · exact (JacobiPeriodProbe.canonical_period cop hp (hp.trans le) _).mpr dvd_rfl
  · rintro t ⟨tp,works⟩
    exact Nat.le_of_dvd tp ((JacobiPeriodProbe.canonical_period cop hp (hp.trans le) t).mp works)

end PrimeFactors.JacobiPeriodSquareClass
