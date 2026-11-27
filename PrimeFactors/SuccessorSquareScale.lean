import PrimeFactors.JacobiPeriodSquareClass

/-! Product-only sum candidates from square classes of (p+1)(q+1), on
strictly ordered balanced factors. -/
namespace PrimeFactors.SuccessorSquareScale

/-- Correct the integer square root of the scaled input to obtain a proposed
square root of the scaled successor product. -/
def root (n t : ℕ) := (n/t).sqrt + if t=1 then 2 else 1

def sum (n t : ℕ) := t*(root n t)^2-(n+1)

private theorem gap_bound {p q : ℕ} (ordered : p<q) (balanced : q<2*p) :
    (p+q+1)^2 ≤ 8*(p*q) := by
  have sides := Nat.mul_le_mul (show p+q+1≤3*p by omega)
    (show 3*(p+q+1)≤8*q by omega)
  nlinarith only [sides]

/-- If the gap between N and t*(a+s)² is small on the scale √(tN),
then a lies below the scaled square root of N. -/
private theorem lower_square {n D t a s : ℕ} (eq : t*(a+s)^2=n+D)
    (bound : D^2≤4*s^2*t*n) : t*a^2≤n := by
  by_contra! big
  have delta : 2*s*t*a<D := by nlinarith only [eq,big,Nat.zero_le (t*s^2)]
  have high := Nat.pow_lt_pow_left delta (by decide : 2≠0)
  have low := Nat.mul_le_mul_left (4*s^2*t) big.le
  nlinarith only [high,low,bound]

/-- For an actual square class the square root is one above the scaled
integer root for t≥2 and two above it for t=1. -/
theorem root_correct {p q t z : ℕ} (hp : 1<p) (ordered : p<q) (balanced : q<2*p)
    (tp : 0<t) (square : t*z^2=(p+1)*(q+1)) : root (p*q) t=z := by
  have budget := gap_bound ordered balanced
  have succEq : t*z^2=p*q+(p+q+1) := by rw [square]; ring
  by_cases one : t=1
  · subst t
    simp only [one_mul] at square succEq
    have zbig : 2≤z := by
      by_contra! tiny
      have small := Nat.pow_le_pow_left (show z≤1 by omega) 2
      nlinarith only [small,square,hp,ordered,Nat.zero_le (p*q)]
    let a := z-2
    have za : z=a+2 := by dsimp [a]; omega
    have lo : a^2≤p*q := by
      have e : 1*(a+2)^2=p*q+(p+q+1) := by simpa [←za] using succEq
      simpa using lower_square e (by nlinarith only [budget,Nat.zero_le (p*q)])
    have strict : 2*z<p+q+2 := by
      apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
      obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le ordered.le
      have dp : 0<d := by omega
      rw [hd] at square ⊢
      nlinarith only [square,pow_pos dp 2]
    have hi : p*q < (a+1)^2 := by
      rw [za] at succEq strict
      nlinarith only [succEq,strict]
    have isqrt := Nat.le_antisymm (Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr hi)) (Nat.le_sqrt'.mpr lo)
    simpa [root,isqrt] using za.symm
  · have zp : 0<z := by by_contra! zero; simp [Nat.eq_zero_of_le_zero zero] at square
    let a := z-1
    have za : z=a+1 := by dsimp [a]; omega
    have e : t*(a+1)^2=p*q+(p+q+1) := za ▸ succEq
    have large := Nat.mul_le_mul_right (p*q) (show 8≤4*t by omega)
    have lo : t*a^2≤p*q := lower_square e (by simpa using budget.trans large)
    have hi : p*q<t*(a+1)^2 := by omega
    have ineq := Nat.le_antisymm
      (Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr ((Nat.div_lt_iff_lt_mul tp).mpr
        (by simpa only [Nat.mul_comm t] using hi))))
      (Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le tp).mpr (by rwa [Nat.mul_comm])))
    simpa [root,one,ineq] using za.symm

/-- A positive scale reconstructs the true sum exactly if its product with
an integer square is the successor product. -/
theorem sum_iff {p q t : ℕ} (hp : 1<p) (ordered : p<q) (balanced : q<2*p) (tp : 0<t) :
    sum (p*q) t=p+q ↔ ∃ z : ℕ, t*z^2=(p+1)*(q+1) := by
  have factor : (p+1)*(q+1)=(p*q+1)+(p+q) := by ring
  constructor
  · intro hit
    unfold sum at hit
    exact ⟨root (p*q) t,by rw [factor]; omega⟩
  · rintro ⟨z,square⟩
    rw [sum,root_correct hp ordered balanced tp square,square,factor,Nat.add_sub_cancel_left]

/-- All successful scales are the squarefree kernel c times a square of
a divisor of U, where the successor product is c*U². -/
theorem successful_scales {p q t c U : ℕ} (hp : 1<p) (ordered : p<q) (balanced : q<2*p)
    (free : Squarefree c) (rep : (p+1)*(q+1)=c*U^2) (tp : 0<t) :
    sum (p*q) t=p+q ↔ ∃ w : ℕ, w ∣ U ∧ t=c*w^2 := by
  rw [sum_iff hp ordered balanced tp]
  constructor
  · rintro ⟨z,square⟩
    have zp : 0<z := by by_contra! zero; simp [Nat.eq_zero_of_le_zero zero] at square
    obtain ⟨w,uw,tw⟩ := JacobiPeriodSquareClass.square_class free zp (rep.symm.trans square.symm)
    exact ⟨w,⟨z,uw.trans (Nat.mul_comm ..)⟩,tw⟩
  · rintro ⟨w,⟨z,rfl⟩,rfl⟩
    exact ⟨z,by rw [rep]; ring⟩

/-- The least positive scale in the successor search is exactly c. -/
theorem first_scale {p q c U : ℕ} (hp : 1<p) (ordered : p<q) (balanced : q<2*p)
    (free : Squarefree c) (rep : (p+1)*(q+1)=c*U^2) :
    IsLeast {t : ℕ | 0<t ∧ sum (p*q) t=p+q} c := by
  have cp := Nat.pos_of_ne_zero free.ne_zero
  refine ⟨⟨cp,(successful_scales hp ordered balanced free rep cp).mpr ⟨1,one_dvd _,by simp⟩⟩,?_⟩
  rintro t ⟨tp,hit⟩
  obtain ⟨w,_,multiple⟩ := (successful_scales hp ordered balanced free rep tp).mp hit
  exact Nat.le_of_dvd tp ⟨_,multiple⟩

/-- Every input in the promised range has a squarefree first scale. -/
theorem exists_first {p q : ℕ} (hp : 1<p) (ordered : p<q) (balanced : q<2*p) :
    ∃ c U : ℕ, Squarefree c ∧ (p+1)*(q+1)=c*U^2 ∧
      IsLeast {t : ℕ | 0<t ∧ sum (p*q) t=p+q} c := by
  obtain ⟨c,U,_,_,eq,free⟩ := Nat.sq_mul_squarefree_of_pos (Nat.mul_pos (Nat.succ_pos p) (Nat.succ_pos q))
  have rep := eq.symm.trans (Nat.mul_comm _ _)
  exact ⟨c,U,free,rep,first_scale hp ordered balanced free rep⟩

/-- At 527=17*31 the successor product is 24², and at 77=7*11 it is 6*4².
These examples exercise both square-root corrections. -/
theorem controls :
    ExactFactorization 527 [17,31] ∧ root 527 1=24 ∧ sum 527 1=48 ∧
    ExactFactorization 77 [7,11] ∧ root 77 6=4 ∧ sum 77 6=18 := by
  refine ⟨by norm_num [ExactFactorization],by decide +kernel,by decide +kernel,
    by norm_num [ExactFactorization],by decide +kernel,by decide +kernel⟩

end PrimeFactors.SuccessorSquareScale
