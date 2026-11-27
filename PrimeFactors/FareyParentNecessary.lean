import PrimeFactors.ConvergentGcdThreshold

/-! The lower Farey parent controls the strict, one-sided error of every ordinary upper
convergent. The proof follows the same natural Euclidean rows as the project search. -/
namespace PrimeFactors.FareyParentNecessary

open UpperConvergentDeficit

/-- Signed errors and the unimodular determinant of adjacent Euclidean rows. -/
def Adjacent (N E u v : ℕ) (x y : Row) : Prop :=
  (E*x.b=N*x.a+u ∧ N*y.a=E*y.b+v ∧ y.a*x.b=x.a*y.b+1) ∨
  (N*x.a=E*x.b+u ∧ E*y.b=N*y.a+v ∧ x.a*y.b=y.a*x.b+1)

theorem advance {N E u v : ℕ} {x y : Row} (h : Adjacent N E u v x y) :
    Adjacent N E v (u%v) y (step x y (u/v)) := by
  rcases h with ⟨lo,hi,det⟩ | ⟨hi,lo,det⟩
  · exact Or.inr ⟨hi,next_lower lo hi,by dsimp [step]; nlinarith only [det]⟩
  · exact Or.inl ⟨lo,next_upper hi lo,by dsimp [step]; nlinarith only [det]⟩

private def HasParent (N E : ℕ) (z : Row) : Prop :=
  ∃ c d : ℕ, 0<d ∧ d≤z.b ∧ z.a*d=z.b*c+1 ∧ (N*z.a-E*z.b)*(z.b+d)<N

private theorem walk (N E i u v : ℕ) (x y : Row) (vu : v≤u) (yp : 0<y.b)
    (adj : Adjacent N E u v x y) (mass : u*y.b+v*x.b=N) :
    let z := indexed i u v x y
    E*z.b<N*z.a → HasParent N E z := by
  induction i generalizing u v x y with
  | zero =>
    by_cases vz : v=0
    · subst v
      simp only [indexed,if_true]
      intro h
      rcases adj with ⟨_,hi,_⟩ | ⟨_,lo,_⟩ <;> omega
    rw [indexed,if_neg vz]
    let z := step x y (u/v)
    have vp := Nat.pos_of_ne_zero vz
    have large : y.b≤z.b :=
      (Nat.le_mul_of_pos_left y.b (Nat.div_pos vu vp)).trans (Nat.le_add_left ..)
    have newmass : v*z.b+(u%v)*y.b=N := (ConvergentGcdThreshold.mass_step u v x y).trans mass
    change E*z.b<N*z.a → HasParent N E z
    intro strict
    rcases advance adj with ⟨_,hi,det⟩ | ⟨_,lo,_⟩
    · change N*z.a=E*z.b+u%v at hi
      refine ⟨y.a,y.b,yp,large,by simpa [Nat.mul_comm] using det,?_⟩
      change (N*z.a-E*z.b)*(z.b+y.b)<N
      rw [hi,Nat.add_sub_cancel_left,Nat.mul_add]
      have small := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt u vp) (yp.trans_le large)
      omega
    · change E*z.b=N*z.a+u%v at lo
      omega
  | succ i ih =>
    by_cases vz : v=0
    · subst v
      simp only [indexed,if_true]
      intro h
      rcases adj with ⟨_,hi,_⟩ | ⟨_,lo,_⟩ <;> omega
    rw [indexed,if_neg vz]
    have vp := Nat.pos_of_ne_zero vz
    have large : y.b≤(step x y (u/v)).b :=
      (Nat.le_mul_of_pos_left y.b (Nat.div_pos vu vp)).trans (Nat.le_add_left ..)
    exact ih v (u%v) y (step x y (u/v)) (Nat.mod_lt u vp).le (yp.trans_le large)
      (advance adj) ((ConvergentGcdThreshold.mass_step u v x y).trans mass)

/-- Extract the lower parent from every strict upper ordinary row, including rows with
denominator one. Its previous Euclidean remainder is strictly larger than the current one. -/
theorem upper_parent {N : ℕ} (np : 0<N) (E i : ℕ) :
    let z := indexed i E N ⟨0,1⟩ ⟨1,0⟩
    E*z.b<N*z.a → ∃ c d : ℕ, 0<d ∧ d≤z.b ∧ z.a*d=z.b*c+1 ∧
      (N*z.a-E*z.b)*(z.b+d)<N := by
  let z := step ⟨0,1⟩ ⟨1,0⟩ (E/N)
  have low : E*z.b=N*z.a+E%N := by
    dsimp [z,step]
    simpa [Nat.add_comm] using (Nat.mod_add_div E N).symm
  cases i with
  | zero =>
    rw [indexed,if_neg np.ne']
    change E*z.b<N*z.a → _
    omega
  | succ i =>
    rw [indexed,if_neg np.ne']
    exact walk N E i N (E%N) ⟨1,0⟩ z (Nat.mod_lt E np).le (by simp [z,step])
      (advance (show Adjacent N E E N ⟨0,1⟩ ⟨1,0⟩ from Or.inl (by simp)))
      (by simp [z,step])

theorem parent_mod {a b c d : ℕ} (det : a*d=b*c+1) :
    a*d≡1 [MOD b] := by
  change (a*d)%b=1%b
  simp [det,Nat.add_mod]

/-- Among positive denominators at most b, the determinant determines the lower parent
denominator uniquely. Subtracting one handles the endpoint d=b=1 without an exception. -/
theorem parent_unique {a b c d c' d' : ℕ} (dp : 0<d) (db : d≤b) (dp' : 0<d') (db' : d'≤b)
    (left : a*d=b*c+1) (right : a*d'=b*c'+1) : d=d' := by
  have cop := Nat.coprime_of_mul_modEq_one d (parent_mod left)
  have same := Nat.ModEq.cancel_left_of_coprime cop.symm.gcd_eq_one
    ((parent_mod left).trans (parent_mod right).symm)
  have pred : d-1≡d'-1 [MOD b] := Nat.ModEq.add_right_cancel' 1 (by
    simpa [Nat.sub_add_cancel dp,Nat.sub_add_cancel dp'] using same)
  have := pred.eq_of_lt_of_lt (by omega) (by omega)
  omega

/-- Sharp necessary side of the upper Farey criterion for a positive fraction E/F above
E/N. The supplied determinant ensures that a/b is reduced and that d is its lower
parent's denominator. No coprimality or E≤N hypothesis is required separately. -/
theorem necessary {N E F a b c d : ℕ} (ep : 0<E) (fp : 0<F) (fn : F<N)
    (bp : 0<b) (db : d≤b) (fraction : a*F=E*b) (parent : a*d=b*c+1)
    (present : ∃ i, (E:ℚ)/F=((E:ℝ)/N).convergent i) :
    (a*(N-F))*(b+d)<N := by
  obtain ⟨i,hi⟩ := present
  let z := indexed i E N ⟨0,1⟩ ⟨1,0⟩
  have np := fp.trans fn
  have frac : (z.a:ℚ)/z.b=(E:ℚ)/F := (agreement E N i np).trans hi.symm
  have pos : (0:ℚ)<(E:ℚ)/F := div_pos (by exact_mod_cast ep) (by exact_mod_cast fp)
  have za : 0<z.a := Nat.pos_of_ne_zero (fun h => by
    rw [←frac,h,Nat.cast_zero,zero_div] at pos
    exact lt_irrefl _ pos)
  have zb : 0<z.b := Nat.pos_of_ne_zero (fun h => by
    rw [←frac,h,Nat.cast_zero,div_zero] at pos
    exact lt_irrefl _ pos)
  have eq : E*z.b=z.a*F := by
    exact_mod_cast ((div_eq_div_iff (by positivity : (z.b:ℚ)≠0)
      (by positivity : (F:ℚ)≠0)).mp frac).symm
  have above : E*z.b<N*z.a := by rw [eq,Nat.mul_comm N]; exact Nat.mul_lt_mul_of_pos_left fn za
  obtain ⟨c',d',dp',db',det,bound⟩ := upper_parent np E i above
  change z.a*d'=z.b*c'+1 at det
  change d'≤z.b at db'
  change (N*z.a-E*z.b)*(z.b+d')<N at bound
  have cross : a*z.b=z.a*b := by
    apply Nat.eq_of_mul_eq_mul_right fp
    nlinarith only [congrArg (fun t => t*z.b) fraction,congrArg (fun t => t*b) eq]
  have ab := Nat.coprime_of_mul_modEq_one d (parent_mod parent)
  have zz := Nat.coprime_of_mul_modEq_one d' (parent_mod det)
  have bd : z.b=b := Nat.dvd_antisymm
    (zz.symm.dvd_of_dvd_mul_left (cross ▸ dvd_mul_left _ _))
    (ab.symm.dvd_of_dvd_mul_left (cross.symm ▸ dvd_mul_left _ _))
  have ad : z.a=a := by rw [bd] at cross; exact (Nat.eq_of_mul_eq_mul_right bp cross).symm
  simp only [ad,bd] at det bound db'
  have dp : 0<d := Nat.pos_of_ne_zero (fun h => by rw [h,Nat.mul_zero] at parent; omega)
  have dd := parent_unique dp db dp' db' parent det
  rw [←dd,←fraction,Nat.mul_comm N,←Nat.mul_sub] at bound
  exact bound

end PrimeFactors.FareyParentNecessary
