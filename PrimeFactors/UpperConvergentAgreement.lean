import PrimeFactors.UpperConvergentDeficit

namespace PrimeFactors.UpperConvergentDeficit

/-- Indexed Euclidean row, repeating the final row once division ends,
as in mathlib's rational convergents. -/
def indexed : ℕ → ℕ → ℕ → Row → Row → Row
  | 0,u,v,x,y => if v=0 then y else step x y (u/v)
  | i+1,u,v,x,y => if v=0 then y else indexed i v (u%v) y (step x y (u/v))

private theorem indexed_last (i u : ℕ) (x y : Row) : indexed i u 0 x y=y := by
  cases i <;> simp [indexed]

private theorem digit {u v : ℕ} (vp : 0<v) :
    ⌊(u:ℝ)/v⌋=↑(u/v) ∧ (Int.fract ((u:ℝ)/v))⁻¹=(v:ℝ)/(u%v:ℕ) := by
  have rpos : 0<(v:ℝ) := by exact_mod_cast vp
  have divmod : (u:ℝ)=(u/v:ℕ)*(v:ℝ)+(u%v:ℕ) := by
    exact_mod_cast (by simpa [Nat.add_comm,Nat.mul_comm] using (Nat.mod_add_div u v).symm :
      u=u/v*v+u%v)
  have decomp : (u:ℝ)/v=(u/v:ℕ)+(u%v:ℕ)/(v:ℝ) := by
    field_simp
    linarith only [divmod]
  have lo : (0:ℝ)≤(u%v:ℕ)/(v:ℝ) := by positivity
  have hi : ((u%v:ℕ):ℝ)/(v:ℝ)<1 := (div_lt_one rpos).mpr (by exact_mod_cast Nat.mod_lt u vp)
  have q : ⌊(u:ℝ)/v⌋=↑(u/v) := by
    apply Int.floor_eq_iff.mpr
    simp only [Int.cast_natCast]
    constructor <;> linarith only [decomp,lo,hi]
  refine ⟨q,?_⟩
  rw [Int.fract,q,decomp]
  simp only [Int.cast_natCast,add_sub_cancel_left,inv_div]

private def evalRow (z : Row) : ℚ := (z.a:ℚ)/z.b

private def transform (x y : Row) (r : ℚ) : ℚ :=
  (x.a+r*y.a)/(x.b+r*y.b)

private theorem eval_step (x y : Row) (d : ℕ) : evalRow (step x y d)=transform x y d := by
  simp [evalRow,step,transform]

private theorem transform_digit (x y : Row) (d : ℕ) {t : ℚ} (nz : t≠0) :
    transform x y ((d:ℚ)+t⁻¹)=transform y (step x y d) t := by
  dsimp [transform,step]
  push_cast
  calc
    _ = ((y.a+t*(x.a+d*(y.a:ℚ)))/t)/((y.b+t*(x.b+d*(y.b:ℚ)))/t) := by
      congr 1 <;> field_simp <;> ring
    _ = _ := div_div_div_cancel_right₀ nz _ _

private theorem indexed_value (i u v : ℕ) (vp : 0<v) (x y : Row) :
    evalRow (indexed i u v x y)=transform x y (((u:ℝ)/v).convergent i) := by
  induction i generalizing u v x y with
  | zero =>
    simp only [indexed,if_neg vp.ne',Real.convergent_zero,(digit vp).1,Int.cast_natCast,eval_step]
  | succ i ih =>
    rw [indexed,if_neg vp.ne',Real.convergent_succ,(digit vp).1,(digit vp).2,Int.cast_natCast]
    by_cases zero : u%v=0
    · rw [zero,indexed_last]
      simp [eval_step]
    have rp := Nat.pos_of_ne_zero zero
    have one : 0<v/(u%v) := Nat.div_pos (Nat.mod_lt u vp).le rp
    have qr := PowerRatioRemainder.above_floor ((v:ℝ)/(u%v:ℕ)) i
    rw [(digit (u:=v) rp).1,Int.cast_natCast] at qr
    have pos : 0<((v:ℝ)/(u%v:ℕ)).convergent i := (by exact_mod_cast one : (0:ℚ)<(v/(u%v):ℕ)).trans_le qr
    rw [ih _ _ rp,transform_digit _ _ _ pos.ne']

/-- Exact agreement between the natural forward Euclidean enumerator
and mathlib, including every index past rational termination. -/
theorem agreement (E N i : ℕ) (np : 0<N) :
    let z := indexed i E N ⟨0,1⟩ ⟨1,0⟩
    (z.a:ℚ)/z.b=((E:ℝ)/N).convergent i := by
  simpa [evalRow,transform] using indexed_value i E N np ⟨0,1⟩ ⟨1,0⟩

private def Bracket (N E u v : ℕ) (x y : Row) : Prop :=
  (E*x.b=N*x.a+u ∧ N*y.a=E*y.b+v) ∨ (N*x.a=E*x.b+u ∧ E*y.b=N*y.a+v)

private theorem advance {N E u v : ℕ} {x y : Row} (b : Bracket N E u v x y) :
    Bracket N E v (u%v) y (step x y (u/v)) := by
  rcases b with ⟨l,h⟩|⟨h,l⟩
  · exact Or.inr ⟨h,next_lower l h⟩
  · exact Or.inl ⟨l,next_upper h l⟩

private theorem ended {N E L u : ℕ} {x y : Row} (lp : 0<L) (b : Bracket N E u 0 x y) :
    score N E L y=0 := by
  apply lower_score (u:=0) lp
  rcases b with ⟨_,h⟩|⟨_,h⟩ <;> omega

private theorem counted (N E : ℕ) {L : ℕ} (lp : 0<L) (i u v : ℕ) (x y : Row)
    (b : Bracket N E u v x y) :
    score N E L (indexed i u v x y) ≤ visits N E L (i+1) u v x y := by
  induction i generalizing u v x y with
  | zero =>
    by_cases h : v=0
    · subst v
      rw [indexed_last,last,ended lp b]
    · simp [indexed,visits,h]
  | succ i ih =>
    by_cases h : v=0
    · subst v
      rw [indexed_last,last,ended lp b]
    · rw [indexed,if_neg h,visits,if_neg h]
      exact (ih _ _ _ _ (advance b)).trans (Nat.le_add_left ..)

/-- As every positive Euclidean denominator decreases, fuel N covers all
rows of E/N. A longer requested prefix cannot uncover another candidate. -/
theorem sufficient (N E L v u : ℕ) (x y : Row) (i k : ℕ) (cap : v≤k) :
    visits N E L i u v x y ≤ visits N E L k u v x y := by
  induction v using Nat.strong_induction_on generalizing u x y i k with
  | h v ih =>
    by_cases vz : v=0
    · subst v
      simp only [last,le_refl]
    have vp := Nat.pos_of_ne_zero vz
    cases i with
    | zero => exact Nat.zero_le _
    | succ i =>
      cases k with
      | zero => omega
      | succ k =>
        rw [visits,if_neg vz,visits,if_neg vz]
        have down := Nat.mod_lt u vp
        exact Nat.add_le_add_left (ih (u%v) down _ _ _ i k (by omega)) _

/-- Match the existing mathlib convergent promise to the executable
one-row bound. Exactly one row in the entire terminated Euclidean walk
requires a further test when the genuine positive ratio is present. -/
theorem unique_pass {N E F L : ℕ} (np : 0<N) (ep : 0<E) (fp : 0<F) (lp : 0<L)
    (band : L≤N-F ∧ N-F<2*L)
    (present : ∃ i, (E:ℚ)/F=((E:ℝ)/N).convergent i) :
    visits N E L N E N ⟨0,1⟩ ⟨1,0⟩=1 := by
  obtain ⟨i,hi⟩ := present
  let z := indexed i E N ⟨0,1⟩ ⟨1,0⟩
  have frac : (z.a:ℚ)/z.b=(E:ℚ)/F := (agreement E N i np).trans hi.symm
  have pos : (0:ℚ)<(E:ℚ)/F := div_pos (by exact_mod_cast ep) (by exact_mod_cast fp)
  have ap : 0<z.a := Nat.pos_of_ne_zero (fun h => by rw [←frac, h, Nat.cast_zero, zero_div] at pos; exact lt_irrefl _ pos)
  have bp : 0<z.b := Nat.pos_of_ne_zero (fun h => by rw [←frac, h, Nat.cast_zero, div_zero] at pos; exact lt_irrefl _ pos)
  have eq : E*z.b=z.a*F := by
    exact_mod_cast ((div_eq_div_iff (by positivity : (z.b:ℚ)≠0) (by positivity : (F:ℚ)≠0)).mp frac).symm
  have bracket : Bracket N E E N ⟨0,1⟩ ⟨1,0⟩ := Or.inl (by simp)
  have hit := counted N E lp i E N ⟨0,1⟩ ⟨1,0⟩ bracket
  change score N E L z ≤ _ at hit
  rw [correct_row ap eq band] at hit
  exact Nat.le_antisymm (at_most_one N E lp N)
    (hit.trans (sufficient N E L N E _ _ _ N le_rfl))

end PrimeFactors.UpperConvergentDeficit
