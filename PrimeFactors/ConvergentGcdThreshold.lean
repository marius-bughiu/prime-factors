import PrimeFactors.UpperConvergentAgreement

/-! Two strict gcd thresholds for the occurrence of E/F among the ordinary
convergents of E/N. The only inputs to the Euclidean walk are E and N. -/
namespace PrimeFactors.ConvergentGcdThreshold

open UpperConvergentDeficit

def Bracket (N E u v : ℕ) (x y : Row) : Prop :=
  (E*x.b=N*x.a+u ∧ N*y.a=E*y.b+v) ∨ (N*x.a=E*x.b+u ∧ E*y.b=N*y.a+v)

theorem advance {N E u v : ℕ} {x y : Row} (h : Bracket N E u v x y) :
    Bracket N E v (u%v) y (step x y (u/v)) := by
  rcases h with ⟨l,r⟩|⟨l,r⟩
  · exact Or.inr ⟨r,next_lower l r⟩
  · exact Or.inl ⟨r,next_upper l r⟩

private theorem cross {N E u v : ℕ} {x y : Row} (h : Bracket N E u v x y) :
    N*y.a-E*y.b≤v := by
  rcases h with ⟨_,h⟩|⟨_,h⟩ <;> omega

theorem mass_step (u v : ℕ) (x y : Row) :
    v*(step x y (u/v)).b+(u%v)*y.b=u*y.b+v*x.b := by
  dsimp [step]
  nlinarith only [congrArg (fun z => z*y.b) (Nat.mod_add_div u v)]

private theorem indexed_bound (N E i u v : ℕ) (x y : Row) (np : 0<N)
    (mass : u*y.b+v*x.b=N) (h : Bracket N E u v x y) :
    let z := indexed i u v x y
    (N*z.a-E*z.b)*z.b<N := by
  induction i generalizing u v x y with
  | zero =>
    by_cases vz : v=0
    · subst v
      have zero := cross h
      simp only [indexed,if_true]
      rw [Nat.eq_zero_of_le_zero zero,Nat.zero_mul]
      exact np
    rw [indexed,if_neg vz]
    let z := step x y (u/v)
    have mass' : v*z.b+(u%v)*y.b=N := (mass_step u v x y).trans mass
    have cr : N*z.a-E*z.b≤u%v := cross (advance h)
    by_cases zb : z.b=0
    · change _*z.b<N
      simpa only [zb,Nat.mul_zero] using np
    have less := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt u (Nat.pos_of_ne_zero vz))
      (Nat.pos_of_ne_zero zb)
    exact (Nat.mul_le_mul_right z.b cr).trans_lt (less.trans_le (by omega))
  | succ i ih =>
    by_cases vz : v=0
    · subst v
      have zero := cross h
      simp only [indexed,if_true]
      rw [Nat.eq_zero_of_le_zero zero,Nat.zero_mul]
      exact np
    rw [indexed,if_neg vz]
    exact ih v (u%v) y (step x y (u/v)) ((mass_step u v x y).trans mass) (advance h)

/-- Every native upper row has cross error strictly less than N/b. A lower
row has zero truncated cross error. This includes every terminal index. -/
theorem ordinary_row {N : ℕ} (np : 0<N) (E i : ℕ) :
    let z := indexed i E N ⟨0,1⟩ ⟨1,0⟩
    (N*z.a-E*z.b)*z.b<N :=
  indexed_bound N E i E N _ _ np (by simp) (Or.inl (by simp))

private theorem den {E F : ℕ} (fp : 0<F) :
    ((E:ℚ)/F).den=F/E.gcd F := by
  rw [show (E:ℚ)/F=Rat.divInt E F by simp [Rat.divInt_eq_div],Rat.den_mk]
  simp [fp.ne',Int.gcd]

private theorem clear_threshold {N E F c b g : ℕ} (fp : 0<F) (gp : 0<g) (fb : b*g=F) :
    c*E*F*(N-F)<N*g^2 ↔ E*(N-F)*(c*b^2)<N*F := calc
  _ ↔ (c*E*F*(N-F))*F < (N*g^2)*F := (Nat.mul_lt_mul_right fp).symm
  _ ↔ (E*(N-F)*(c*b^2))*g^2 < (N*F)*g^2 := by rw [←fb]; ring_nf
  _ ↔ _ := Nat.mul_lt_mul_right (Nat.pow_pos gp)

/-- The exact comparison, before applying either continued-fraction theorem.
It holds for every positive constant c, with c=1 and c=2 giving the two bounds. -/
theorem threshold_iff {N E F c : ℕ} (fp : 0<F) (fn : F≤N) (cp : 0<c) :
    c*E*F*(N-F)<N*(E.gcd F)^2 ↔
      |(E:ℝ)/N-(((E:ℚ)/F:ℚ):ℝ)| < 1/((c:ℝ)*((((E:ℚ)/F).den:ℕ):ℝ)^2) := by
  let g := E.gcd F
  let b := F/g
  have gp : 0<g := Nat.gcd_pos_of_pos_right E fp
  have fb : b*g=F := Nat.div_mul_cancel (Nat.gcd_dvd_right E F)
  have bp : 0<b := Nat.pos_of_ne_zero (fun h => by
    have pos : 0<b*g := by rwa [fb]
    rw [h,zero_mul] at pos
    exact lt_irrefl _ pos)
  have nr : 0<(N:ℝ) := by exact_mod_cast fp.trans_le fn
  have fr : 0<(F:ℝ) := by exact_mod_cast fp
  have d : |(E:ℝ)/N-(((E:ℚ)/F:ℚ):ℝ)| = ((E:ℝ)*(N-F:ℕ))/(N*F) := by
    simp only [Rat.cast_div,Rat.cast_natCast,Nat.cast_sub fn]
    rw [abs_sub_comm,abs_of_nonneg]
    · field_simp
      ring
    · apply sub_nonneg.mpr
      exact div_le_div_of_nonneg_left (by positivity) fr (by exact_mod_cast fn)
  rw [d,den fp]
  change c*E*F*(N-F)<N*g^2 ↔ _ < 1/((c:ℝ)*(b:ℝ)^2)
  rw [div_lt_div_iff₀ (mul_pos nr fr) (by positivity)]
  have equiv := clear_threshold (N:=N) (E:=E) (c:=c) fp gp fb
  simpa only [one_mul] using (by exact_mod_cast equiv :
    c*E*F*(N-F)<N*g^2 ↔ (E:ℝ)*(N-F:ℕ)*((c:ℝ)*(b:ℝ)^2)<(N:ℝ)*F)

/-- Sufficient side. Legendre's theorem applied at the actual value of E/N
gives an ordinary convergent whenever the stronger gcd threshold holds. -/
theorem sufficient {N E F : ℕ} (fp : 0<F) (fn : F≤N)
    (large : 2*E*F*(N-F)<N*(E.gcd F)^2) :
    ∃ i, (E:ℚ)/F=((E:ℝ)/N).convergent i := by
  apply Real.exists_rat_eq_convergent
  simpa only [Nat.cast_ofNat] using (threshold_iff fp fn (by decide : 0<2)).mp large

/-- Necessary side. The Euclidean error bound applies even when a fraction
representing the convergent has not been reduced in advance. -/
theorem necessary {N E F : ℕ} (ep : 0<E) (fp : 0<F) (fn : F≤N)
    (present : ∃ i, (E:ℚ)/F=((E:ℝ)/N).convergent i) :
    E*F*(N-F)<N*(E.gcd F)^2 := by
  obtain ⟨i,hi⟩ := present
  have np := fp.trans_le fn
  let z := indexed i E N ⟨0,1⟩ ⟨1,0⟩
  have frac : (z.a:ℚ)/z.b=(E:ℚ)/F := (agreement E N i np).trans hi.symm
  have pos : (0:ℚ)<(E:ℚ)/F := div_pos (by exact_mod_cast ep) (by exact_mod_cast fp)
  have bp : 0<z.b := Nat.pos_of_ne_zero (fun h => by
    rw [←frac,h,Nat.cast_zero,div_zero] at pos
    exact lt_irrefl _ pos)
  have eq : E*z.b=z.a*F := by
    exact_mod_cast ((div_eq_div_iff (by positivity : (z.b:ℚ)≠0)
      (by positivity : (F:ℚ)≠0)).mp frac).symm
  have div_le : F/E.gcd F≤z.b := calc
    _ = ((E:ℚ)/F).den := (den fp).symm
    _ = ((z.a:ℚ)/z.b).den := congrArg Rat.den frac.symm
    _ = z.b/z.a.gcd z.b := den bp
    _ ≤ _ := Nat.div_le_self _ _
  have error : (N*z.a-E*z.b)*z.b<N := ordinary_row np E i
  rw [eq,Nat.mul_comm z.a F,←Nat.sub_mul] at error
  have narrowed : E*(N-F)*(1*(F/E.gcd F)^2)<N*F := calc
    _ ≤ E*(N-F)*z.b^2 := by
      rw [one_mul]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left div_le 2)
    _ = ((N-F)*z.a*z.b)*F := by
      nlinarith only [congrArg (fun t => t*((N-F)*z.b)) eq]
    _ < _ := Nat.mul_lt_mul_of_pos_right error fp
  have h := (clear_threshold (c:=1) fp (Nat.gcd_pos_of_pos_right E fp)
    (Nat.div_mul_cancel (Nat.gcd_dvd_right E F))).mpr narrowed
  simpa only [one_mul] using h

/-- On the same product 143 = 11·13 the transition band contains both an
absent ratio (E=20) and a present one (E=24). The five explicit ordinary
rows for E=20 exhaust its Euclidean walk, including the repeated exact tail. -/
theorem transition_examples :
    (∀ E ∈ ({20,24} : Finset ℕ),
      E*120*(143-120)<143*(E.gcd 120)^2 ∧ 143*(E.gcd 120)^2≤2*E*120*(143-120)) ∧
    (¬ ∃ i, (20:ℚ)/120=((20:ℝ)/143).convergent i) ∧
    (∃ i, (24:ℚ)/120=((24:ℝ)/143).convergent i) := by
  refine ⟨?_,?_,?_⟩
  · intro E h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl <;> decide
  · rintro ⟨i,hi⟩
    have h := hi.trans (agreement 20 143 i (by decide)).symm
    iterate 5
      rcases i with _|i
      · norm_num [indexed,step] at h
    cases i <;> norm_num [indexed,step] at h
  · refine ⟨1,?_⟩
    apply Eq.trans _ (agreement 24 143 1 (by decide))
    norm_num [indexed,step]

end PrimeFactors.ConvergentGcdThreshold
