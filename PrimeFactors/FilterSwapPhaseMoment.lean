import PrimeFactors.FourRowResidueCounts
import PrimeFactors.FiniteFilterWork

/-! Moments of the signed lookup savings from swapping two tests in a moving
window. Averages range over all translations of a finite additive group.
For a positive width w the triangle uses lags 0 through w−1. Evaluating
the toy CRT formula from its local tables requires at most w dots on each
of the periods 3, 11 and 13, or O(w·(3+11+13)) local multiply-adds. The
result measures variation across starting phases. -/

namespace PrimeFactors.FilterSwapPhaseMoment

open Finset

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Unnormalized autocorrelation at a displacement. -/
noncomputable def correlation (f : G → ℤ) (h : G) : ℤ := ∑ x, f x * f (x+h)

/-- Sum of the signed one-position savings over a translated window. -/
noncomputable def windowTotal (f : G → ℤ) (step : G) (w : ℕ) (x : G) : ℤ :=
  ∑ j ∈ range w, f (x+j•step)

private theorem translated (f : G → ℤ) (h : G) : ∑ x, f (x+h) = ∑ x, f x :=
  Equiv.sum_comp (Equiv.addRight h) f

/-- Every position appears equally often as the starting phase is translated. -/
theorem first_moment (f : G → ℤ) (step : G) (w : ℕ) :
    ∑ x, windowTotal f step w x = (w:ℤ) * ∑ x, f x := by
  unfold windowTotal
  rw [sum_comm]
  simp only [translated, sum_const, card_range, nsmul_eq_mul]

omit [Fintype G] in
private theorem head (f : G → ℤ) (step : G) (w : ℕ) (x : G) :
    windowTotal f step (w+1) x = f x + windowTotal f step w (x+step) := by
  rw [windowTotal, sum_range_succ', windowTotal]
  simp only [zero_smul,add_zero,add_smul,one_smul]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro j _
  congr 1
  abel

private theorem cross (f : G → ℤ) (step : G) (w : ℕ) :
    ∑ x, f x * windowTotal f step w (x+step) =
      ∑ j ∈ range w, correlation f ((j+1)•step) := by
  simp only [windowTotal, mul_sum, correlation]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro x _
  rw [add_smul, one_smul]
  congr 2
  abel

/-- The diagonal lag and the two directions of each positive lag. -/
noncomputable def triangle (w : ℕ) (c : ℕ → ℤ) : ℤ :=
  (w:ℤ)*c 0 + 2 * ∑ j ∈ range w, ((w:ℤ)-1-j)*c (j+1)

private theorem triangle_succ (w : ℕ) (c : ℕ → ℤ) :
    triangle (w+1) c = triangle w c + c 0 + 2 * ∑ j ∈ range w, c (j+1) := by
  simp only [triangle, sum_range_succ, Nat.cast_add, Nat.cast_one]
  have eq : ∑ j ∈ range w, ((w:ℤ)+1-1-j)*c (j+1) =
      (∑ j ∈ range w, ((w:ℤ)-1-j)*c (j+1)) + ∑ j ∈ range w, c (j+1) := by
    rw [←sum_add_distrib]
    exact sum_congr rfl (fun _ _ => by ring)
  rw [eq]
  ring

/-- The second moment of a window is determined by at most `w` distinct lags. -/
theorem second_moment (f : G → ℤ) (step : G) (w : ℕ) :
    ∑ x, (windowTotal f step w x)^2 = triangle w (fun h => correlation f (h•step)) := by
  induction w with
  | zero => simp [windowTotal,triangle]
  | succ w ih =>
    have expand (x : G) : (windowTotal f step (w+1) x)^2 =
        (windowTotal f step w (x+step))^2 + (f x)^2 + 2 * (f x * windowTotal f step w (x+step)) := by
      rw [head]; ring
    simp_rw [expand]
    rw [sum_add_distrib,sum_add_distrib,←mul_sum,cross,triangle_succ]
    have shift := translated (fun x => (windowTotal f step w x)^2) step
    simp only at shift
    rw [shift,ih]
    simp [correlation,pow_two]

/-- The centered second moment, scaled by the cube of the number of phases to
avoid division in the variance itself. -/
theorem centered_moment (f : G → ℤ) (step : G) (w : ℕ) :
    let n : ℤ := Fintype.card G
    let m := (w:ℤ) * ∑ x, f x
    ∑ x, (n * windowTotal f step w x - m)^2 =
      n^2 * triangle w (fun h => correlation f (h•step)) - n*m^2 := by
  dsimp only
  let n : ℤ := Fintype.card G
  let m := (w:ℤ) * ∑ x, f x
  have expand (x : G) : (n*windowTotal f step w x-m)^2 =
      n^2*(windowTotal f step w x)^2 - (2*n*m)*windowTotal f step w x+m^2 := by ring
  change ∑ x, (n*windowTotal f step w x-m)^2 = _
  simp_rw [expand]
  rw [sum_add_distrib,sum_sub_distrib,←mul_sum,←mul_sum,first_moment,second_moment]
  simp only [sum_const, card_univ,nsmul_eq_mul]
  dsimp [m,n]
  ring

section Product
variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

omit [AddCommGroup A] [AddCommGroup B] in
private theorem independent_sum (a : A → ℤ) (b : B → ℤ) :
    ∑ z : A × B, a z.1 * b z.2 = (∑ x, a x)*(∑ y, b y) := by
  rw [Fintype.sum_prod_type,sum_mul]
  simp_rw [mul_sum]

/-- On a product of independent cyclic phases, prefix autocorrelations multiply. -/
theorem correlation_mul (a : A → ℤ) (b : B → ℤ) (h : A) (k : B) :
    correlation (fun z : A × B => a z.1*b z.2) (h,k) = correlation a h * correlation b k := by
  unfold correlation
  simp only [Prod.fst_add,Prod.snd_add]
  simp_rw [mul_mul_mul_comm (a _) (b _) (a _) (b _)]
  exact independent_sum (fun x => a x*a (x+h)) (fun y => b y*b (y+k))

/-- For two separate coordinates, the cross terms use only their one-coordinate totals. -/
theorem correlation_difference (a : A → ℤ) (b : B → ℤ) (h : A) (k : B) :
    correlation (fun z : A × B => a z.1-b z.2) (h,k) =
    (Fintype.card B:ℤ)*correlation a h + (Fintype.card A:ℤ)*correlation b k -
      2*(∑ x, a x)*(∑ y, b y) := by
  have expand (x : A × B) : (a x.1 - b x.2) * (a (x.1+h)-b (x.2+k)) =
      (a x.1*a (x.1+h))*1 + 1*(b x.2*b (x.2+k)) -
        (a x.1*b (x.2+k)+a (x.1+h)*b x.2) := by ring
  simp only [correlation,Prod.fst_add,Prod.snd_add,expand,sum_sub_distrib,sum_add_distrib]
  rw [independent_sum (fun x => a x*a (x+h)) (fun _ : B => 1),
    independent_sum (fun _ : A => 1) (fun y => b y*b (y+k)), independent_sum a (fun y => b (y+k)),
    independent_sum (fun x => a (x+h)) b,translated,translated]
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one]
  ring

/-- Transporting a score to CRT coordinates preserves the correlation. -/
theorem correlation_equiv (e : A ≃+ B) (f : B → ℤ) (h : A) :
    correlation (fun x => f (e x)) h = correlation f (e h) := by
  simp only [correlation,map_add]
  exact Equiv.sum_comp e.toEquiv (fun y => f y * f (y+e h))

end Product

open FourRowResidueCounts ThreeTestMarginals FiniteFilterWork

private noncomputable def prefixGate (x : ZMod 3) : ℤ := (row (2+4*x.val)).1.toNat
private noncomputable def gate11 (x : ZMod 11) : ℤ := (row (2+4*x.val)).2.2.toNat
private noncomputable def gate13 (x : ZMod 13) : ℤ := (row (2+4*x.val)).2.1.toNat

private noncomputable def crt : ZMod 429 ≃+* ZMod 3 × (ZMod 11 × ZMod 13) :=
  (ZMod.chineseRemainder (by decide : Nat.Coprime 3 143)).trans
    ((RingEquiv.refl _).prodCongr (ZMod.chineseRemainder (by decide : Nat.Coprime 11 13)))

private noncomputable def localScore (v : ZMod 3 × (ZMod 11 × ZMod 13)) : ℤ :=
  prefixGate v.1 * (gate11 v.2.1 - gate13 v.2.2)

noncomputable def score (z : ZMod 429) : ℤ := localScore (crt z)

/-- Exact factorization of the 429-phase correlation at every lag into dots on
three short periods. Both of the latter two gates have six acceptable residues. -/
theorem local_correlations (h : ℕ) :
    correlation score (h : ZMod 429) = correlation prefixGate (h : ZMod 3) *
      (13*correlation gate11 (h : ZMod 11) + 11*correlation gate13 (h : ZMod 13) - 72) := by
  change correlation (fun z => localScore (crt.toAddEquiv z)) _ = _
  rw [correlation_equiv]
  change correlation localScore (crt (h : ZMod 429)) = _
  rw [map_natCast]
  change correlation (fun v : ZMod 3 × (ZMod 11 × ZMod 13) =>
    prefixGate v.1 * (gate11 v.2.1 - gate13 v.2.2)) ((h : ZMod 3),((h : ZMod 11),(h : ZMod 13))) = _
  rw [correlation_mul prefixGate (fun z : ZMod 11 × ZMod 13 => gate11 z.1-gate13 z.2)
    (h:ZMod 3) ((h:ZMod 11),(h:ZMod 13)), correlation_difference, ZMod.card, ZMod.card]
  have a : ∑ x, gate11 x = 6 := by decide +kernel
  have b : ∑ x, gate13 x = 6 := by decide +kernel
  rw [a,b]
  rfl

/-- Positive values are scalar lookups saved by testing 13 before 11 after test 3. -/
noncomputable def saving (i : ℕ) : ℤ :=
  (work (window i) [(·.1),(·.2.2),(·.2.1)] : ℤ) -
    work (window i) [(·.1),(·.2.1),(·.2.2)]

theorem saving_period (i : ℕ) : saving (i+429) = saving i := by simp [saving, period]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The signed local-gate window is exactly the swap cost on the original arithmetic rows. -/
theorem saving_is_window : ∀ i : Fin 429, saving i.val = windowTotal score 1 4 (i.val : ZMod 429) := by
  decide +kernel

noncomputable def savings : List ℤ := (List.range 429).map saving

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- Histogram, first raw total and second raw total for all 429 starting phases. -/
theorem histogram : savings.length = 429 ∧ savings.count (-1) = 80 ∧ savings.count 0 = 224 ∧
    savings.count 1 = 122 ∧ savings.count 2 = 3 ∧ savings.sum = 48 ∧
    (savings.map (fun s => s^2)).sum = 214 := by
  decide +kernel

/-- Four local dot products suffice for the second moment at width four.
The zero correlations occur because distinct positions cannot both pass the
modulo-three prefix at lags one and two. -/
theorem four_lags :
    [0,1,2,3].map (fun h : ℕ => correlation score (h : ZMod 429)) = [72,0,0,-37] := by
  simp only [List.map_cons,List.map_nil,local_correlations]
  decide +kernel

/-- Recover the census's second raw total from small-period correlations. -/
theorem square_total_from_lags : ∑ z : ZMod 429, (saving z.val)^2 = 214 := by
  have agreement (z : ZMod 429) : saving z.val = windowTotal score 1 4 z := by
    simpa only [ZMod.natCast_zmod_val] using saving_is_window ⟨z.val,z.val_lt⟩
  simp_rw [agreement]
  rw [second_moment]
  have lag := four_lags
  simp only [List.map_cons,List.map_nil,List.cons.injEq,true_and,and_true] at lag
  obtain ⟨h₀,h₁,h₂,h₃⟩ := lag
  norm_num [triangle,Finset.sum_range_succ,nsmul_eq_mul] at h₀ h₁ h₂ h₃ ⊢
  rw [h₀,h₁,h₂,h₃]
  decide


end PrimeFactors.FilterSwapPhaseMoment
