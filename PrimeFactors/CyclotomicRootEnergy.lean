import PrimeFactors.InverseCyclotomicMeasurements
import PrimeFactors.FejerProjection

/-! Mean squared norm of the public polynomial on all mth roots of unity. -/
namespace PrimeFactors.CyclotomicRootEnergy

open Polynomial Finset
open scoped ComplexConjugate
open InverseCyclotomicMeasurements

noncomputable def energy (N m : ℕ) [NeZero m] : ℝ :=
  (∑ x : ZMod m, Complex.normSq ((polynomial N).eval₂ (Int.castRingHom ℂ)
    (ZMod.stdAddChar x))) / m

/-- Complex mean of the polynomial values themselves on the same grid. -/
noncomputable def mean (N m : ℕ) [NeZero m] : ℂ :=
  (∑ x : ZMod m, (polynomial N).eval₂ (Int.castRingHom ℂ) (ZMod.stdAddChar x)) / m

private noncomputable def wave {m : ℕ} [NeZero m] (x a : ZMod m) : ℂ :=
  ZMod.stdAddChar (x*a)

private noncomputable def paired {m : ℕ} [NeZero m] (x a : ZMod m) : ℂ :=
  wave x a+wave x (-a)

private noncomputable def flag {m : ℕ} [NeZero m] (a : ZMod m) : ℝ :=
  if a=0 then 1 else 0

private theorem wave_add {m : ℕ} [NeZero m] (x a b : ZMod m) :
    wave x (a+b) = wave x a*wave x b := by simp [wave,mul_add,AddChar.map_add_eq_mul]

private theorem norm_one {m : ℕ} [NeZero m] (x a : ZMod m) :
    (Complex.normSq (1-wave x a) : ℂ)=2-paired x a := by
  have conjWave : conj (wave x a)=wave x (-a) := by
    rw [wave,wave,ZMod.stdAddChar_apply,←Circle.coe_inv_eq_conj,ZMod.stdAddChar_apply,
      mul_neg,AddChar.map_neg_eq_inv]
  have unit : wave x a*wave x (-a)=1 := by
    rw [←wave_add,add_neg_cancel]
    simp [wave,AddChar.map_zero_eq_one]
  rw [←Complex.mul_conj,map_sub,map_one,conjWave,paired]
  linear_combination unit

private theorem paired_mul {m : ℕ} [NeZero m] (x a b : ZMod m) :
    paired x a*paired x b=paired x (a+b)+paired x (a-b) := by
  simp only [paired,sub_eq_add_neg,neg_add,neg_neg,wave_add]
  ring

private theorem square_expansion {m : ℕ} [NeZero m] (x a b : ZMod m) :
    (Complex.normSq ((1-wave x a)*(1-wave x b)) : ℂ) =
       4-2*paired x a-2*paired x b+paired x (a+b)+paired x (a-b) := by
  rw [Complex.normSq_mul,Complex.ofReal_mul,norm_one,norm_one]
  linear_combination paired_mul x a b

private theorem paired_sum {m : ℕ} [NeZero m] (a : ZMod m) :
    ∑ x : ZMod m, paired x a=(m:ℂ)*(2*(flag a:ℂ)) := by
  simp only [paired,wave,sum_add_distrib,AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar m),
    ZMod.card,neg_eq_zero]
  by_cases ha : a=0
  · simp [ha,flag]
    ring
  · simp [ha,flag]

private theorem evaluated {p q m : ℕ} [NeZero m] (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (x : ZMod m) : (polynomial (p*q)).eval₂ (Int.castRingHom ℂ) (ZMod.stdAddChar x) =
       (1-wave x p)*(1-wave x q) := by
  rw [sparse hp hq ord]
  simp only [eval₂_mul,eval₂_sub,eval₂_one,eval₂_pow,eval₂_X,wave]
  simp only [←AddChar.map_nsmul_eq_pow,nsmul_eq_mul,mul_comm x]

private theorem normalized {p q m : ℕ} [NeZero m] (hp : p.Prime) (hq : q.Prime) (ord : p<q) :
    energy (p*q) m=4-4*flag (p:ZMod m)-4*flag (q:ZMod m) +
      2*flag ((p:ZMod m)+(q:ZMod m))+2*flag ((p:ZMod m)-(q:ZMod m)) := by
  unfold energy
  apply (div_eq_iff (by exact_mod_cast NeZero.ne m : (m:ℝ)≠0)).mpr
  apply Complex.ofReal_injective
  push_cast
  simp_rw [evaluated hp hq ord,square_expansion]
  simp only [sum_add_distrib,sum_sub_distrib,←mul_sum,paired_sum,sum_const,card_univ,
    ZMod.card,nsmul_eq_mul]
  ring

/-- The normalization includes all m sampling points, including those
of smaller order. The statement also holds at m=1 and at factor moduli. -/
theorem alias_formula {p q m : ℕ} [NeZero m] (hp : p.Prime) (hq : q.Prime) (ord : p<q) :
    energy (p*q) m=4 - 4*(if m∣p then 1 else 0) - 4*(if m∣q then 1 else 0) +
      2*(if m∣p+q then 1 else 0) + 2*(if m∣q-p then 1 else 0) := by
  rw [normalized hp hq ord]
  have gap : (p:ZMod m)-(q:ZMod m)=0 ↔ m∣q-p := by
    rw [sub_eq_zero,ZMod.natCast_eq_natCast_iff,Nat.modEq_iff_dvd' ord.le]
  simp only [flag,←Nat.cast_add,gap,ZMod.natCast_zmod_eq_zero_iff_dvd]

/-- Keeping the complex phases removes the gap contribution. -/
theorem mean_formula {p q m : ℕ} [NeZero m] (hp : p.Prime) (hq : q.Prime) (ord : p<q) :
    mean (p*q) m = 1-(if m∣p then 1 else 0)-(if m∣q then 1 else 0)+
      (if m∣p+q then 1 else 0) := by
  have orth (a : ℕ) : ∑ x : ZMod m, wave x a =
      (m:ℂ)*(if m∣a then 1 else 0) := by
    simp only [wave,AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar m),ZMod.card,
      ZMod.natCast_zmod_eq_zero_iff_dvd]
    split_ifs <;> simp
  have expansion (x : ZMod m) : (1-wave x p)*(1-wave x q) =
      1-wave x p-wave x q+wave x ((p+q:ℕ):ZMod m) := by
    rw [Nat.cast_add,wave_add]
    ring
  unfold mean
  apply (div_eq_iff (by exact_mod_cast NeZero.ne m : (m:ℂ)≠0)).mpr
  simp_rw [evaluated hp hq ord,expansion]
  simp only [sum_add_distrib,sum_sub_distrib,orth,sum_const,card_univ,ZMod.card,nsmul_eq_mul]
  ring

private theorem not_dvd_of_coprime {m a : ℕ} (large : 1<m) (cop : m.Coprime a) : ¬m∣a := by
  intro divides
  have h := cop.gcd_eq_one
  rw [Nat.gcd_eq_left divides] at h
  omega

/-- At a coprime modulus greater than one, subtracting the constant term
leaves exactly the indicator of divisibility of the factor sum. -/
theorem mean_sum_flag {p q m : ℕ} [NeZero m] (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (large : 1<m) (cop : m.Coprime (p*q)) :
    mean (p*q) m-1 = if m∣p+q then 1 else 0 := by
  obtain ⟨cp,cq⟩ := Nat.coprime_mul_iff_right.mp cop
  rw [mean_formula hp hq ord,if_neg (not_dvd_of_coprime large cp),
    if_neg (not_dvd_of_coprime large cq)]
  ring

/-- The three nonzero square remainders modulo seven. -/
def squareSeven (N : ℕ) : Prop := N%7=1 ∨ N%7=2 ∨ N%7=4

noncomputable instance (N : ℕ) : Decidable (squareSeven N) := by unfold squareSeven; infer_instance

theorem squareSeven_iff (N : ℕ) : squareSeven N ↔ (N:ZMod 7)≠0 ∧ IsSquare (N:ZMod 7) := by
  have table : ∀ x : ZMod 7, (x.val=1 ∨ x.val=2 ∨ x.val=4) ↔
      x≠0 ∧ ∃ r : ZMod 7, x=r^2 := by decide +kernel
  simpa only [squareSeven,ZMod.val_natCast,isSquare_iff_exists_sq] using table (N:ZMod 7)

private theorem seven_table : ∀ a b : ZMod 7, a≠0 → b≠0 →
    (((a*b).val=1 ∨ (a*b).val=2 ∨ (a*b).val=4) → a+b≠0) ∧
    (¬((a*b).val=1 ∨ (a*b).val=2 ∨ (a*b).val=4) → a≠b) := by decide +kernel

/-- At seven the public square class identifies the only possible collision:
equal factor residues for a square product, opposite residues otherwise. -/
theorem seven_decision {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (cop : Nat.Coprime 7 (p*q)) :
    energy (p*q) 7 = if squareSeven (p*q) then (if 7∣q-p then 6 else 4)
      else (if 7∣p+q then 6 else 4) := by
  obtain ⟨cp,cq⟩ := Nat.coprime_mul_iff_right.mp cop
  have np := not_dvd_of_coprime (by decide : 1<7) cp
  have nq := not_dvd_of_coprime (by decide : 1<7) cq
  have table := seven_table (p:ZMod 7) (q:ZMod 7)
    (fun h => np ((ZMod.natCast_zmod_eq_zero_iff_dvd p 7).mp h))
    (fun h => nq ((ZMod.natCast_zmod_eq_zero_iff_dvd q 7).mp h))
  rw [←Nat.cast_mul, ZMod.val_natCast] at table
  change (squareSeven (p*q) → (p:ZMod 7)+(q:ZMod 7)≠0) ∧
    (¬squareSeven (p*q) → (p:ZMod 7)≠(q:ZMod 7)) at table
  rw [alias_formula hp hq ord, if_neg np, if_neg nq]
  by_cases square : squareSeven (p*q)
  · have miss : ¬7∣p+q := by
      intro hit
      exact table.1 square (by simpa only [Nat.cast_add] using
        (ZMod.natCast_zmod_eq_zero_iff_dvd (p+q) 7).mpr hit)
    simp only [if_pos square,if_neg miss]
    split_ifs <;> norm_num
  · have miss : ¬7∣q-p := fun hit => table.2 square <|
      (ZMod.natCast_eq_natCast_iff p q 7).mpr ((Nat.modEq_iff_dvd' ord.le).mpr hit)
    simp only [if_neg square,if_neg miss]
    split_ifs <;> norm_num

theorem control_seven :
    14351%7=1 ∧ 11663%7=1 ∧ energy 14351 7=6 ∧ energy 11663 7=4 := by
  have a := alias_formula (m:=7) (p:=113) (q:=127) (by norm_num) (by norm_num) (by decide)
  have b := alias_formula (m:=7) (p:=107) (q:=109) (by norm_num) (by norm_num) (by decide)
  norm_num at a b
  exact ⟨by decide,by decide,a,b⟩

/-- Two 14-bit products in the same nonsquare class. The first pair has
a sum divisible by seven and the second pair has neither collision. -/
theorem control_seven_sum :
    9523%7=3 ∧ 11413%7=3 ∧ energy 9523 7=6 ∧ energy 11413 7=4 ∧
    mean 9523 7=2 ∧ mean 11413 7=1 := by
  have a := alias_formula (m:=7) (p:=89) (q:=107) (by norm_num) (by norm_num) (by decide)
  have b := alias_formula (m:=7) (p:=101) (q:=113) (by norm_num) (by norm_num) (by decide)
  have c := mean_formula (m:=7) (p:=89) (q:=107) (by norm_num) (by norm_num) (by decide)
  have d := mean_formula (m:=7) (p:=101) (q:=113) (by norm_num) (by norm_num) (by decide)
  norm_num at a b c d
  exact ⟨by decide,by decide,a,b,c,d⟩

end PrimeFactors.CyclotomicRootEnergy
