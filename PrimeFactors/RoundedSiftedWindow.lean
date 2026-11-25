import PrimeFactors.SiftedDivisorWindow
import PrimeFactors.ChebyshevDivisorWindow

/-! Auditable height bounds for integer-valued sifted rows after bringing
each monic polynomial closer to the Chebyshev polynomial on the interval. -/

namespace PrimeFactors.RoundedSiftedWindow

open Polynomial Finset
open SiftedDivisorWindow (raw denominator scale numerator)

abbrev Corrections := Fin 7 → Fin 7 → ℤ

private noncomputable def row (e : Corrections) (U : ℕ) (i : Fin 7) : ℤ[X] :=
  ChebyshevDivisorWindow.basis U i.val + ofFn 7 (e i)

/-- Direct integer evaluation, including the constant row. -/
noncomputable def value (e : Corrections) (U : ℕ) (i : Fin 7) (x : ℤ) : ℤ :=
  (if i.val=0 then 1 else 2*GapPolynomialScale.companion ((U:ℤ)^2) x (i.val+1)
    - x*GapPolynomialScale.companion ((U:ℤ)^2) x i.val) + ∑ j, e i j*x^j.val

private theorem eval_row (e : Corrections) (U : ℕ) (i : Fin 7) (x : ℤ) :
    (row e U i).eval x=value e U i x := by
  rw [row,eval_add,HigherDivisorWindow.eval_coeff]
  unfold value
  congr 1
  cases h : i.val with
  | zero => simp [ChebyshevDivisorWindow.basis]
  | succ j => simp only [ChebyshevDivisorWindow.basis,GapPolynomialScale.dickson_companion,
      Nat.succ_ne_zero,if_false]

private theorem row_degree (e : Corrections) (U : ℕ) (i : Fin 7) : (row e U i).natDegree≤6 := by
  apply natDegree_add_le_of_degree_le
  · exact (ChebyshevDivisorWindow.degree_basis U i.val).1.trans_le (by omega)
  · exact Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide : 0<7) (e i))

/-- Seven evaluation residues per coordinate suffice, including for negative offsets. -/
def gridChecks (e : Corrections) (U : ℕ) (s : ℤ) : Prop :=
  ∀ i j : Fin 7, (denominator i:ℤ) ∣ value e U i j.val - raw i (j.val+s)

private theorem transfer {e : Corrections} {U : ℕ} {s : ℤ} (grid : gridChecks e U s)
    (i : Fin 7) (x : ℤ) (ok : (denominator i:ℤ)∣raw i (x+s)) : (denominator i:ℤ)∣value e U i x := by
  let P := row e U i - numerator i s
  have deg : P.natDegree≤6 := natDegree_sub_le_of_le (row_degree e U i)
    ((SiftedDivisorWindow.numerator_degree i s).trans (by omega : i.val≤6))
  have sample (j : ℕ) (hj : j≤6) : (denominator i:ℤ)∣P.eval (0+1*j) := by
    simpa only [P,zero_add,one_mul,eval_sub,eval_row,SiftedDivisorWindow.eval_numerator]
      using (grid i ⟨j,by omega⟩)
  have h := DifferenceLane.finite_grid_dvd (denominator i:ℤ) 0 1 P deg sample x
  simp only [P,zero_add,one_mul,eval_sub,eval_row,SiftedDivisorWindow.eval_numerator] at h
  exact (dvd_sub_left ok).mp h

noncomputable def envelope (e : Corrections) (U : ℕ) (i : Fin 7) : ℕ :=
  ChebyshevDivisorWindow.weight U i.val + ∑ j, (e i j).natAbs*(2*U)^j.val

noncomputable def weight (e : Corrections) (U : ℕ) (i : Fin 7) : ℕ :=
  max 1 (envelope e U i / denominator i)

noncomputable def height (e : Corrections) (U : ℕ) (v : Fin 7 → ℤ) : ℤ :=
  ∑ i, |v i| * (weight e U i:ℤ)

private theorem bound {U : ℕ} {x : ℤ} (e : Corrections) (i : Fin 7) (near : |x|≤2*(U:ℤ)) :
    |value e U i x| ≤ (envelope e U i:ℤ) := by
  rw [←eval_row,row,eval_add,HigherDivisorWindow.eval_coeff,envelope,Nat.cast_add,Nat.cast_sum]
  apply (abs_add_le ..).trans (add_le_add (ChebyshevDivisorWindow.eval_bound U i.val x near) ?_)
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro j _
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs,abs_mul,abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) near j.val) (abs_nonneg _)

private noncomputable def combined (e : Corrections) (U : ℕ) (v : Fin 7 → ℤ) : ℤ[X] :=
  ∑ i, C (v i*(scale i:ℤ)) * row e U i

private theorem eval_combined (e : Corrections) (U : ℕ) (v : Fin 7 → ℤ) (x : ℤ) :
    (combined e U v).eval x=∑ i, v i*(scale i:ℤ)*value e U i x := by
  simp only [combined,eval_finset_sum,eval_mul,eval_C,eval_row]

def rowChecks (e : Corrections) (U : ℕ) (v w : Fin 7 → ℤ) : Prop :=
  ∀ j : Fin 7, (∑ i, v i*(scale i:ℤ)*value e U i j.val) = ∑ i, w i*(j.val:ℤ)^i.val

private theorem convert_row {e : Corrections} {U : ℕ} {v w : Fin 7 → ℤ} (checked : rowChecks e U v w) :
    combined e U v=ofFn 7 w := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (v:=fun i : Fin 7 => (i.val:ℤ)) univ
  · intro a _ b _ eq
    change (a.val:ℤ)=(b.val:ℤ) at eq
    exact Fin.ext (by exact_mod_cast eq)
  · have deg : (combined e U v).natDegree≤6 :=
      natDegree_sum_le_of_forall_le _ _ fun i _ => (natDegree_C_mul_le _ _).trans (row_degree e U i)
    rw [card_univ,Fintype.card_fin]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le deg)
  · rw [card_univ,Fintype.card_fin]
    exact ofFn_degree_lt w
  · intro j _
    rw [eval_combined,HigherDivisorWindow.eval_coeff]
    exact checked j

/-- Integrality, the measured bound and the modular root check together
exclude all divisors in the displayed closed interval. -/
theorem excludes {n first U depth modulus : ℕ} {v w : Fin 7 → ℤ} {t s h : ℤ} {e : Corrections}
    (hn : n%2=1) (oddFirst : first%2=1) (anchor : (n:ℤ)∣(first+4*U:ℕ)+2*t)
    (cop : n.Coprime 45360) (align : (105:ℤ)∣(first+4*U:ℕ)-2*s)
    (grid : gridChecks e U s) (checked : rowChecks e U v w) (jets : HigherWindowCertificate.jetChecks w n depth t)
    (measured : height e U v=h) (small : h<(first:ℤ)^depth) (hm : 0<modulus)
    (miss : HigherWindowCertificate.rootChecks w modulus)
    (d : ℕ) (lo : first≤d) (hi : d≤first+8*U) : ¬ d∣n := by
  intro hd
  have odd := Nat.odd_iff.mpr hn
  have unit := (Nat.coprime_two_left.mpr odd).isCoprime
  obtain ⟨q,hq⟩ := hd
  obtain ⟨a,ha⟩ := (Nat.odd_mul.mp (hq ▸ odd)).1
  have dz : (d:ℤ)∣(n:ℤ) := by exact_mod_cast (show d∣n from ⟨q,hq⟩)
  let x := ((d:ℤ)-(first+4*U:ℕ))/2
  have position : (d:ℤ)=(first+4*U:ℕ)+2*x := by dsimp only [x]; omega
  have near : |x|≤2*(U:ℤ) := by rw [abs_le]; dsimp only [x]; omega
  have eql := convert_row checked
  have translated : HigherDivisorWindow.Jets depth n t (combined e U v) := by
    intro j
    rw [eql,HigherDivisorWindow.jet_coeff]
    exact jets j
  have dvd := HigherDivisorWindow.dvd_eval_of_jets translated dz
    (QuarticDivisorWindow.progression_offset unit anchor dz position)
  obtain ⟨b,eb⟩ := Classical.axiomOfChoice fun i => transfer grid i x
    (SiftedDivisorWindow.eligible_divisibility cop.isCoprime dz position align i)
  have eqScaled : (combined e U v).eval x=45360*∑ i, v i*b i := by
    rw [eval_combined,mul_sum]
    apply sum_congr rfl
    intro i _
    have sc : ∀ i, (scale i:ℤ)*(denominator i:ℤ)=45360 := by decide +kernel
    rw [eb i]
    linear_combination v i*b i*sc i
  have bnd : |∑ i, v i*b i| ≤ height e U v := by
    apply (abs_sum_le_sum_abs ..).trans
    apply sum_le_sum
    intro i _
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have smallVal := bound e i near
    rw [eb i,abs_mul,abs_of_nonneg (Int.natCast_nonneg _)] at smallVal
    have pos : ∀ i, 0<denominator i := by decide +kernel
    have div : |b i|≤(envelope e U i:ℤ) / (denominator i:ℤ) :=
      (Int.le_ediv_iff_mul_le (by exact_mod_cast pos i)).mpr (by simpa [mul_comm] using smallVal)
    exact div.trans (by exact_mod_cast (le_max_right 1 (envelope e U i / denominator i)))
  rw [eqScaled] at dvd
  have hit := (cop.isCoprime.of_isCoprime_of_dvd_left dz).pow_left.dvd_of_dvd_mul_left dvd
  have floor := pow_le_pow_left₀ (Int.natCast_nonneg first) (by exact_mod_cast lo : (first:ℤ)≤d) depth
  have zero := Int.eq_zero_of_abs_lt_dvd hit (bnd.trans_lt (measured.trans_lt (small.trans_le floor)))
  apply HigherWindowCertificate.no_integer_root hm miss x
  rw [←eql,eqScaled,zero,mul_zero]

end PrimeFactors.RoundedSiftedWindow
