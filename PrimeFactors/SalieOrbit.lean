import PrimeFactors.FactorSumCRT
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace PrimeFactors

/-- The public trace image from the product alone has one occupied phase for each
admissible sum with unit product. Its size gives the factor sum. -/
theorem salieOrbit_phase_count {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (pp : p ≠ 2) (qq : q ≠ 2) (cop : Nat.Coprime p q) :
    4 * Nat.card {s : ZMod (p*q) // AdmissibleSum 1 s} = (p+1)*(q+1) := by
  have hp := (Fact.out : p.Prime)
  have hq := (Fact.out : q.Prime)
  obtain ⟨k,op⟩ := hp.odd_of_ne_two pp
  obtain ⟨l,oq⟩ := hq.odd_of_ne_two qq
  have cp : 2*((p+1)/2)=p+1 := by omega
  have cq : 2*((q+1)/2)=q+1 := by omega
  have h := card_admissibleSum_crt cop 1
  simp only [Nat.cast_one] at h
  rw [h, card_admissibleSum_eq p _ one_ne_zero, card_admissibleSum_eq q _ one_ne_zero,
    card_factorSumResidues_of_square p pp _ one_ne_zero (by exact IsSquare.one),
    card_factorSumResidues_of_square q qq _ one_ne_zero (by exact IsSquare.one)]
  calc
    _ = (2*((p+1)/2))*(2*((q+1)/2)) := by ring
    _ = _ := by rw [cp,cq]

/-- Rational row and column shifts preserve every alternating rectangle. -/
theorem salieOrbit_rectangle (u v x y a b c d : ℚ) :
    (u*x+a+c)-(u*y+a+d)-(v*x+b+c)+(v*y+b+d)=(u-v)*(x-y) := by ring

private def salieExceptional {ι : Type*} (rows : Finset ι) (slope root : ι → ℚ)
    (target : ℚ → ℚ) (v : ℚ) : Prop :=
  target v ≠ 0 ∧ ∀ i ∈ rows, slope i * (v-root i) = target v

private theorem salieExceptional_unique {ι : Type*} {rows : Finset ι}
    {slope root : ι → ℚ} {target : ℚ → ℚ} {v w : ℚ}
    (different : ∃ i ∈ rows, ∃ j ∈ rows, slope i ≠ slope j)
    (ev : salieExceptional rows slope root target v) (ew : salieExceptional rows slope root target w) :
    v = w := by
  obtain ⟨i,hi,j,hj,neq⟩ := different
  have prod : (slope i-slope j)*(v-w)=0 := by
    linear_combination (ev.2 i hi) - (ev.2 j hj) - (ew.2 i hi) + (ew.2 j hj)
  exact sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left (sub_ne_zero.mpr neq))

private theorem salieExceptional_distinct_roots {ι : Type*} {rows : Finset ι}
    {slope root : ι → ℚ} {target : ℚ → ℚ} {e : ℚ}
    (ee : salieExceptional rows slope root target e) {i j : ι}
    (hi : i ∈ rows) (hj : j ∈ rows) (ss : slope i ≠ slope j) : root i ≠ root j := by
  intro same
  have ei := ee.2 i hi
  have ej := ee.2 j hj
  rw [← same] at ej
  have eq := (mul_left_inj' (sub_ne_zero.mpr (show e ≠ root i by
    intro h
    rw [← h, sub_self, mul_zero] at ei
    exact ee.1 ei.symm))).mp (ei.trans ej.symm)
  exact ss eq

/-- If all nonzero slopes coincide off the horizontal axis, the column's weight
can be paid by the lost multiplicity of their horizontal-axis intersections. -/
private theorem salieExceptional_budget {ι : Type*} {rows : Finset ι}
    {slope root : ι → ℚ} {target : ℚ → ℚ} {e : ℚ} (weight : ℚ → ℕ) (H : ℕ)
    (cap : ∀ t, weight t ≤ H) (light : ∀ t ≠ 0, 2*weight t ≤ H)
    (different : ∃ i ∈ rows, ∃ j ∈ rows, slope i ≠ slope j)
    (ee : salieExceptional rows slope root target e) :
    (∑ i ∈ rows, weight (root i)) + weight e ≤ rows.card*H := by
  classical
  obtain ⟨i,hi,j,hj,ss⟩ := different
  have ij : i ≠ j := fun h => ss (congrArg slope h)
  have distinct := salieExceptional_distinct_roots ee hi hj ss
  let loss (k : ι) := H-weight (root k)
  have total : (∑ k ∈ rows, weight (root k)) + (∑ k ∈ rows, loss k) = rows.card*H := by
    rw [← Finset.sum_add_distrib]
    simp [loss,Nat.add_sub_of_le (cap _)]
  suffices pay : weight e ≤ ∑ k ∈ rows, loss k by omega
  by_cases ez : e = 0
  · have nz (k) (hk : k ∈ rows) : root k ≠ 0 := by
      intro z
      have ek := ee.2 k hk
      rw [← ez] at z
      rw [z, sub_self, mul_zero] at ek
      exact ee.1 ek.symm
    have li := light _ (nz i hi)
    have lj := light _ (nz j hj)
    have pair : loss i+loss j ≤ ∑ k ∈ rows, loss k := by
      have sub : ({i,j} : Finset ι) ⊆ rows := by
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | h
        · exact hi
        · exact Finset.mem_singleton.mp h ▸ hj
      simpa [ij] using Finset.sum_le_sum_of_subset_of_nonneg sub
        (fun k _ _ => Nat.zero_le (loss k))
    have ce := cap e
    apply (le_trans _ pair)
    dsimp [loss]
    omega
  · obtain ⟨k,hk,nk⟩ : ∃ k ∈ rows, root k ≠ 0 := by
      by_cases z : root i = 0
      · exact ⟨j,hj,fun t => distinct (z.trans t.symm)⟩
      · exact ⟨i,hi,z⟩
    have single := Finset.single_le_sum (f:=loss) (fun k _ => Nat.zero_le _) hk
    have ck := light _ nk
    have ce := light _ ez
    apply (le_trans _ single)
    dsimp [loss]
    omega

/-- Count how many positions equal the selected target in one column after
homogenizing rows of the same slope. There are A horizontal rows, all zero. -/
private def salieMatches {ι : Type*} (rows : Finset ι) (slope root : ι → ℚ)
    (target : ℚ → ℚ) (A : ℕ) (v : ℚ) : ℕ :=
  (if target v = 0 then A else 0) +
    (rows.filter fun i => slope i*(v-root i)=target v).card

/-- Any rational row/column offsets after homogenizing equal slopes leave at
least the original number of nonzeros. Equivalently, the matches have mass
at most A times the total column mass plus H times the nonhorizontal rows. -/
theorem salieOrbit_matches_bound {ι : Type*} (rows : Finset ι) (cols : Finset ℚ)
    (slope root : ι → ℚ) (target : ℚ → ℚ) (weight : ℚ → ℕ) (A H : ℕ)
    (mass : rows.card=A+1) (nz : ∀ i ∈ rows, slope i ≠ 0)
    (different : ∃ i ∈ rows, ∃ j ∈ rows, slope i ≠ slope j)
    (cap : ∀ t, weight t ≤ H) (light : ∀ t ≠ 0, 2*weight t ≤ H) :
    (∑ v ∈ cols, weight v * ((if target v = 0 then A else 0) +
      (rows.filter fun i => slope i*(v-root i)=target v).card)) ≤
    A*(∑ v ∈ cols, weight v)+rows.card*H := by
  classical
  let bonus (v : ℚ) := if salieExceptional rows slope root target v then 1 else 0
  let hits (v : ℚ) := (rows.filter fun i => root i=v).card
  have point (v : ℚ) : salieMatches rows slope root target A v ≤ A+hits v+bonus v := by
    by_cases z : target v = 0
    · have same : (rows.filter fun i => slope i*(v-root i)=target v) =
          rows.filter fun i => root i=v := by
        ext i
        simp only [Finset.mem_filter, z]
        constructor
        · rintro ⟨hi,h⟩
          exact ⟨hi,(sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (nz i hi))).symm⟩
        · rintro ⟨hi,h⟩
          simp [hi,h]
      unfold salieMatches
      rw [same,if_pos z]
      exact Nat.le_add_right _ _
    · by_cases off : salieExceptional rows slope root target v
      · have le := Finset.card_filter_le rows (fun i => slope i*(v-root i)=target v)
        simp only [salieMatches,if_neg z,zero_add,bonus,if_pos off]
        omega
      · have proper : (rows.filter fun i => slope i*(v-root i)=target v) ⊂ rows := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨Finset.filter_subset _ _, ?_⟩
          intro all
          apply off
          refine ⟨z,fun i hi => ?_⟩
          have mem : i ∈ rows.filter (fun k => slope k*(v-root k)=target v) := by rw [all]; exact hi
          exact (Finset.mem_filter.mp mem).2
        have lt := Finset.card_lt_card proper
        simp only [salieMatches,if_neg z,zero_add,bonus,if_neg off,add_zero]
        omega
  have hits_le : (∑ v ∈ cols, weight v * hits v) ≤ ∑ i ∈ rows, weight (root i) := by
    calc
      _ = ∑ v ∈ cols, ∑ i ∈ rows, if root i=v then weight v else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        rw [← Finset.sum_filter]
        simp [hits, Nat.mul_comm]
      _ = ∑ i ∈ rows, ∑ v ∈ cols, if root i=v then weight v else 0 := Finset.sum_comm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        rw [Finset.sum_ite_eq]
        split <;> omega
  have budget : (∑ v ∈ cols, weight v*hits v)+(∑ v ∈ cols, weight v*bonus v) ≤ rows.card*H := by
    by_cases some : ∃ e ∈ cols, salieExceptional rows slope root target e
    · obtain ⟨e,he,ee⟩ := some
      have eq (v : ℚ) : salieExceptional rows slope root target v ↔ v=e :=
        ⟨fun ev => salieExceptional_unique different ev ee,fun h => h ▸ ee⟩
      have b : (∑ v ∈ cols, weight v*bonus v)=weight e := by
        simp [bonus,eq,Finset.sum_ite_eq',he]
      rw [b]
      exact (Nat.add_le_add_right hits_le _).trans
        (salieExceptional_budget weight H cap light different ee)
    · have b : (∑ v ∈ cols, weight v*bonus v)=0 := by
        apply Finset.sum_eq_zero
        intro v hv
        have no : ¬salieExceptional rows slope root target v := fun ev => some ⟨v,hv,ev⟩
        simp [bonus,no]
      rw [b,add_zero]
      exact hits_le.trans (by simpa using Finset.sum_le_sum (s:=rows) (fun i _ => cap (root i)))
  calc
    _ ≤ ∑ v ∈ cols, weight v*(A+hits v+bonus v) :=
      Finset.sum_le_sum (fun v _ => Nat.mul_le_mul_left _ (point v))
    _ = A*(∑ v ∈ cols, weight v) + ((∑ v ∈ cols, weight v*hits v)+(∑ v ∈ cols, weight v*bonus v)) := by
      simp only [Nat.mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
      ring
    _ ≤ _ := Nat.add_le_add_left budget _

/-- For the exceptional product 3·5 the three slopes are −1, 0, 1 and the
columns 0, 1, −2 have multiplicities 2, 2, 1. Every translated matrix
has at most nine zeros. -/
theorem salieOrbit_small_profile (a b c d e : ℚ) :
    2*((if a=c then 1 else 0)+(if (0:ℚ)=c then 1 else 0)+(if b=c then 1 else 0))+
    2*((if a-1=d then 1 else 0)+(if (0:ℚ)=d then 1 else 0)+(if b+1=d then 1 else 0))+
    ((if a+2=e then 1 else 0)+(if (0:ℚ)=e then 1 else 0)+(if b-2=e then 1 else 0)) ≤ (9:ℕ) := by
  split_ifs <;> first | decide | exfalso; linarith

end PrimeFactors
