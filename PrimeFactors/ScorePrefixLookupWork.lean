import PrimeFactors.ScorePrefixSieve

/-! A lookup at stage i is charged for each member of the score prefix that
passes the conditions preceding that stage. -/
namespace PrimeFactors.ScorePrefixLookupWork

open Finset ScoreSumOrder ScorePrefixSieve
open scoped Classical
variable {I : Type*} [Fintype I]

/-- The residue set for a stage describes its entry condition. -/
noncomputable def lookups (n lo hi s : ℕ) (L : I→ℕ) (A : ∀ i,Finset (ZMod (L i))) :=
  ∑ i,(filtered n lo hi s (A i)).card

private theorem divide_bound {l k v a : ℕ} (lp : 0<l) (count : l*k≤v*a+10*l*a) :
    (k:ℚ)≤v*((a:ℚ)/l)+10*a := by
  have pos : (0:ℚ)<l := by exact_mod_cast lp
  have raw : (l:ℚ)*k≤v*a+10*l*a := by exact_mod_cast count
  calc
    (k:ℚ) = ((l:ℚ)*k)/l := by field_simp
    _ ≤ (v*a+10*l*a:ℚ)/l := div_le_div_of_nonneg_right raw pos.le
    _ = _ := by field_simp; ring

/-- A bound on each intermediate residue table can replace its exact size. -/
theorem bound_of_caps {n : ℕ} (unit : n%5≠0) (lo hi s : ℕ) (L : I→ℕ)
    (positive : ∀ i,0<L i) (cop : ∀ i,Nat.Coprime 100 (L i))
    (A : ∀ i,Finset (ZMod (L i))) (cap : I→ℕ) (size : ∀ i,(A i).card≤cap i) :
    (lookups n lo hi s L A:ℚ) ≤ (ScoreSumOrder.«prefix» n lo hi s).card *
      (∑ i,(cap i:ℚ)/L i) + 10*(∑ i,cap i : ℕ) := by
  let V := (ScoreSumOrder.«prefix» n lo hi s).card
  have each (i : I) : ((filtered n lo hi s (A i)).card:ℚ) ≤ V*((cap i:ℚ)/L i)+10*cap i := by
    haveI : NeZero (L i) := ⟨(positive i).ne'⟩
    apply (divide_bound (positive i) (filtered_bound unit (cop i) (A i) lo hi s)).trans
    have h : ((A i).card:ℚ)≤cap i := by exact_mod_cast size i
    exact add_le_add (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)) (mul_le_mul_of_nonneg_left h (by norm_num))
  simpa only [lookups,Nat.cast_sum,sum_add_distrib,←mul_sum,V] using sum_le_sum (s:=univ) (fun i _ => each i)

/-- Complete-period lookup densities add, as do the errors from at most
ten incomplete periods per lookup stage. -/
theorem bound {n : ℕ} (unit : n%5≠0) (lo hi s : ℕ) (L : I→ℕ)
    (positive : ∀ i,0<L i) (cop : ∀ i,Nat.Coprime 100 (L i)) (A : ∀ i,Finset (ZMod (L i))) :
    (lookups n lo hi s L A:ℚ) ≤ (ScoreSumOrder.«prefix» n lo hi s).card *
      (∑ i,((A i).card:ℚ)/L i) + 10*(∑ i,(A i).card : ℕ) :=
  bound_of_caps unit lo hi s L positive cop A (fun i => (A i).card) (fun _ => le_rfl)

/-- Counting by actual candidates gives the same number as counting by stage. -/
theorem by_candidate (n lo hi s : ℕ) (L : I→ℕ) (A : ∀ i,Finset (ZMod (L i))) :
    lookups n lo hi s L A=∑ t∈ScoreSumOrder.«prefix» n lo hi s,
      ∑ i,if (t:ZMod (L i))∈A i then 1 else 0 := by
  calc
    _ = ∑ i,∑ t∈ScoreSumOrder.«prefix» n lo hi s,if (t:ZMod (L i))∈A i then 1 else 0 := by
      unfold lookups filtered
      apply sum_congr rfl
      intro i _
      simp
    _ = _ := sum_comm

/-- Exactly the stages reached before stopping, including the first failure. -/
noncomputable def checks {k : ℕ} (test : Fin k→ℕ→Prop) (t : ℕ) :=
  (univ.filter (fun i : Fin k => ∀ j < i,test j t)).card

theorem checks_on_failure {k : ℕ} (test : Fin k→ℕ→Prop) (t : ℕ) (i : Fin k)
    (before : ∀ j < i,test j t) (failed : ¬test i t) : checks test t=i.val+1 := by
  have set : (univ.filter (fun h : Fin k => ∀ j < h,test j t))=Iic i := by
    ext h
    simp only [mem_filter,mem_univ,true_and,mem_Iic]
    exact ⟨fun ok => le_of_not_gt (fun later => failed (ok i later)),
      fun le j lt => before j (lt_of_lt_of_le lt le)⟩
  rw [checks,set,Fin.card_Iic]

theorem checks_on_success {k : ℕ} (test : Fin k→ℕ→Prop) (t : ℕ) (all : ∀ i,test i t) :
    checks test t=k := by simp [checks,all]

/-- If the residue sets encode the conjunction of all previous tests, the
stage-wise count is the number of scalar tests executed by short circuiting. -/
theorem short_circuit {k : ℕ} (n lo hi s : ℕ) (L : Fin k→ℕ) (A : ∀ i,Finset (ZMod (L i)))
    (test : Fin k→ℕ→Prop) (entry : ∀ i t, t∈ScoreSumOrder.«prefix» n lo hi s →
      ((t:ZMod (L i))∈A i ↔ ∀ j < i,test j t)) :
    lookups n lo hi s L A = ∑ t∈ScoreSumOrder.«prefix» n lo hi s,checks test t := by
  rw [by_candidate]
  apply sum_congr rfl
  intro t ht
  simp [entry _ t ht, checks]

end PrimeFactors.ScorePrefixLookupWork
