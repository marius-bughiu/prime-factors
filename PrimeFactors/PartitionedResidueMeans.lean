import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Replace the distribution inside each band by uniform coordinates while
keeping exactly the observed probability mass of every band. -/
namespace PrimeFactors.PartitionedResidueMeans

open Finset
variable {I X : Type*} [Fintype I] [Fintype X]

/-- Number of observations in a band and in the complete sample. -/
noncomputable def rowPopulation (w : I→X→ℕ) (i : I) := ∑ x,w i x
noncomputable def population (w : I→X→ℕ) := ∑ i,rowPopulation w i

noncomputable def actual (w : I→X→ℕ) (c : I→X→ℝ) :=
  (∑ i,∑ x,(w i x:ℝ)*c i x)/(population w:ℝ)

/-- The uniform mean in each band is multiplied by its observed population.
A completely empty band contributes zero to the numerator. -/
noncomputable def mixture (w : I→X→ℕ) (c : I→X→ℝ) :=
  (∑ i,(rowPopulation w i:ℝ)*((∑ x,c i x)/(Fintype.card X:ℝ)))/(population w:ℝ)

private theorem mean_error [Nonempty X] (w : X→ℕ) {E : ℕ}
    (spread : ∀ x y,w x≤w y+E) (x : X) : |(w x:ℝ)-(∑ y,(w y:ℝ))/Fintype.card X|≤E := by
  have p : (0:ℝ)<Fintype.card X := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card X)
  have upper := sum_le_sum (s:=univ) (fun y _ => (show (w x:ℝ)≤w y+E by exact_mod_cast spread x y))
  have lower := sum_le_sum (s:=univ) (fun y _ => (show (w y:ℝ)≤w x+E by exact_mod_cast spread y x))
  simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul] at upper lower
  apply abs_le.mpr
  constructor
  · have hi : (∑ y,(w y:ℝ))/Fintype.card X ≤ w x+E :=
      (div_le_iff₀ p).mpr (by nlinarith only [lower])
    linarith only [hi]
  · have lo : (w x:ℝ)-E ≤ (∑ y,(w y:ℝ))/Fintype.card X :=
      (le_div_iff₀ p).mpr (by nlinarith only [upper])
    linarith only [lo]

omit [Fintype I] in
private theorem row_numerator (w : I→X→ℕ) (c : I→X→ℝ) (i : I) :
    (rowPopulation w i:ℝ)*((∑ x,c i x)/(Fintype.card X:ℝ)) =
      ∑ x, ((∑ y,(w i y:ℝ))/Fintype.card X)*c i x := by
  rw [←mul_sum]
  simp only [rowPopulation,Nat.cast_sum]
  ring

/-- If every two coordinate counts in a band differ by at most E, the
observed mean differs from the band-preserving mixture by this amount. -/
theorem transfer (w : I→X→ℕ) (c : I→X→ℝ) {E : ℕ} {C : ℝ}
    (spread : ∀ i x y,w i x≤w i y+E) (costs : ∀ i x,0≤c i x ∧ c i x≤C)
    (positive : 0<population w) :
    |actual w c - mixture w c| ≤ Fintype.card I*E*C*Fintype.card X/(population w:ℝ) := by
  classical
  haveI : Nonempty X := by
    by_contra h
    haveI := not_nonempty_iff.mp h
    simp [population,rowPopulation] at positive
  let δ (i : I) (x : X) := ((w i x:ℝ)-(∑ y,(w i y:ℝ))/Fintype.card X)*c i x
  have cap (i : I) (x : X) : |δ i x|≤(E:ℝ)*C := by
    dsimp only [δ]
    rw [abs_mul,abs_of_nonneg (costs i x).1]
    exact mul_le_mul (mean_error (w i) (spread i) x) (costs i x).2 (costs i x).1 (Nat.cast_nonneg _)
  have band (i : I) : |∑ x,δ i x| ≤ (Fintype.card X:ℝ)*((E:ℝ)*C) := by
    exact (abs_sum_le_sum_abs _ _).trans (by
      simpa only [sum_const,card_univ,nsmul_eq_mul] using sum_le_sum (s:=univ) (fun x _ => cap i x))
  have total : |∑ i,∑ x,δ i x| ≤ Fintype.card I*E*C*Fintype.card X := by
    apply (abs_sum_le_sum_abs _ _).trans
    exact (sum_le_sum (s:=univ) (fun i _ => band i)).trans_eq (by simp; ring)
  have p : 0<(population w:ℝ) := by exact_mod_cast positive
  unfold actual mixture
  rw [←sub_div,abs_div,abs_of_pos p]
  apply div_le_div_of_nonneg_right _ p.le
  simpa only [δ,sub_mul,sum_sub_distrib,←row_numerator] using total

/-- Column-wise lower bounds control the total record count without an
individual lower bound in every band. -/
theorem population_lower (w : I→X→ℕ) {M : ℕ} (floor : ∀ x,M≤∑ i,w i x) :
    Fintype.card X*M≤population w := by
  have h := sum_le_sum (s:=univ) (fun x _ => floor x)
  simpa only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,sum_comm (f:=fun x i => w i x),population,rowPopulation] using h

/-- With at least M records for each coordinate across all bands, the
normalized bound is independent of the number of coordinates. -/
theorem transfer_of_floor [Nonempty X] (w : I→X→ℕ) (c : I→X→ℝ) {E M : ℕ} {C : ℝ}
    (spread : ∀ i x y,w i x≤w i y+E) (costs : ∀ i x,0≤c i x ∧ c i x≤C)
    (hM : 0<M) (floor : ∀ x,M≤∑ i,w i x) :
    |actual w c-mixture w c| ≤ Fintype.card I*E*C/(M:ℝ) := by
  classical
  have h := population_lower w floor
  have p := (Nat.mul_pos (Fintype.card_pos (α:=X)) hM).trans_le h
  haveI : Nonempty I := by
    by_contra v
    haveI := not_nonempty_iff.mp v
    simp [population] at p
  have cn := (costs (Classical.choice ‹Nonempty I›) (Classical.choice ‹Nonempty X›)).1.trans
    (costs (Classical.choice ‹Nonempty I›) (Classical.choice ‹Nonempty X›)).2
  apply (transfer w c spread costs p).trans
  apply (div_le_div_iff₀ (by exact_mod_cast p) (by exact_mod_cast hM)).mpr
  have right := mul_le_mul_of_nonneg_left
    (show (Fintype.card X:ℝ)*M≤population w by exact_mod_cast h)
    (show 0≤(Fintype.card I:ℝ)*E*C by positivity)
  simpa only [mul_assoc] using right

private theorem constant_total (w : I→X→ℕ) (q : ℝ) :
    (∑ i,(rowPopulation w i:ℝ)*q)=q*population w := by
  rw [←sum_mul,population,Nat.cast_sum,mul_comm]

/-- An upper bound shared by every uniform row mean bounds the mixture. -/
theorem mixture_le (w : I→X→ℕ) (c : I→X→ℝ) {q : ℝ} (positive : 0<population w)
    (upper : ∀ i,(∑ x,c i x)/(Fintype.card X:ℝ)≤q) : mixture w c≤q := by
  unfold mixture
  rw [div_le_iff₀ (by exact_mod_cast positive),←constant_total w q]
  exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (upper i) (Nat.cast_nonneg _))

/-- A lower bound shared by every uniform row mean bounds the mixture. -/
theorem le_mixture (w : I→X→ℕ) (c : I→X→ℝ) {q : ℝ} (positive : 0<population w)
    (lower : ∀ i,q≤(∑ x,c i x)/(Fintype.card X:ℝ)) : q≤mixture w c := by
  unfold mixture
  rw [le_div_iff₀ (by exact_mod_cast positive),←constant_total w q]
  exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (lower i) (Nat.cast_nonneg _))

/-- Equal row means stay equal after reweighting the bands by population. -/
theorem mixture_eq (w : I→X→ℕ) (c : I→X→ℝ) {q : ℝ} (positive : 0<population w)
    (same : ∀ i,(∑ x,c i x)/(Fintype.card X:ℝ)=q) : mixture w c=q :=
  le_antisymm (mixture_le w c positive (fun i => (same i).le))
    (le_mixture w c positive (fun i => (same i).ge))

/-- Each band may choose its own policy. -/
private abbrev selected {A : I→Type*} (score : (i : I)→A i→X→ℝ) (P : ∀ i,A i) :=
  fun i => score i (P i)

/-- A finite policy family in each band attains an observed minimum within
ε of the common minimum of the uniform row means. -/
theorem minimum_near {A : I→Type*} [∀ i,Fintype (A i)] (w : I→X→ℕ)
    (score : (i : I)→A i→X→ℝ) {q ε : ℝ} (positive : 0<population w)
    (row : ∀ i, IsLeast (Set.range (fun a : A i => (∑ x,score i a x)/(Fintype.card X:ℝ))) q)
    (near : ∀ P : ∀ i,A i, |actual w (selected score P)-mixture w (selected score P)|≤ε) :
    ∃ P, IsLeast (Set.range (fun Q => actual w (selected score Q))) (actual w (selected score P)) ∧
      |actual w (selected score P)-q|≤ε := by
  classical
  choose Q same using fun i => (row i).1
  have optimum := mixture_eq w (selected score Q) positive same
  letI : Nonempty (∀ i,A i) := ⟨Q⟩
  obtain ⟨P,_,least⟩ := univ.exists_min_image (fun p => actual w (selected score p)) univ_nonempty
  have floor := le_mixture w (selected score P) positive (fun i => (row i).2 ⟨P i,rfl⟩)
  have comparison := least Q (mem_univ _)
  have lower := (abs_le.mp (near P)).1
  have upper := (abs_le.mp (near Q)).2
  refine ⟨P,⟨⟨P,rfl⟩,fun y ⟨p,h⟩ => h ▸ least p (mem_univ _)⟩,abs_le.mpr ⟨?_,?_⟩⟩
  · linarith only [floor,lower]
  · linarith only [comparison,upper,optimum]

/-- The corresponding bound for maximizing a score such as success rate. -/
theorem maximum_near {A : I→Type*} [∀ i,Fintype (A i)] (w : I→X→ℕ)
    (score : (i : I)→A i→X→ℝ) {q ε : ℝ} (positive : 0<population w)
    (row : ∀ i, IsGreatest (Set.range (fun a : A i => (∑ x,score i a x)/(Fintype.card X:ℝ))) q)
    (near : ∀ P : ∀ i,A i, |actual w (selected score P)-mixture w (selected score P)|≤ε) :
    ∃ P, IsGreatest (Set.range (fun Q => actual w (selected score Q))) (actual w (selected score P)) ∧
      |actual w (selected score P)-q|≤ε := by
  classical
  choose Q same using fun i => (row i).1
  have optimum := mixture_eq w (selected score Q) positive same
  letI : Nonempty (∀ i,A i) := ⟨Q⟩
  obtain ⟨P,_,greatest⟩ := univ.exists_max_image (fun p => actual w (selected score p)) univ_nonempty
  have cap := mixture_le w (selected score P) positive (fun i => (row i).2 ⟨P i,rfl⟩)
  have comparison := greatest Q (mem_univ _)
  have lower := (abs_le.mp (near Q)).1
  have upper := (abs_le.mp (near P)).2
  refine ⟨P,⟨⟨P,rfl⟩,fun y ⟨p,h⟩ => h ▸ greatest p (mem_univ _)⟩,abs_le.mpr ⟨?_,?_⟩⟩
  · linarith only [comparison,lower,optimum]
  · linarith only [cap,upper]

end PrimeFactors.PartitionedResidueMeans
