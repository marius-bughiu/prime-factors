import PrimeFactors.SumClueOrbitRanks

/-! Optimal ranks when the modular sum is reported through a finite partition.
The underlying population has a fixed unit product and a uniform first unit.
Each one-based guess names an unordered complementary pair of residues. -/

namespace PrimeFactors.CompressedSumClue

open Finset FactorOrbitGuessRanks
open SumClueOrbitRanks (clue)
open PrimeSquareSumWeights (weight)
open FiveSquareGuessRanks (score)
open scoped Classical
open private PrimeFactors.SumClueOrbitRanks.labelFintype PrimeFactors.SumClueOrbitRanks.singles
  PrimeFactors.SumClueOrbitRanks.mass PrimeFactors.SumClueOrbitRanks.one_single
  PrimeFactors.SumClueOrbitRanks.sum_mass PrimeFactors.SumClueOrbitRanks.sum_singles
  PrimeFactors.SumClueOrbitRanks.normalize
  from PrimeFactors.SumClueOrbitRanks
open private PrimeFactors.FactorOrbitGuessRanks.integer_optimum PrimeFactors.FactorOrbitGuessRanks.sizes
  from PrimeFactors.FactorOrbitGuessRanks
open private PrimeFactors.FiveSquareGuessRanks.overlap from PrimeFactors.FiveSquareGuessRanks
attribute [local instance 2000] PrimeFactors.SumClueOrbitRanks.labelFintype

variable {α β : Type*} [Fintype α] [Fintype β]
variable {m : ℕ} [NeZero m]
private abbrev U (m : ℕ) := (ZMod m)ˣ

/-- Sum the weights of the fine labels with this report. -/
noncomputable def pool (f : α→β) (w : α→ℕ) (b : β) := ∑ x : {x // f x=b},w x.val

omit [Fintype β] in
private theorem pool_as_sum (f : α→β) (w : α→ℕ) (b : β) :
    pool f w b=∑ x,if f x=b then w x else 0 := by
  have h := sum_subtype (F:=inferInstanceAs (Fintype {x // f x=b})) (p:=fun x => f x=b) (univ.filter (fun x => f x=b)) (by simp) w
  rw [sum_filter] at h
  exact h.symm

private theorem pool_total (f : α→β) (w : α→ℕ) : (∑ b,pool f w b)=∑ a,w a :=
  Fintype.sum_fiberwise f w

/-- Number of singleton orbits with each original sum. -/
noncomputable def diagonal (u : U m) (s : ZMod m) := PrimeFactors.SumClueOrbitRanks.singles u s

theorem diagonal_le_one (u : U m) (two : IsUnit (2 : ZMod m)) (s : ZMod m) :
    diagonal u s≤1 := PrimeFactors.SumClueOrbitRanks.one_single u two s

abbrev Row (u : U m) (f : ZMod m→β) (b : β) := {o : Label u // f (clue u o)=b}
abbrev Policy (u : U m) (f : ZMod m→β) := ∀ b : β, Fin (Fintype.card (Row u f b)) ≃ Row u f b

private noncomputable def position {u : U m} {f : ZMod m→β} (P : Policy u f) (o : Label u) :=
  ((P (f (clue u o))).symm ⟨o,rfl⟩).val+1

noncomputable def mean {u : U m} {f : ZMod m→β} (P : Policy u f) : ℚ :=
  ((∑ a : U m,position P (label u a):ℕ):ℚ)/Fintype.card (U m)

omit [Fintype β] in
private theorem pool_rows (u : U m) (f : ZMod m→β) (b : β) (g : Label u→ℕ) :
    (∑ o : Row u f b,g o.val)=pool f (fun s => ∑ o : SumClueOrbitRanks.Row u s,g o.val) b := by
  let e : (Σ s : {s // f s=b}, SumClueOrbitRanks.Row u s.val) ≃ Row u f b :=
    { toFun := fun x => ⟨x.2.val,x.2.property.symm ▸ x.1.property⟩
      invFun := fun x => ⟨⟨clue u x.val,x.property⟩,x.val,rfl⟩
      left_inv := fun ⟨⟨s,h⟩,⟨o,eq⟩⟩ => by change clue u o=s at eq; subst s; rfl
      right_inv := fun x => rfl }
  have h := e.sum_comp (fun o => g o.val)
  rw [Fintype.sum_sigma] at h
  exact h.symm

private def w {u : U m} {f : ZMod m→β} {b : β} (o : Row u f b) := o.val.val.card

omit [Fintype β] in
private theorem mass (u : U m) (f : ZMod m→β) (b : β) :
    (∑ o : Row u f b,w o)=pool f (weight u.val.val) b := by
  refine (pool_rows u f b (fun o => o.val.card)).trans (congrArg (fun v => pool f v b) ?_)
  exact funext (fun s => PrimeFactors.SumClueOrbitRanks.mass u s)

omit [Fintype β] in
private theorem singles (u : U m) (f : ZMod m→β) (b : β) :
    (∑ o : Row u f b,if w o=1 then 1 else 0)=pool f (diagonal u) b :=
  pool_rows u f b (fun o => if o.val.card=1 then 1 else 0)

private theorem row_cost {γ : Type*} [Fintype γ] (v : γ→ℕ) (sizes : ∀ x,v x=1 ∨ v x=2)
    {M D : ℕ} (total : (∑ x,v x)=M) (diags : (∑ x,if v x=1 then 1 else 0)=D) :
    ∃ k : ℕ, IsLeast (Set.range (score v)) k ∧ 4*k=M^2+2*M+D^2 := by
  obtain ⟨k,least,h⟩ := PrimeFactors.FactorOrbitGuessRanks.integer_optimum v
  have term (x : γ) : (if v x=1 then 1 else 0)+v x=2 := by
    rcases sizes x with hx|hx <;> simp [hx]
  have both := sum_congr (rfl : (univ : Finset γ)=univ) (fun x _ => term x)
  simp only [sum_add_distrib,diags,total,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id] at both
  have cnt : (D:ℝ)+M=Fintype.card γ*2 := by exact_mod_cast both
  have tot : (∑ x,(v x:ℝ))=(M:ℝ) := by exact_mod_cast total
  rw [total] at h
  have overlap : (2:ℝ)*k=M+∑ x,∑ y,min (v x:ℝ) (v y:ℝ) := by
    dsimp only [PrimeFactors.FiveSquareGuessRanks.overlap] at h
    exact_mod_cast h
  rw [FirstPowerGuessOverlap.one_two v sizes,tot,
    show (Fintype.card γ:ℝ)=((D:ℝ)+M)/2 by linarith only [cnt]] at overlap
  have formula : (4:ℝ)*k=(M:ℝ)^2+2*M+(D:ℝ)^2 := by nlinarith only [overlap]
  exact ⟨k,least,by exact_mod_cast formula⟩

private theorem sum_scores {u : U m} {f : ZMod m→β} (P : Policy u f) :
    (∑ a,position P (label u a))=∑ b,score w (P b) := by
  calc
    _ = ∑ o : Label u,o.val.card*position P o := by_orbit u (position P)
    _ = ∑ b,∑ o : Row u f b,o.val.val.card*position P o.val :=
      (Fintype.sum_fiberwise (fun o => f (clue u o)) (fun o => o.val.card*position P o)).symm
    _ = _ := ?_
  apply sum_congr rfl
  intro b _
  have each (o : Row u f b) : position P o.val=((P b).symm o).val+1 := by
    rcases o with ⟨o,rfl⟩; rfl
  simp_rw [each]
  have h := (P b).sum_comp (fun o : Row u f b => o.val.val.card*(((P b).symm o).val+1))
  simpa only [Equiv.symm_apply_apply,w,score,Nat.mul_comm] using h.symm

/-- A report retains the total ordered-pair mass and the singleton-orbit
count in each of its bins. Both enter the optimum as second moments. -/
noncomputable def cost (u : U m) (f : ZMod m→β) : ℚ :=
  1/2+(((∑ b,pool f (weight u.val.val) b^2:ℕ):ℚ)+((∑ b,pool f (diagonal u) b^2:ℕ):ℚ))/
    (4*Fintype.card (U m))

theorem optimal (u : U m) (f : ZMod m→β) : IsLeast (Set.range (mean (u:=u) (f:=f))) (cost u f) := by
  choose k least eq using fun b => row_cost (w (u:=u) (f:=f) (b:=b))
    (fun o => PrimeFactors.FactorOrbitGuessRanks.sizes u o.val) (mass u f b) (singles u f b)
  have all := sum_congr (rfl : (univ : Finset β)=univ) (fun b _ => eq b)
  simp only [←mul_sum,sum_add_distrib,pool_total,PrimeFactors.SumClueOrbitRanks.sum_mass] at all
  have size : (0:ℚ)<Fintype.card (U m) := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card (U m))
  have rat : (4:ℚ)*(∑ b,k b:ℕ)=((∑ b,pool f (weight u.val.val) b^2:ℕ):ℚ)+
      2*Fintype.card (U m)+((∑ b,pool f (diagonal u) b^2:ℕ):ℚ) := by exact_mod_cast all
  have val : ((∑ b,k b:ℕ):ℚ)/Fintype.card (U m)=cost u f :=
    PrimeFactors.SumClueOrbitRanks.normalize size rat
  rw [←val]
  choose P attained using fun b => (least b).1
  constructor
  · exact ⟨P,by simp only [mean,sum_scores,attained]⟩
  · rintro _ ⟨P,rfl⟩
    apply div_le_div_of_nonneg_right _ size.le
    rw [sum_scores]
    exact_mod_cast sum_le_sum (s:=univ) (fun b _ => (least b).2 ⟨P b,rfl⟩)

/-- Send the second sum to the first and preserve every other report. -/
noncomputable def merge (s t x : α) := if x=t then s else x

private theorem pool_merge (s t : α) (w : α→ℕ) (b : α) :
    pool (merge s t) w b=(if b=t then 0 else w b)+(if b=s then w t else 0) := by
  have term (x : α) :
      (if merge s t x=b then w x else 0) =
      (if x=b then (if b=t then 0 else w b) else 0)+
        (if x=t then (if b=s then w t else 0) else 0) := by
    by_cases h : x=t <;> by_cases k : x=b <;> by_cases j : b=s <;> simp_all [merge]
    all_goals exact fun eq => (j eq.symm).elim
  rw [pool_as_sum]
  simp_rw [term,sum_add_distrib]
  simp

/-- The second moment gains exactly one cross term in each direction. -/
theorem merge_second (s t : α) (ne : s≠t) (w : α→ℕ) :
    (∑ b,pool (merge s t) w b^2)=(∑ b,w b^2)+2*w s*w t := by
  have row (b : α) : pool (merge s t) w b^2+(if b=t then w t^2 else 0)=
      w b^2+(if b=s then w t^2+2*w s*w t else 0) := by
    rw [pool_merge]
    by_cases h : b=t <;> by_cases k : b=s <;> simp_all
    ring
  have all := sum_congr (rfl : (univ : Finset α)=univ) (fun b _ => row b)
  simp only [sum_add_distrib,sum_ite_eq',mem_univ,if_true] at all
  omega

private theorem pool_id (w : α→ℕ) (a : α) : pool id w a=w a := by simp [pool_as_sum]

/-- The second moment weights each original label by the total mass of
all labels receiving the same report. -/
theorem second_eq (f : α→β) (w : α→ℕ) :
    (∑ b,pool f w b^2)=∑ a,w a*pool f w (f a) := by
  have row (b : β) : (∑ x : {a // f a=b},w x.val*pool f w (f x.val))=pool f w b^2 := by
    have same (x : {a // f a=b}) : f x.val=b := x.property
    simp_rw [same]
    rw [←sum_mul,pow_two]
    rfl
  simpa only [row] using Fintype.sum_fiberwise f (fun a => w a*pool f w (f a))

omit [Fintype β] in
private theorem has_mass (f : α→β) (w : α→ℕ) (a : α) : w a≤pool f w (f a) := by
  let x : {z // f z=f a} := ⟨a,rfl⟩
  exact single_le_sum (f:=fun y : {z // f z=f a} => w y.val)
    (fun z _ => Nat.zero_le _) (mem_univ x)

theorem second_le (f : α→β) (w : α→ℕ) : (∑ a,w a^2)≤∑ b,pool f w b^2 := by
  rw [second_eq]
  exact sum_le_sum (fun a _ => pow_two (w a) ▸ Nat.mul_le_mul_left (w a) (has_mass f w a))

theorem second_lt (f : α→β) (w : α→ℕ) {s t : α} (ne : s≠t) (same : f s=f t)
    (hs : 0<w s) (ht : 0<w t) : (∑ a,w a^2)<∑ b,pool f w b^2 := by
  rw [second_eq]
  apply sum_lt_sum (fun a _ => pow_two (w a) ▸ Nat.mul_le_mul_left (w a) (has_mass f w a))
  refine ⟨s,mem_univ _,?_⟩
  let a : {z // f z=f s} := ⟨s,rfl⟩
  let b : {z // f z=f s} := ⟨t,same.symm⟩
  have apart : a≠b := fun h => ne (congrArg Subtype.val h)
  have both := sum_le_sum_of_subset_of_nonneg (f:=fun x : {z // f z=f s} => w x.val)
    (subset_univ ({a,b}:Finset _)) (fun _ _ _ => Nat.zero_le _)
  rw [sum_pair apart] at both
  change w s+w t≤pool f w (f s) at both
  rw [pow_two]
  exact Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le (Nat.lt_add_of_pos_right ht) both) hs

/-- Any finite report that identifies two attained sums has strictly worse
optimal mean than the full sum, even if it also merges other sums. -/
theorem strict_partition (u : U m) (f : ZMod m→β) {s t : ZMod m} (ne : s≠t)
    (same : f s=f t) (hs : 0<weight u.val.val s) (ht : 0<weight u.val.val t) :
    cost u id<cost u f := by
  simp only [cost,pool_id]
  apply add_lt_add_left
  apply div_lt_div_of_pos_right _ (mul_pos (by norm_num) (by exact_mod_cast (Fintype.card_pos : 0<Fintype.card (U m))))
  exact add_lt_add_of_lt_of_le (by exact_mod_cast second_lt f (weight u.val.val) ne same hs ht)
    (by exact_mod_cast second_le f (diagonal u))

private theorem second_of_inj (f : α→β) (w : α→ℕ) (inj : Set.InjOn f {a | 0<w a}) :
    (∑ b,pool f w b^2)=∑ a,w a^2 := by
  rw [second_eq]
  apply sum_congr rfl
  intro a _
  by_cases empty : w a=0
  · simp [empty]
  have pos := Nat.pos_of_ne_zero empty
  have row : pool f w (f a)=w a := by
    rw [pool_as_sum]
    rw [sum_eq_single a]
    · simp
    · intro b _ ne
      by_cases same : f b=f a
      · have vacant : w b=0 := by
          by_contra h
          exact ne (inj (Nat.pos_of_ne_zero h) pos same)
        simp [vacant]
      · simp [same]
    · simp
  rw [row,pow_two]

theorem diagonal_le_weight (u : U m) (s : ZMod m) : diagonal u s≤weight u.val.val s := by
  change (∑ o : SumClueOrbitRanks.Row u s, if o.val.val.card=1 then 1 else 0)≤_
  rw [←PrimeFactors.SumClueOrbitRanks.mass u s]
  apply sum_le_sum
  intro o _
  change (if o.val.val.card=1 then 1 else 0)≤o.val.val.card
  split_ifs with h <;> omega

theorem full_le (u : U m) (f : ZMod m→β) : cost u id≤cost u f := by
  simp only [cost,pool_id]
  apply add_le_add_left
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact add_le_add (by exact_mod_cast second_le f (weight u.val.val))
    (by exact_mod_cast second_le f (diagonal u))

/-- Exactly the distinctions among sums attained by an actual pair matter.
Unattained sums can be assigned any report without loss. -/
theorem cost_eq_iff (u : U m) (f : ZMod m→β) :
    cost u f=cost u id ↔ Set.InjOn f {s | 0<weight u.val.val s} := by
  constructor
  · intro equal s hs t ht same
    by_contra different
    exact (strict_partition u f different same hs ht).ne' equal
  · intro inj
    have subset : {s | 0<diagonal u s} ⊆ {s | 0<weight u.val.val s} := by
      intro s hs
      exact lt_of_lt_of_le hs (diagonal_le_weight u s)
    simp only [cost,pool_id,second_of_inj f _ inj,second_of_inj f _ (inj.mono subset)]

/-- Identity reporting is the same experiment as supplying the complete sum. -/
theorem full_optimum (u : U m) (two : IsUnit (2 : ZMod m)) :
    IsLeast (Set.range (SumClueOrbitRanks.mean (u:=u))) (cost u id) := by
  have sq (s : ZMod m) : diagonal u s^2=diagonal u s := by
    rcases (show diagonal u s=0 ∨ diagonal u s=1 by have := diagonal_le_one u two s; omega) with h|h <;> simp [h]
  have total : (∑ s,diagonal u s)=SquareFiberMoments.roots u := PrimeFactors.SumClueOrbitRanks.sum_singles u
  simp only [cost,pool_id,sq,total]
  exact SumClueOrbitRanks.mean_optimum u two

/-- Exact increase in the optimal mean when just two distinct labels are
merged. This also applies to even moduli, for which a sum can have
multiple singleton orbits. -/
theorem merge_cost (u : U m) (s t : ZMod m) (ne : s≠t) :
    cost u (merge s t)=cost u id+
      (((weight u.val.val s:ℚ)*weight u.val.val t+(diagonal u s:ℚ)*diagonal u t)/
        (2*Fintype.card (U m))) := by
  simp only [cost,merge_second s t ne,pool_id,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have positive : (0:ℚ)<Fintype.card (U m) := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card (U m))
  field_simp [positive.ne']
  ring

/-- Losing the distinction between any two attained sums strictly
increases the best inclusive rank. -/
theorem strict_merge (u : U m) (s t : ZMod m) (ne : s≠t)
    (hs : 0<weight u.val.val s) (ht : 0<weight u.val.val t) : cost u id<cost u (merge s t) := by
  rw [merge_cost u s t ne]
  apply lt_add_of_pos_right
  have size : (0:ℚ)<Fintype.card (U m) := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card (U m))
  exact div_pos (add_pos_of_pos_of_nonneg (mul_pos (by exact_mod_cast hs) (by exact_mod_cast ht))
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) (mul_pos (by norm_num) size)

end PrimeFactors.CompressedSumClue
