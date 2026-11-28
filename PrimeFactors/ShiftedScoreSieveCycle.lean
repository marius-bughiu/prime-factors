import Mathlib.Data.Finset.Sort
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! A cyclic index for parallel arithmetic progressions of common step 100.
Every seed uses the same ascending table. Quotient and remainder select
the cycle and the table position within that cycle. -/

namespace PrimeFactors.ShiftedScoreSieveCycle

open Finset
open scoped Classical

variable {M : ℕ} [NeZero M]

/-- The original acceptance set in coordinates where the step equals one. -/
noncomputable def normalized (A : Finset (ZMod M)) : Finset (ZMod M) :=
  univ.filter (fun x => (100:ZMod M)*x∈A)

noncomputable def phase (z : ZMod M) : ℕ := ((100:ZMod M)⁻¹*z).val

/-- Scan the period once in increasing index order, regardless of the seed. -/
noncomputable def table (A : Finset (ZMod M)) : Finset ℕ :=
  (range M).filter (fun j => (j:ZMod M)∈normalized A)

theorem sorted_scan (A : Finset (ZMod M)) :
    (table A).sort (·≤·)=(List.range M).filter (fun j : ℕ => decide ((j:ZMod M)∈normalized A)) := by
  apply List.Sorted.eq_of_mem_iff (table A).sort_sorted_lt
    ((List.sorted_lt_range M).filter _)
  intro x
  simp [table]

omit [NeZero M] in
private theorem inverse (h : Nat.Coprime 100 M) :
    (100:ZMod M)*(100:ZMod M)⁻¹=1 := ZMod.coe_mul_inv_eq_one 100 h

theorem mem_normalized (h : Nat.Coprime 100 M) (A : Finset (ZMod M)) (x : ZMod M) :
    x∈normalized A ↔ ∃ a∈A, x=(100:ZMod M)⁻¹*a := by
  simp only [normalized,mem_filter,mem_univ,true_and]
  have left : (100:ZMod M)⁻¹*100=1 := (mul_comm ..).trans (inverse h)
  constructor
  · intro inside
    exact ⟨100*x,inside,by rw [←mul_assoc,left,one_mul]⟩
  · rintro ⟨a,inside,rfl⟩
    simpa only [←mul_assoc,inverse h,one_mul] using inside

theorem table_nonempty {A : Finset (ZMod M)} (h : Nat.Coprime 100 M) (ha : A.Nonempty) :
    (table A).Nonempty := by
  obtain ⟨x,hx⟩ := ha
  refine ⟨((100:ZMod M)⁻¹*x).val,?_⟩
  simp only [table,normalized,mem_filter,mem_range,ZMod.val_lt,mem_univ,true_and,
    ZMod.natCast_zmod_val,←mul_assoc,inverse h,one_mul,hx]

/-- A phase shift turns each stream's original test into a lookup in the
same normalized table, including indices beyond the first period. -/
theorem accepts_iff (h : Nat.Coprime 100 M) (A : Finset (ZMod M)) (z : ZMod M) (j : ℕ) :
    z+100*(j:ZMod M)∈A ↔ (j+phase z)%M∈table A := by
  have cast : (((j+phase z)%M:ℕ):ZMod M)=(j:ZMod M)+(100:ZMod M)⁻¹*z := by
    simp [phase]
  simp only [table,normalized,mem_filter,mem_range,Nat.mod_lt _ (NeZero.pos M),
    mem_univ,true_and,cast,mul_add,←mul_assoc,inverse h,one_mul,add_comm z]

/-- A hit in the repeated table. The remainder is its zero-based slot. -/
noncomputable def absolute (M : ℕ) (T : Finset ℕ) (h : T.Nonempty) (n : ℕ) :=
  (n/T.card)*M+T.orderEmbOfFin rfl ⟨n%T.card,Nat.mod_lt _ (card_pos.mpr h)⟩

theorem at_slot (M : ℕ) (T : Finset ℕ) (h : T.Nonempty) (q : ℕ) (i : Fin T.card) :
    absolute M T h (q*T.card+i.val)=q*M+T.orderEmbOfFin rfl i := by
  have quotient : (q*T.card+i.val)/T.card=q := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (card_pos.mpr h),Nat.div_eq_of_lt i.isLt,zero_add]
  have rem : (q*T.card+i.val)%T.card=i.val := by simp [Nat.add_comm,Nat.mod_eq_of_lt i.isLt]
  simp only [absolute,quotient,rem]

private theorem blocks {q r x y m : ℕ} (ord : q<r) (lt : x<m) :
    q*m+x<r*m+y := by
  have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt ord)
  rw [Nat.succ_mul] at h
  omega

theorem absolute_strict (M : ℕ) (T : Finset ℕ) (h : T.Nonempty) (bounded : ∀ x∈T,x<M) :
    StrictMono (absolute M T h) := by
  intro i j ij
  let slot (n : ℕ) : Fin T.card := ⟨n%T.card,Nat.mod_lt _ (card_pos.mpr h)⟩
  change i/T.card*M+T.orderEmbOfFin rfl (slot i)<j/T.card*M+T.orderEmbOfFin rfl (slot j)
  rcases lt_or_eq_of_le (Nat.div_le_div_right ij.le) with low|eq
  · exact blocks low (bounded _ (T.orderEmbOfFin_mem rfl _))
  · have a := Nat.div_add_mod' i T.card
    have b := Nat.div_add_mod' j T.card
    rw [eq] at a ⊢
    have less : slot i<slot j := by change i%T.card<j%T.card; omega
    exact Nat.add_lt_add_left ((T.orderEmbOfFin rfl).strictMono less) _

theorem absolute_iff (m : ℕ) (T : Finset ℕ) (h : T.Nonempty) (bounded : ∀ x∈T,x<m) (x : ℕ) :
    (∃ n,absolute m T h n=x) ↔ x%m∈T := by
  constructor
  · rintro ⟨n,rfl⟩
    let i : Fin T.card := ⟨n%T.card,Nat.mod_lt _ (card_pos.mpr h)⟩
    have member := T.orderEmbOfFin_mem rfl i
    change ((n/T.card)*m+T.orderEmbOfFin rfl i)%m∈T
    simp [Nat.add_comm,Nat.mod_eq_of_lt (bounded _ member),member]
  · intro member
    let i := (T.orderIsoOfFin rfl).symm ⟨x%m,member⟩
    have entry : T.orderEmbOfFin rfl i=x%m := congrArg Subtype.val ((T.orderIsoOfFin rfl).apply_symm_apply _)
    refine ⟨(x/m)*T.card+i.val,?_⟩
    rw [at_slot,entry,Nat.div_add_mod']

private theorem enough (M : ℕ) (mp : 0<M) (T : Finset ℕ) (h : T.Nonempty) (c : ℕ) :
    ∃ n,c≤absolute M T h n := by
  let i : Fin T.card := ⟨0,card_pos.mpr h⟩
  refine ⟨c*T.card+i.val,?_⟩
  rw [at_slot]
  exact (Nat.le_mul_of_pos_right _ mp).trans (Nat.le_add_right ..)

/-- The initial table slot is the first absolute position at or above the
seed phase. After initialization the slot advances by one per output. -/
noncomputable def start (M : ℕ) (mp : 0<M) (T : Finset ℕ) (h : T.Nonempty) (c : ℕ) :=
  Nat.find (enough M mp T h c)

noncomputable def output (M : ℕ) (mp : 0<M) (T : Finset ℕ) (h : T.Nonempty) (c k : ℕ) :=
  absolute M T h (start M mp T h c+k)-c

private theorem start_le {M : ℕ} (mp : 0<M) {T : Finset ℕ} (h : T.Nonempty) (bounded : ∀ x∈T,x<M)
    (c k : ℕ) : c≤absolute M T h (start M mp T h c+k) :=
  (Nat.find_spec (enough M mp T h c)).trans
    ((absolute_strict M T h bounded).monotone (Nat.le_add_right _ k))

theorem ordered {M : ℕ} (mp : 0<M) {T : Finset ℕ} (h : T.Nonempty) (bounded : ∀ x∈T,x<M) (c : ℕ) :
    StrictMono (output M mp T h c) := by
  intro i j ij
  have inc := absolute_strict M T h bounded (Nat.add_lt_add_left ij (start M mp T h c))
  have first := start_le mp h bounded c i
  unfold output
  omega

theorem outputs_iff {M : ℕ} (mp : 0<M) {T : Finset ℕ} (h : T.Nonempty)
    (bounded : ∀ x∈T,x<M) (c j : ℕ) :
    (∃ k,output M mp T h c k=j) ↔ (j+c)%M∈T := by
  rw [←absolute_iff M T h bounded]
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨_,(Nat.sub_add_cancel (start_le mp h bounded c k)).symm⟩
  · rintro ⟨n,en⟩
    have floor : c≤absolute M T h n := en ▸ Nat.le_add_left c j
    have prev : start M mp T h c≤n := Nat.find_min' (enough M mp T h c) floor
    exact ⟨n-start M mp T h c,by rw [output,Nat.add_sub_of_le prev,en,Nat.add_sub_cancel]⟩

theorem no_skip {M : ℕ} (mp : 0<M) {T : Finset ℕ} (h : T.Nonempty) (bounded : ∀ x∈T,x<M)
    (c k j : ℕ) (after : output M mp T h c k<j) (accepted : (j+c)%M∈T) :
    output M mp T h c (k+1)≤j := by
  obtain ⟨i,rfl⟩ := (outputs_iff mp h bounded c j).mpr accepted
  have mono := ordered mp h bounded c
  exact mono.monotone (Nat.succ_le_of_lt (mono.lt_iff_lt.mp after))

theorem gap_le {M : ℕ} (mp : 0<M) {T : Finset ℕ} (h : T.Nonempty) (bounded : ∀ x∈T,x<M) (c k : ℕ) :
    output M mp T h c (k+1)≤output M mp T h c k+M := by
  let j := output M mp T h c k
  have accepted := (outputs_iff mp h bounded c j).mp ⟨k,rfl⟩
  apply no_skip mp h bounded c k _ (Nat.lt_add_of_pos_right mp)
  change (j+M+c)%M∈T
  rw [Nat.add_right_comm,Nat.add_mod_right]
  exact accepted

/-- Since phases are period residues, initialization needs at most one
pass through the table. Slot T.card is slot zero in the next period. -/
theorem start_le_card {M : ℕ} (mp : 0<M) {T : Finset ℕ} (h : T.Nonempty) {c : ℕ} (hc : c≤M) :
    start M mp T h c≤T.card := by
  apply Nat.find_min' (enough M mp T h c)
  let first : Fin T.card := ⟨0,card_pos.mpr h⟩
  have wrap := at_slot M T h 1 first
  change absolute M T h (1*T.card+0)=1*M+T.orderEmbOfFin rfl first at wrap
  simp only [one_mul,add_zero] at wrap
  rw [wrap]
  exact hc.trans (Nat.le_add_right ..)

/-- A full lap advances by exactly M original positions. -/
theorem full_lap {M : ℕ} (mp : 0<M) {T : Finset ℕ} (h : T.Nonempty) (bounded : ∀ x∈T,x<M) (c k : ℕ) :
    output M mp T h c (k+T.card)=output M mp T h c k+M := by
  have lap (n : ℕ) : absolute M T h (n+T.card)=absolute M T h n+M := by
    simp only [absolute,Nat.add_div_right _ (card_pos.mpr h),Nat.add_mod_right,Nat.add_mul,one_mul]
    omega
  have base := start_le mp h bounded c k
  rw [output,←Nat.add_assoc,lap,output]
  omega

/-- The increasing outputs give precisely the accepted positions in the
original stream. The table is independent of the seed. -/
theorem stream_exact (h : Nat.Coprime 100 M) {A : Finset (ZMod M)} (ha : A.Nonempty)
    (z : ZMod M) (j : ℕ) :
    (∃ k,output M (NeZero.pos M) (table A) (table_nonempty h ha) (phase z) k=j) ↔
      z+100*(j:ZMod M)∈A := by
  exact (outputs_iff (T:=table A) (NeZero.pos M) (table_nonempty h ha)
    (fun _ hx => mem_range.mp (mem_filter.mp hx).1) (phase z) j).trans (accepts_iff h A z j).symm

end PrimeFactors.ShiftedScoreSieveCycle
