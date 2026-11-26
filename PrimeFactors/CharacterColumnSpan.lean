import PrimeFactors.CharacterDivisorColumn
import PrimeFactors.ShortPascalRow
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Compare candidate counts over the whole feasible factor interval and
over the smaller-factor interval, with exact endpoint clipping. -/
namespace PrimeFactors.CharacterColumnSpan

open Finset

/-- Count the retained offsets i for which the absolute address L+i has
one of the prescribed residues. An interval of length zero is empty. -/
noncomputable def visits (L length P : ℕ) (mask : Finset ℕ) : ℕ :=
  ∑ i ∈ range length, if (L+i)%P∈mask then 1 else 0

theorem visits_card (L length P : ℕ) (mask : Finset ℕ) :
    visits L length P mask=((range length).filter fun i => (L+i)%P∈mask).card := by
  simp [visits]

private theorem residue_inj (L P len : ℕ) (clip : len≤P) :
    Set.InjOn (fun i : ℕ => (L+i)%P) (range len : Set ℕ) := by
  intro a ha b hb eq
  have h := Nat.ModEq.add_left_cancel' L (show Nat.ModEq P (L+a) (L+b) from eq)
  change a%P=b%P at h
  have al := (mem_range.mp ha).trans_le clip
  have bl := (mem_range.mp hb).trans_le clip
  simpa only [Nat.mod_eq_of_lt al,Nat.mod_eq_of_lt bl] using h

theorem clipped {L len P : ℕ} (clip : len≤P) (mask : Finset ℕ) :
    visits L len P mask ≤ mask.card := by
  rw [visits_card]
  apply card_le_card_of_injOn (fun i : ℕ => (L+i)%P) (fun _ hi => (mem_filter.mp hi).2)
  intro a ha b hb eq
  exact residue_inj L P len clip (mem_filter.mp ha).1 (mem_filter.mp hb).1 eq

theorem complete {L P : ℕ} (pos : 0<P) {mask : Finset ℕ} (valid : mask ⊆ range P) :
    visits L P P mask=mask.card := by
  let f (i : ℕ) := (L+i)%P
  have inj := residue_inj L P P le_rfl
  have surj : (range P).image f=range P := by
    apply eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨i,_,rfl⟩ := mem_image.mp hr
      exact mem_range.mpr (Nat.mod_lt _ pos)
    · rw [card_image_of_injOn inj]
  rw [visits_card]
  apply card_nbij f (fun _ hi => (mem_filter.mp hi).2)
  · intro i hi j hj eq
    exact inj (mem_filter.mp hi).1 (mem_filter.mp hj).1 eq
  · intro r hr
    obtain ⟨i,hi,eq⟩ := mem_image.mp (show r∈(range P).image f by rw [surj]; exact valid hr)
    exact ⟨i,mem_filter.mpr ⟨hi,eq ▸ hr⟩,eq⟩

private theorem append (L P k r : ℕ) (mask : Finset ℕ) :
    visits L (k*P+r) P mask=visits L (k*P) P mask+visits L r P mask := by
  unfold visits
  rw [sum_range_add]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [show L+(k*P+i)=(L+i)+k*P by omega,Nat.add_mul_mod_self_right]

theorem exact_count {L P : ℕ} (pos : 0<P) {mask : Finset ℕ} (valid : mask ⊆ range P)
    (k r : ℕ) : visits L (k*P+r) P mask=k*mask.card+visits L r P mask := by
  have blocks (j : ℕ) : visits L (j*P) P mask=j*mask.card := by
    induction j with
    | zero => simp [visits]
    | succ j ih => rw [Nat.succ_mul,append,ih,complete pos valid,Nat.succ_mul]
  rw [append,blocks]

private theorem monotone (L P : ℕ) {a b : ℕ} (le : a≤b) (mask : Finset ℕ) :
    visits L a P mask ≤ visits L b P mask := by
  rw [visits_card,visits_card]
  exact card_le_card (filter_subset_filter _ (fun _ ha => mem_range.mpr ((mem_range.mp ha).trans_le le)))

private theorem split_mask {L len P : ℕ} {A D : Finset ℕ} (sub : D⊆A) :
    visits L len P A=visits L len P D+visits L len P (A\D) := by
  unfold visits
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases small : (L+i)%P∈D
  · simp [small,sub small]
  · by_cases large : (L+i)%P∈A <;> simp [small,large]

private theorem decompose {U P : ℕ} (up : 0<U) (pos : 0<P) :
    ∃ k r, U=k*P+r ∧ 1≤r ∧ r≤P := by
  have div := Nat.div_add_mod (U-1) P
  have rem := Nat.mod_lt (U-1) pos
  refine ⟨(U-1)/P,(U-1)%P+1,?_,by omega,by omega⟩
  rw [Nat.mul_comm P _] at div
  omega

/-- A half-sized sign mask also works in a different phase or with
unrelated labels. At most one ordinary period of savings can arise from
clipping. The lengths are inclusive counts, so 2U−1 is sufficient. -/
theorem compare {L₁ L₂ U S P : ℕ} {A D : Finset ℕ} (pos : 0<P)
    (span : 2*U≤S+1) (va : A⊆range P) (vd : D⊆range P) (half : 2*D.card=A.card) :
    visits L₁ U P A ≤ visits L₂ S P D + A.card := by
  rcases Nat.eq_zero_or_pos U with rfl|up
  · simp [visits]
  obtain ⟨k,r,eq,rp,clip⟩ := decompose up pos
  have len : (2*k)*P≤S := by rw [Nat.mul_assoc]; omega
  have long := monotone L₂ P len D
  have blocks := exact_count (L:=L₂) pos vd (2*k) 0
  simp only [Nat.add_zero,show visits L₂ 0 P D=0 by simp [visits]] at blocks
  rw [blocks,show 2*k*D.card=k*A.card by rw [←half]; ring] at long
  rw [eq,exact_count pos va]
  have tail := clipped (L:=L₁) clip A
  omega

/-- With a common start and nested masks, the only potential saving is
the unselected half of a single period. -/
theorem compare_nested {L U S P : ℕ} {A D : Finset ℕ} (pos : 0<P)
    (span : 2*U≤S+1) (va : A⊆range P) (sub : D⊆A) (half : 2*D.card=A.card) :
    visits L U P A ≤ visits L S P D + D.card := by
  rcases Nat.eq_zero_or_pos U with rfl|up
  · simp [visits]
  obtain ⟨k,r,eq,rp,clip⟩ := decompose up pos
  have len : (2*k)*P+r≤S := by rw [Nat.mul_assoc]; omega
  have long := monotone L P len D
  rw [exact_count pos (sub.trans va),show 2*k*D.card=k*A.card by rw [←half]; ring] at long
  rw [eq,exact_count pos va,split_mask (len:=r) sub]
  have tail := clipped (L:=L) clip (A\D)
  have splitCount := card_sdiff_add_card_eq_card sub
  omega

theorem geometry {n H L : ℕ} (cover : n≤H*L) :
    2*(n.sqrt+1-L)≤(H+1-L)+1 := by
  have sq := Nat.sqrt_le n
  have middle : 2*n.sqrt≤H+L := by
    zify at sq cover ⊢
    nlinarith [sq_nonneg ((H:ℤ)-(L:ℤ))]
  omega

/-- H=2B−1, L=max(B,ceil(n/H)), with no factor input. -/
theorem public_compare {n B P : ℕ} (bp : 0<B) (pos : 0<P) {A D : Finset ℕ}
    (va : A⊆range P) (sub : D⊆A) (half : 2*D.card=A.card) :
    let H := 2*B-1
    let L := ShortPascalRow.lower n B
    visits L (n.sqrt+1-L) P A ≤ visits L (H+1-L) P D + D.card := by
  let H := 2*B-1
  have hp : 0<H := by dsimp [H]; omega
  have ceil := Nat.lt_mul_div_succ (n-1) hp
  have bound : n≤H*((n-1)/H+1) := by omega
  have cap : n≤H*ShortPascalRow.lower n B :=
    bound.trans (Nat.mul_le_mul_left H (le_max_right ..))
  exact compare_nested pos (geometry cap) va sub half

/-- Shared wheel residues for the ordinary and signed scans. -/
noncomputable def units (P : ℕ) := (range P).filter fun a => a.Coprime P

noncomputable def signed (P : ℕ) (d ε : ℤ) := (units P).filter fun a => jacobiSym d a=ε

private theorem mod_coprime {a P : ℕ} : (a%P).Coprime P ↔ a.Coprime P := by
  unfold Nat.Coprime
  rw [←Nat.gcd_rec P a,Nat.gcd_comm P a]

private theorem odd_unit {a P : ℕ} {d : ℤ} (period : 4*d.natAbs ∣ P) (unit : a.Coprime P) :
    Odd a :=
  (unit.of_dvd_right ((dvd_mul_of_dvd_left (by decide : 2∣4) _).trans period)).odd_of_right

theorem residue_sign {a P : ℕ} {d ε : ℤ} (pos : 0<P) (period : 4*d.natAbs ∣ P) :
    a%P∈signed P d ε ↔ a.Coprime P ∧ jacobiSym d a=ε := by
  simp only [signed,units,mem_filter,mem_range,Nat.mod_lt _ pos,true_and,mod_coprime]
  by_cases unit : a.Coprime P
  · have sign := CharacterDivisorColumn.periodic (odd_unit period (mod_coprime.mpr unit))
      (odd_unit period unit) d ((Nat.mod_modEq a P).of_dvd period)
    simp [unit,sign]
  · simp [unit]

/-- Multiplication by N permutes the wheel units and switches signs.
The half-density holds even when d shares primes with the wheel. -/
theorem signed_half {n P : ℕ} {d : ℤ} (pos : 0<P) (period : 4*d.natAbs ∣ P)
    (wheel : n.Coprime P) (select : jacobiSym d n= -1) {ε : ℤ} (sign : ε=1 ∨ ε= -1) :
    2*(signed P d ε).card=(units P).card := by
  have nz : n≠0 := (odd_unit period wheel).pos.ne'
  have map_le (s : ℤ) : (signed P d s).card ≤ (signed P d (-s)).card := by
    apply card_le_card_of_injOn (fun a : ℕ => (n*a)%P)
    · intro a ha
      obtain ⟨u,hs⟩ := mem_filter.mp ha
      have au := (mem_filter.mp u).2
      apply (residue_sign pos period).mpr
      refine ⟨Nat.coprime_mul_iff_left.mpr ⟨wheel,au⟩,?_⟩
      rw [jacobiSym.mul_right' _ nz (odd_unit period au).pos.ne',select,hs,neg_one_mul]
    · intro a ha b hb eq
      have h := Nat.ModEq.cancel_left_of_coprime wheel.symm (show Nat.ModEq P (n*a) (n*b) from eq)
      have al := mem_range.mp (mem_filter.mp (mem_filter.mp ha).1).1
      have bl := mem_range.mp (mem_filter.mp (mem_filter.mp hb).1).1
      change a%P=b%P at h
      simpa only [Nat.mod_eq_of_lt al,Nat.mod_eq_of_lt bl] using h
  have cards : (signed P d 1).card=(signed P d (-1)).card :=
    le_antisymm (map_le 1) (by simpa only [neg_neg] using map_le (-1))
  have cover : signed P d 1 ∪ signed P d (-1)=units P := by
    apply Subset.antisymm (union_subset (filter_subset ..) (filter_subset ..))
    intro a ha
    have au := (mem_filter.mp ha).2
    have ad := au.of_dvd_right ((dvd_mul_left d.natAbs 4).trans period)
    have sym := jacobiSym.eq_one_or_neg_one (a:=d) (b:=a) (by
      rw [Int.gcd_eq_natAbs,Int.natAbs_natCast]
      exact ad.symm)
    exact sym.elim (fun plus => mem_union_left _ (mem_filter.mpr ⟨ha,plus⟩))
      (fun minus => mem_union_right _ (mem_filter.mpr ⟨ha,minus⟩))
  have disj : Disjoint (signed P d 1) (signed P d (-1)) := by
    apply disjoint_left.mpr
    intro a h m
    have := (mem_filter.mp h).2
    have := (mem_filter.mp m).2
    omega
  rw [←cover,card_union_of_disjoint disj,cards]
  rcases sign with rfl|rfl <;> simp only [cards,two_mul]

/-- Exact comparison for a Jacobi sign on a matched unit wheel. It requires
only public inputs, including the same cheap wheel and selector checks used
to choose the residue mask. -/
theorem jacobi_compare {n B P : ℕ} {d ε : ℤ} (bp : 0<B) (pos : 0<P)
    (period : 4*d.natAbs ∣ P) (wheel : n.Coprime P) (select : jacobiSym d n= -1)
    (sign : ε=1 ∨ ε= -1) :
    let L := ShortPascalRow.lower n B
    visits L (n.sqrt+1-L) P (units P) ≤
      visits L (2*B-1+1-L) P (signed P d ε)+(signed P d ε).card :=
  public_compare bp pos (filter_subset ..) (filter_subset ..) (signed_half pos period wheel select sign)

end PrimeFactors.CharacterColumnSpan
