import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! Abstract row counts for a materialized list joined to a streamed one. A
rank is a position in any enumeration of the left rows. A winning rank
guarantees a result by itself. An occupied rank only guarantees a match,
which may be false. Costs here count rows, independently of bucket accesses,
exponentiations, and the number of matching pairs inside one row. -/
namespace PrimeFactors.StreamedSumBudget

open Finset

/-- The first winning row in each traversal direction. -/
theorem orientation {A : ℕ} (S : Finset ℕ) (nonempty : S.Nonempty)
    (inside : ∀ t∈S, t<A) :
    (S.min' nonempty+1)+(A-S.max' nonempty)+S.card ≤ A+2 := by
  let lo := S.min' nonempty
  let hi := S.max' nonempty
  have sub : S ⊆ Icc lo hi := fun t ht => mem_Icc.mpr ⟨S.min'_le t ht,S.le_max' t ht⟩
  have count := card_le_card sub
  rw [Nat.card_Icc] at count
  have top := inside hi (S.max'_mem nonempty)
  have both : lo≤hi := S.min'_le _ (S.max'_mem nonempty)
  change (lo+1)+(A-hi)+S.card ≤ A+2
  omega

/-- Once two distinct occupied rows suffice, the second occupied rank from
each end bounds the two visits. With three occupied rows these can coincide. -/
theorem two_occupied {A : ℕ} (S : Finset ℕ) (three : 3≤S.card)
    (inside : ∀ t∈S, t<A) :
    ∃ lo∈S, ∃ front∈S, ∃ back∈S, ∃ hi∈S,
      lo<front ∧ front≤back ∧ back<hi ∧ (front+1)+(A-back)+S.card≤A+4 := by
  have ne : S.Nonempty := card_pos.mp (by omega)
  let lo := S.min' ne
  let hi := S.max' ne
  have low : lo∈S := S.min'_mem ne
  have high : hi∈S := S.max'_mem ne
  have ends : lo<hi := by
    have span := orientation S ne inside
    have top := inside hi high
    change (lo+1)+(A-hi)+S.card ≤ A+2 at span
    omega
  let middle := (S.erase lo).erase hi
  have mem (t) : t∈middle ↔ t≠hi ∧ t≠lo ∧ t∈S := by simp [middle]
  have size : middle.card+2=S.card := by
    have hh : hi∈S.erase lo := mem_erase.mpr ⟨ends.ne',high⟩
    simp only [middle,card_erase_of_mem hh,card_erase_of_mem low]
    omega
  have mn : middle.Nonempty := card_pos.mp (by omega)
  let front := middle.min' mn
  let back := middle.max' mn
  have mf := (mem front).mp (middle.min'_mem mn)
  have mb := (mem back).mp (middle.max'_mem mn)
  have lf : lo≤front := S.min'_le _ mf.2.2
  have bh : back≤hi := S.le_max' _ mb.2.2
  have ranks := orientation middle mn (fun t h => inside t ((mem t).mp h).2.2)
  change (front+1)+(A-back)+middle.card≤A+2 at ranks
  exact ⟨lo,low,front,mf.2.2,back,mb.2.2,hi,high,lt_of_le_of_ne lf mf.2.1.symm,
    middle.min'_le _ (middle.max'_mem mn),lt_of_le_of_ne bh mb.1,by omega⟩

variable {A : ℕ} [NeZero A]

/-- All cyclic starting rows for which one of the next K positions lies in S. -/
noncomputable def starts (S : Finset (ZMod A)) (K : ℕ) : Finset (ZMod A) := by
  classical
  exact univ.filter (fun c => ∃ j∈range K, c+(j:ZMod A)∈S)

theorem mem_starts (S : Finset (ZMod A)) (K : ℕ) (c : ZMod A) :
    c∈starts S K ↔ ∃ j<K, c+(j:ZMod A)∈S := by simp [starts]

private theorem one (S : Finset (ZMod A)) : starts S 1=S := by
  ext c
  simp [starts]

private theorem mono (S : Finset (ZMod A)) (K : ℕ) :
    starts S K ⊆ starts S (K+1) := by
  intro c h
  obtain ⟨i,hi,hv⟩ := (mem_starts ..).mp h
  exact (mem_starts ..).mpr ⟨i,by omega,hv⟩

private theorem previous (S : Finset (ZMod A)) (K : ℕ) {c : ZMod A}
    (h : c∈starts S K) : c-1∈starts S (K+1) := by
  obtain ⟨i,hi,hv⟩ := (mem_starts ..).mp h
  refine (mem_starts ..).mpr ⟨i+1,by omega,?_⟩
  simpa [Nat.cast_add,sub_add_add_cancel] using hv

private theorem full_of_closed {S : Finset (ZMod A)} (ne : S.Nonempty)
    (back : ∀ c∈S, c-1∈S) : S=univ := by
  obtain ⟨a,ha⟩ := ne
  have walk (i : ℕ) : a-(i:ZMod A)∈S := by
    induction i with
    | zero => simpa using ha
    | succ i ih => simpa [Nat.cast_succ,sub_add_eq_sub_sub] using back _ ih
  apply eq_univ_of_forall
  intro b
  simpa using walk (a-b).val

/-- For H nonempty winning ranks, at least min(A,H+K−1) cyclic starting
positions reach one of them within K positive visits. -/
theorem rotation_bound (S : Finset (ZMod A)) (ne : S.Nonempty) (k : ℕ) :
    min A (S.card+k) ≤ (starts S (k+1)).card := by
  induction k with
  | zero => simp [one]
  | succ k ih =>
    let U := starts S (k+1)
    let V := starts S (k+1+1)
    have sub : U⊆V := mono S (k+1)
    have inhabited : U.Nonempty := by
      obtain ⟨c,hc⟩ := ne
      exact ⟨c,(mem_starts ..).mpr ⟨0,by omega,by simpa using hc⟩⟩
    by_cases eq : U=V
    · have full := full_of_closed inhabited (fun c h => eq ▸ previous S _ h)
      have any : V=univ := eq.symm.trans full
      change _ ≤ V.card
      rw [any,card_univ,ZMod.card]
      exact min_le_left ..
    · have strict := card_lt_card (ssubset_of_subset_of_ne sub eq)
      change min A (S.card+k)≤U.card at ih
      change min A (S.card+(k+1))≤V.card
      omega

/-- Consecutive winning ranks give the smallest hit probability, assuming
a uniformly chosen start. The window itself need not have distinct sums. -/
noncomputable def run (A H : ℕ) : Finset (ZMod A) :=
  (range H).image (fun i : ℕ => (i : ZMod A))

omit [NeZero A] in
private theorem run_card (H : ℕ) (small : H≤A) : (run A H).card=H := by
  unfold run
  rw [card_image_of_injOn,card_range]
  intro i hi j hj e
  have iv : i<A := (mem_range.mp hi).trans_le small
  have jv : j<A := (mem_range.mp hj).trans_le small
  simpa only [ZMod.val_natCast_of_lt iv,ZMod.val_natCast_of_lt jv] using congrArg ZMod.val e

theorem rotation_sharp {H : ℕ} (hp : 0<H) (small : H≤A) (k : ℕ) :
    (starts (run A H) (k+1)).card=min A (H+k) := by
  have size := run_card H small
  have ne : (run A H).Nonempty := card_pos.mp (by rw [size]; exact hp)
  have lower := rotation_bound (run A H) ne k
  rw [size] at lower
  apply le_antisymm _ lower
  apply le_min
  · simpa using (card_le_univ (starts (run A H) (k+1)))
  · have sub : starts (run A H) (k+1) ⊆
        (range (H+k)).image (fun i : ℕ => (i:ZMod A)-(k:ZMod A)) := by
      intro s hs
      obtain ⟨j,hj,hit⟩ := (mem_starts ..).mp hs
      obtain ⟨i,hi,eq⟩ := mem_image.mp hit
      have room : j≤k := by omega
      refine mem_image.mpr ⟨i+(k-j),mem_range.mpr (by have := mem_range.mp hi; omega),?_⟩
      rw [Nat.cast_add,Nat.cast_sub room,eq]
      abel
    exact (card_le_card sub).trans (card_image_le.trans_eq (card_range _))

/-- One winning rank gives exactly K/A probability for a K-row cyclic prefix
when K≤A, for any original row permutation. -/
theorem single (winner : ZMod A) (K : ℕ) :
    (starts {winner} K).card=min A K := by
  cases K with
  | zero => simp [starts]
  | succ k =>
    apply le_antisymm _ (by simpa [Nat.add_comm] using rotation_bound {winner} (singleton_nonempty _) k)
    apply le_min
    · simpa using (card_le_univ (starts {winner} (k+1)))
    · have sub : starts {winner} (k+1) ⊆ (range (k+1)).image (fun i : ℕ => winner-(i:ZMod A)) := by
        intro s hs
        obtain ⟨j,hj,eq⟩ := (mem_starts ..).mp hs
        exact mem_image.mpr ⟨j,mem_range.mpr hj,(eq_sub_iff_add_eq.mpr (mem_singleton.mp eq)).symm⟩
      exact (card_le_card sub).trans (card_image_le.trans_eq (card_range _))

/-- For a uniformly random starting rank, the exact average cost to reach a
designated row is (A+1)/2. A sooner stopping rule only decreases this count. -/
theorem cyclic_visits (winner : ZMod A) :
    (∑ s : ZMod A, ((winner-s).val+1))*2 = A*(A+1) := by
  have rot : (∑ s : ZMod A, ((winner-s).val+1)) = ∑ s : ZMod A, (s.val+1) :=
    Equiv.sum_comp (Equiv.subLeft winner) (fun s => s.val+1)
  have contents : (∑ s : ZMod A, (s.val+1)) = ∑ i∈range A, (i+1) := by
    apply sum_bij' (fun (s:ZMod A) _ => s.val) (fun i _ => (i:ZMod A))
    · intro s _; exact mem_range.mpr (ZMod.val_lt s)
    · intro i _; exact mem_univ _
    · intro s _; exact ZMod.natCast_zmod_val s
    · intro i hi; exact ZMod.val_natCast_of_lt (mem_range.mp hi)
    · intro _ _; rfl
  rw [rot,contents,sum_add_distrib,Nat.add_mul,sum_range_id_mul_two]
  simp only [sum_const,card_range,smul_eq_mul,mul_one]
  have pos : 0<A := NeZero.pos _
  rcases A with _|A
  · omega
  · simp only [Nat.add_sub_cancel]
    ring

/-- The sum of visits in the two directions for a designated true row. -/
theorem single_visits {t A : ℕ} (h : t<A) : (t+1)+(A-t)=A+1 := by omega

/-- With one unit charged per materialized row or visited row, building B≤A
then scanning A to a designated row saves (A−B)/2 in expected work over
choosing the opposite orientation. Memory holds B rows. -/
theorem materialize_smaller {A B : ℕ} (h : B≤A) :
    (2*B+(A+1))+(A-B)=2*A+(B+1) := by omega

end PrimeFactors.StreamedSumBudget
