import PrimeFactors.SixSquareLookupStages

/-! Storage for a single table of stride-100 phases at the first three prime
squares. Phase construction visits each position in one period in order.
Byte counts describe packed payloads and exclude collection headers, cursors,
temporary storage and machine-specific allocation. -/
namespace PrimeFactors.ScoreWheelMemory

open Finset SixSquareLookupStages
open scoped Classical

noncomputable abbrev wheel := period 3

theorem wheel_size : wheel=53361 := by decide +kernel
theorem phase_cap : cap 3=3465 := by decide +kernel

/-- The same list of phases is used for every starting residue. Multiplication
by 100 is invertible at every prefix of the wheel. -/
noncomputable def stride (j : Fin 7) : Equiv.Perm (ZMod (period j)) :=
  (ZMod.unitOfCoprime 100 (coprime j)).mulLeft

theorem stride_apply (j : Fin 7) (x : ZMod (period j)) : stride j x=100*x := rfl

private instance (i : Fin 6) : NeZero ((prime i)^2) :=
  ⟨(by decide +kernel : ∀ j : Fin 6,(prime j)^2≠0) i⟩

/-- Square-residue bitset represented by its exact set of one-bit positions. -/
noncomputable def squares (i : Fin 6) : Finset (ZMod ((prime i)^2)) :=
  univ.image (fun x => x*x)

theorem test_iff (i : Fin 6) (n t : ℕ) :
    ((t:ZMod ((prime i)^2))^2-4*n)∈squares i ↔
      AdmissibleSum (n:ZMod ((prime i)^2)) (t:ZMod ((prime i)^2)) := by
  have cop := (by decide +kernel : ∀ j : Fin 6,Nat.Coprime 2 ((prime j)^2)) i
  rw [admissibleSum_iff_isSquare_of_two_unit ((ZMod.isUnit_iff_coprime 2 _).mpr cop)]
  simp only [squares,mem_image,mem_univ,true_and,IsSquare]
  exact exists_congr (fun _ => eq_comm)

noncomputable def test (n x : ℕ) (i : Fin 6) : Bool :=
  decide (((x:ZMod ((prime i)^2))^2-4*n)∈squares i)

/-- Exactly three ordered lookups suffice to decide whether to emit a phase.
Boolean conjunction can stop after the first failed lookup. -/
noncomputable def keep (n j : ℕ) : Bool :=
  test n (100*j) 0 && test n (100*j) 1 && test n (100*j) 2

private theorem step012 (n t : ℕ) : (t:ZMod wheel)∈A n 3 ↔
    (test n t 0 && test n t 1 && test n t 2)=true := by
  let P (i : Fin 7) := (t:ZMod (period i))∈A n i
  let T (i : Fin 6) := AdmissibleSum (n:ZMod ((prime i)^2)) (t:ZMod ((prime i)^2))
  have s2 : P 3 ↔ P 2 ∧ T 2 := step n t 2
  have s1 : P 2 ↔ P 1 ∧ T 1 := step n t 1
  have s0 : P 1 ↔ P 0 ∧ T 0 := step n t 0
  have zero : P 0 := first n t
  simp only [Bool.and_eq_true,test,decide_eq_true_eq,test_iff]
  change P 3 ↔ (T 0 ∧ T 1) ∧ T 2
  rw [s2,s1,s0,and_iff_right zero]

/-- Output after scanning the public phases from zero through the previous index. -/
noncomputable def scan (n stop : ℕ) : List ℕ := (List.range stop).filter (keep n)

theorem scan_start (n : ℕ) : scan n 0=[] := rfl

/-- The next phase takes one append exactly when it passes. This recurrence
permits a forward write cursor with no sorting or stored input range. -/
theorem scan_step (n j : ℕ) : scan n (j+1)=scan n j ++ (if keep n j then [j] else []) := by
  cases h : keep n j <;> simp [scan,List.range_succ,List.filter_append,List.filter_cons,h]

/-- Single ascending pass through one full period, retaining stride phases. -/
noncomputable def phases (n : ℕ) : List ℕ := scan n wheel

theorem construction_capacity {n stop : ℕ} (size : stop≤wheel) :
    (scan n stop).length≤(phases n).length :=
  (List.Sublist.filter (keep n) (List.range_sublist.mpr size)).length_le

theorem mem_phases (n j : ℕ) :
    j∈phases n ↔ j<wheel ∧ stride 3 (j:ZMod wheel)∈A n 3 := by
  simp only [phases,scan,List.mem_filter,List.mem_range,keep,←step012,Nat.cast_mul,Nat.cast_ofNat,stride_apply]

theorem increasing (n : ℕ) : (phases n).Pairwise (· < ·) := List.pairwise_lt_range.filter _

/-- Each stream needs only its starting phase. Adding one to the table phase
advances by 100 in the original sum residues. -/
theorem shared (n : ℕ) (start : ZMod wheel) (k : ℕ) :
    ((stride 3).symm start+(k:ZMod wheel)).val∈phases n ↔
      start+100*(k:ZMod wheel)∈A n 3 := by
  rw [mem_phases,and_iff_right (ZMod.val_lt _),ZMod.natCast_zmod_val,stride_apply,mul_add]
  rw [←stride_apply,(stride 3).apply_symm_apply]

private noncomputable def reached (n : ℕ) (j : Fin 7) (span : ℕ) :=
  (range span).filter (fun i : ℕ => stride j (i:ZMod (period j))∈A n j)

private theorem complete (n : ℕ) (j : Fin 7) (k : ℕ) :
    (reached n j (k*period j)).card=k*(A n j).card := by
  let m := period j
  let e := stride j
  have pos : 0<m := NeZero.pos _
  let index (a : ℕ×ZMod m) := m*a.1+(e.symm a.2).val
  have rem (a : ℕ×ZMod m) : ((index a:ℕ):ZMod m)=e.symm a.2 := by
    simp only [index,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,zero_add,ZMod.natCast_zmod_val]
  have quot (a : ℕ×ZMod m) : index a/m=a.1 := by
    dsimp only [index]
    rw [Nat.add_comm,Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt (ZMod.val_lt _),Nat.zero_add]
  calc
    _ = ((range k)×ˢ(A n j)).card := by
      apply card_bij' (fun i _ => (i/m,e (i:ZMod m))) (fun a _ => index a)
      · intro i hi
        obtain ⟨lo,hit⟩ := mem_filter.mp hi
        exact mem_product.mpr ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul pos).mpr (mem_range.mp lo)),hit⟩
      · intro a ha
        obtain ⟨lo,hit⟩ := mem_product.mp ha
        exact mem_filter.mpr ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul pos).mp
          ((quot a).symm ▸ mem_range.mp lo)), (rem a ▸ e.apply_symm_apply a.2) ▸ hit⟩
      · intro i _
        change m*(i/m)+(e.symm (e (i:ZMod m))).val=i
        rw [e.symm_apply_apply,ZMod.val_natCast,Nat.div_add_mod]
      · intro a _
        exact Prod.ext (quot a) (by rw [rem,e.apply_symm_apply])
    _ = _ := by simp

theorem entries (n : ℕ) : (phases n).length=(A n 3).card := by
  have eq : (phases n).toFinset=reached n 3 wheel := by
    ext j; simp only [List.mem_toFinset,mem_phases,reached,mem_filter,mem_range]
  rw [←List.toFinset_card_of_nodup (increasing n).nodup,eq]
  simpa only [one_mul] using complete n 3 1

theorem entry_bound {n : ℕ} (unit : n.Coprime SixSquareAuxiliarySieve.L) :
    (phases n).length≤3465 := (entries n).le.trans ((card_bound unit 3).trans_eq phase_cap)

theorem entry_bound_sharp : (phases 41).length=3465 := (entries 41).trans ((sharp 3).trans phase_cap)

theorem entry_width {n j : ℕ} (mem : j∈phases n) : j<2^16 :=
  (mem_phases n j).mp mem |>.1.trans (by rw [wheel_size]; decide)

/-- Each 16-bit unsigned entry decodes to its exact phase. -/
theorem packed_roundtrip (n : ℕ) :
    ((phases n).map UInt16.ofNat).map UInt16.toNat=phases n := by
  rw [List.map_map]
  calc
    _ = (phases n).map id := List.map_congr_left fun j hj =>
      UInt16.toNat_ofNat'.trans (Nat.mod_eq_of_lt (entry_width hj))
    _ = _ := List.map_id _

/-- Three tail bitsets separately rounded to whole bytes. -/
theorem tail_bytes : ((prime 3)^2+7)/8=22 ∧ ((prime 4)^2+7)/8=37 ∧ ((prime 5)^2+7)/8=46 := by
  decide +kernel

noncomputable def bytes (i : Fin 6) := ((prime i)^2+7)/8

/-- Packed storage with just the tail bitsets, or with all six still present. -/
theorem payload {n : ℕ} (unit : n.Coprime SixSquareAuxiliarySieve.L) :
    2*(phases n).length≤6930 ∧
    2*(phases n).length+(bytes 3+bytes 4+bytes 5)≤7035 ∧
    2*(phases n).length+(∑ i : Fin 6,bytes i)≤7060 := by
  obtain ⟨a,b,c⟩ := tail_bytes
  have six : (∑ i : Fin 6,bytes i)=130 := table_sizes.2
  have cap := entry_bound unit
  change bytes 3=22 at a
  change bytes 4=37 at b
  change bytes 5=46 at c
  rw [a,b,c,six]
  omega

/-- Stage zero charges the first test for every phase. Stages one and two
charge the next lookup only for phases passing the preceding tests. -/
noncomputable def setupChecks (n : ℕ) := (reached n 0 wheel).card+
  (reached n 1 wheel).card+(reached n 2 wheel).card

/-- Per-phase charging includes the first failure and counts three lookups on
success. The tests here are exactly the Boolean lookups used by the scan. -/
theorem setup_by_phase (n : ℕ) : setupChecks n=∑ j∈range wheel,
    (1+(if test n (100*j) 0 then 1 else 0)+
      (if test n (100*j) 0 && test n (100*j) 1 then 1 else 0)) := by
  simp only [setupChecks,reached,card_filter,←sum_add_distrib]
  apply sum_congr rfl
  intro j _
  let P (i : Fin 7) := stride i (j:ZMod (period i))∈A n i
  have equiv (i : Fin 7) : P i ↔ ((100*j:ℕ):ZMod (period i))∈A n i := by
    simp only [P,stride_apply,Nat.cast_mul,Nat.cast_ofNat]
  have next (i : Fin 6) : P i.succ ↔ P i.castSucc ∧ test n (100*j) i=true := by
    rw [equiv,equiv,step]
    simp only [test,decide_eq_true_eq,test_iff]
  have h0 : P 0 := (equiv 0).mpr (first n _)
  have h1 : P 1 ↔ P 0 ∧ test n (100*j) 0=true := next 0
  have h2 : P 2 ↔ P 1 ∧ test n (100*j) 1=true := next 1
  change (if P 0 then 1 else 0)+(if P 1 then 1 else 0)+(if P 2 then 1 else 0)=_
  simp only [h2,h1,h0,true_and,ite_true,Bool.and_eq_true]

theorem setup_unconditional (n : ℕ) : setupChecks n≤160083 := by
  have le (j : Fin 7) : (reached n j wheel).card≤53361 :=
    (card_le_card (filter_subset _ _)).trans_eq ((card_range _).trans wheel_size)
  unfold setupChecks
  have := le 0; have := le 1; have := le 2; omega

theorem setup_exact (n : ℕ) : setupChecks n=
    53361*(A n 0).card+5929*(A n 1).card+121*(A n 2).card := by
  have calc_stage (j : Fin 7) (k : ℕ) (fit : k*period j=wheel) :=
    fit ▸ complete n j k
  exact congrArg₂ (·+·) (congrArg₂ (·+·) (calc_stage 0 53361 (by decide +kernel))
    (calc_stage 1 5929 (by decide +kernel))) (calc_stage 2 121 (by decide +kernel))

/-- The full-period short-circuit bound is sharp for a unit input. -/
theorem setup_sharp : (∀ n, n.Coprime SixSquareAuxiliarySieve.L → setupChecks n≤78771) ∧
    setupChecks 41=78771 := by
  constructor
  · intro n unit
    have a := card_bound unit 0
    have b := card_bound unit 1
    have c := card_bound unit 2
    change (A n 0).card≤1 at a
    change (A n 1).card≤3 at b
    change (A n 2).card≤63 at c
    rw [setup_exact]
    omega
  · rw [setup_exact,sharp,sharp,sharp]
    decide +kernel

end PrimeFactors.ScoreWheelMemory
