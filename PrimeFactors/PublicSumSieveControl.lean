import PrimeFactors.FactorSum
import PrimeFactors.LevelMaskCertificate
import PrimeFactors.SumIntervalExclusion
import PrimeFactors.SquareDivisorClueWindow

/-! Product-only local sum constraints on the previously published 39-bit
control. Index i represents 1295590+4i; the masks contain only modular
product information. The known prime certificate is used at the end. -/
namespace PrimeFactors.PublicSumSieveControl

open LevelMaskCertificate

private abbrev N : ℕ := 419636024497
private abbrev start : ℕ := 1295590
private abbrev width : ℕ := 7273
private def sumAt (i : ℕ) := start+4*i

/-- The lower bound uses the square discriminant. The upper uses only
the 20-bit lower endpoint A, via A(p+q) ≤ N+A². -/
theorem public_bounds {p q : ℕ} (prod : p*q=N) (low : 2^19 ≤ p) (low' : 2^19 ≤ q) :
    1295587 ≤ p+q ∧ p+q ≤ 1324680 ∧ (p+q)%4=2 := by
  have am : 4*(p*q) ≤ (p+q)^2 := by nlinarith only [sq_nonneg ((p:ℤ)-q)]
  have cap : 524288*(p+q) ≤ p*q+524288^2 := by
    zify at low low' ⊢
    nlinarith only [mul_nonneg (sub_nonneg.mpr low) (sub_nonneg.mpr low')]
  have odd : (p*q)%2=1 := prod ▸ (by decide)
  have cls := SumIntervalExclusion.sum_congruence odd
  rw [prod] at am cap cls
  dsimp only [N] at am cap cls
  refine ⟨?_,by omega,cls⟩
  by_contra! h
  have sq := Nat.pow_le_pow_left (show p+q≤1295586 by omega) 2
  omega

theorem public_positions (s : ℕ) :
    (1295587 ≤ s ∧ s ≤ 1324680 ∧ s%4=2) ↔ ∃ i < width, s=sumAt i := by
  dsimp only [sumAt,start,width]
  constructor
  · intro h
    exact ⟨(s-1295590)/4,by omega,by omega⟩
  · rintro ⟨i,hi,rfl⟩
    omega

private def rows : List (ℕ × ℕ) :=
  [(3,3),(5,12),(7,85),(11,1928),(13,3258),(17,113474),(19,258698),
   (23,2473380),(29,95073340),(31,1131164601),(37,58233747675),
   (41,1043140421555),(43,7702738069518)]

private def gate (p i : ℕ) : Prop :=
  ∃ a : Fin p, (a.val*(sumAt i+p-a.val))%p=N%p

private instance (p i : ℕ) : Decidable (gate p i) := by unfold gate; infer_instance

private theorem gate_iff (p i : ℕ) (pos : 0 < p) :
    gate p (i%p) ↔ AdmissibleSum (N:ZMod p) (sumAt i : ZMod p) := by
  letI : NeZero p := ⟨pos.ne'⟩
  have same : (sumAt (i%p):ZMod p) = (sumAt i:ZMod p) := by
    simp [sumAt,Nat.cast_add,Nat.cast_mul,ZMod.natCast_mod]
  have criterion (a : Fin p) :
      (a.val*(sumAt (i%p)+p-a.val))%p=N%p ↔
      (a.val:ZMod p)*((sumAt i:ZMod p)-a.val)=(N:ZMod p) := by
    rw [← ZMod.natCast_eq_natCast_iff',Nat.cast_mul,Nat.cast_sub (by have := a.isLt; omega),
      Nat.cast_add,ZMod.natCast_self,add_zero,same]
  constructor
  · rintro ⟨a,h⟩
    exact ⟨a.val,(sumAt i:ZMod p)-a.val,(criterion a).mp h,by ring⟩
  · rintro ⟨x,y,prod,add⟩
    let a : Fin p := ⟨x.val,ZMod.val_lt x⟩
    refine ⟨a,(criterion a).mpr ?_⟩
    change (x.val:ZMod p)*(_-(x.val:ZMod p))=_
    rw [ZMod.natCast_zmod_val,←add]
    simpa only [add_sub_cancel_left] using prod

/-- Each short row is checked against every possible modular sum and
all possible first factors, without the input's prime factors. -/
private theorem row_certificate : ∀ r ∈ rows,
    0<r.1 ∧ r.2<2^r.1 ∧ width≤r.1*2^12 ∧
      ∀ i : Fin r.1, r.2.testBit i.val = true ↔ gate r.1 i.val := by
  decide +kernel

private theorem repeated_iff {p w : ℕ} (small : w<2^p) (d i : ℕ) :
    (repeatWord p w d).testBit i=true ↔ i<p*2^d ∧ w.testBit (i%p)=true := by
  induction d generalizing i with
  | zero =>
    simp only [repeatWord,pow_zero,mul_one]
    by_cases h : i<p
    · simp [h,Nat.mod_eq_of_lt h]
    · have hi : p ≤ i := by omega
      simp [h,Nat.testBit_lt_two_pow (small.trans_le (Nat.pow_le_pow_right (by decide) hi))]
  | succ d ih =>
    rw [repeatWord,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_shiftLeft,Bool.and_eq_true,
      decide_eq_true_eq,ih,ih,pow_succ,←mul_assoc]
    by_cases h : i < p*2^d
    · have top : i < p*2^d*2 := by omega
      simp [h,top,not_le.mpr h]
    · have le : p*2^d ≤ i := by omega
      have congr : (i-p*2^d)%p=i%p := by
        rw [← Nat.add_mul_mod_self_left (i-p*2^d) p (2^d),Nat.sub_add_cancel le]
      have half : i-p*2^d < p*2^d ↔ i < p*2^d*2 := by omega
      simp [h,le,congr,half]

private def packed : List (ℕ×ℕ) → ℕ
  | [] => 2^width-1
  | r::rs => repeatWord r.1 r.2 12 &&& packed rs

private theorem packed_iff (ls : List (ℕ×ℕ)) (sub : ∀ r∈ls, r∈rows) (i : ℕ) :
    (packed ls).testBit i = true ↔ i<width ∧
      ∀ r ∈ ls, AdmissibleSum (N:ZMod r.1) (sumAt i:ZMod r.1) := by
  induction ls with
  | nil => simp [packed]
  | cons r rs ih =>
    obtain ⟨pos,small,room,cert⟩ := row_certificate r (sub r (by simp))
    have localEq := (cert ⟨i%r.1,Nat.mod_lt _ pos⟩).trans (gate_iff r.1 i pos)
    rw [packed,Nat.testBit_and,Bool.and_eq_true,repeated_iff small,ih
      (fun t ht => sub t (List.mem_cons_of_mem _ ht)),localEq]
    simp only [List.forall_mem_cons]
    constructor
    · rintro ⟨⟨_,a⟩,hi,all⟩
      exact ⟨hi,a,all⟩
    · rintro ⟨hi,a,all⟩
      exact ⟨⟨hi.trans_le room,a⟩,hi,all⟩

/-- Public inequalities and the first k modular product/sum tests. -/
def survives (k s : ℕ) : Prop :=
  (1295587≤s ∧ s≤1324680 ∧ s%4=2) ∧
  ∀ row ∈ rows.take k, AdmissibleSum (N:ZMod row.1) (s:ZMod row.1)

theorem public_tests (k s : ℕ) : survives k s ↔
    (1295587≤s ∧ s≤1324680 ∧ s%4=2) ∧
    ∀ p ∈ ([3,5,7,11,13,17,19,23,29,31,37,41,43] : List ℕ).take k,
      AdmissibleSum (N:ZMod p) (s:ZMod p) := by
  change _ ↔ _ ∧ ∀ p ∈ (rows.map Prod.fst).take k, _
  rw [←List.map_take,List.forall_mem_map]
  rfl

private theorem survives_iff (k s : ℕ) :
    survives k s ↔ ∃ i, (packed (rows.take k)).testBit i=true ∧ s=sumAt i := by
  constructor
  · rintro ⟨bounds,all⟩
    obtain ⟨i,hi,rfl⟩ := (public_positions s).mp bounds
    exact ⟨i,(packed_iff _ (fun _ h => List.mem_of_mem_take h) i).mpr ⟨hi,all⟩,rfl⟩
  · rintro ⟨i,h,rfl⟩
    obtain ⟨hi,all⟩ := (packed_iff _ (fun _ k => List.mem_of_mem_take k) i).mp h
    exact ⟨(public_positions _).mpr ⟨i,hi,rfl⟩,all⟩

private theorem masks :
    packed (rows.take 12) = 2^3738 ||| 2^6442 ||| 2^7102 ∧
    packed (rows.take 13) = 2^3738 := by decide +kernel

theorem through41 (s : ℕ) : survives 12 s ↔ s=1310542 ∨ s=1321358 ∨ s=1323998 := by
  rw [survives_iff,masks.1]
  simp only [Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,decide_eq_true_eq,sumAt,start]
  constructor
  · rintro ⟨i,h,rfl⟩
    omega
  · rintro (rfl|rfl|rfl)
    · exact ⟨3738,by decide,by decide⟩
    · exact ⟨6442,by decide,by decide⟩
    · exact ⟨7102,by decide,by decide⟩

theorem through43 (s : ℕ) : survives 13 s ↔ s=1310542 := by
  rw [survives_iff,masks.2]
  simp only [Nat.testBit_two_pow,decide_eq_true_eq,sumAt,start]
  constructor
  · rintro ⟨i,rfl,rfl⟩
    rfl
  · rintro rfl
    exact ⟨3738,rfl,rfl⟩

/-- All sums at stage k, in ascending order. The bit criterion above
proves that positions in the short padded tail are zero. -/
noncomputable def stage (k : ℕ) : List ℕ :=
  ((List.range 8192).filter (packed (rows.take k)).testBit).map sumAt

theorem stage_nodup (k : ℕ) : (stage k).Nodup := by
  apply List.Nodup.map (f:=sumAt) (fun x y eq => by dsimp only [sumAt] at eq; omega)
  exact List.nodup_range.filter _

theorem mem_stage (k s : ℕ) : s ∈ stage k ↔ survives k s := by
  rw [stage,List.mem_map,survives_iff]
  simp only [List.mem_filter,List.mem_range]
  constructor
  · rintro ⟨i,⟨_,bit⟩,rfl⟩
    exact ⟨i,bit,rfl⟩
  · rintro ⟨i,bit,rfl⟩
    have range := ((packed_iff _ (fun _ h => List.mem_of_mem_take h) i).mp bit).1
    exact ⟨i,⟨range.trans (by decide),bit⟩,rfl⟩

/-- A three-bit field in the lookup table counts the low four bits. -/
private def nibble (w : ℕ) := (0x8da691691448 >>> (3*(w%16))) % 8

private theorem nibble_eq (w : ℕ) : nibble w = (List.range 4).countP w.testBit := by
  have table : ∀ i : Fin 16, (0x8da691691448 >>> (3*i.val)) % 8 =
      (List.range 4).countP i.val.testBit := by decide +kernel
  rw [nibble,table ⟨w%16,Nat.mod_lt _ (by decide)⟩]
  apply List.countP_congr
  intro i hi
  change (w%2^4).testBit i=true ↔ w.testBit i=true
  rw [Nat.testBit_mod_two_pow]
  simp [List.mem_range.mp hi]

private theorem count_half (m w : ℕ) : (List.range (m+m)).countP w.testBit =
    (List.range m).countP w.testBit + (List.range m).countP (w >>> m).testBit := by
  rw [List.range_add,List.countP_append,List.countP_map]
  congr 1
  apply List.countP_congr
  intro i _
  simp only [Function.comp_apply,Nat.testBit_shiftRight,Nat.add_comm]

/-- Split the index range into two equal parts at each step, keeping the
kernel recursion depth logarithmic. The leaves count bits in one byte. -/
private def pop : ℕ → ℕ → ℕ
  | 0,w => nibble w + nibble (w >>> 4)
  | k+1,w => pop k w + pop k (w >>> (8*2^k))

private theorem pop_eq (k w : ℕ) : pop k w = (List.range (8*2^k)).countP w.testBit := by
  induction k generalizing w with
  | zero =>
    rw [pop,nibble_eq,nibble_eq]
    exact (count_half 4 w).symm
  | succ k ih =>
    rw [pop,ih,ih,show 8*2^(k+1)=8*2^k+8*2^k by ring,count_half]

private theorem stage_length (k : ℕ) : (stage k).length=pop 10 (packed (rows.take k)) := by
  rw [pop_eq,stage,List.length_map,←List.countP_eq_length_filter]
  rfl

/-- The initial size and the exact survivor counts after each prime.
The factor certificate plays no role in these counts. -/
theorem stage_counts : (List.range 14).map (fun k => (stage k).length) =
    [7273,4849,1939,1108,505,271,141,72,38,14,7,6,3,1] := by
  simp only [stage_length]
  decide +kernel

/-- Every factor pair in the public width range must give the unique
surviving sum. This step does not presume primality or use the receipt. -/
theorem forced_sum {p q : ℕ} (prod : p*q=N) (low : 2^19 ≤ p) (low' : 2^19 ≤ q) :
    p+q=1310542 :=
  (through43 _).mp ⟨public_bounds prod low low',
    fun row _ => admissibleSum_of_factor_pair row.1 prod⟩

/-- The public sieve's unique sum identifies the known control.
The published primality certificate is used only in this final check. -/
theorem recovered : survives 13 1310542 ∧
    (1310542-Nat.sqrt (1310542^2-4*N))/2=556559 ∧
    (1310542+Nat.sqrt (1310542^2-4*N))/2=753983 ∧ ExactFactorization N [556559,753983] := by
  have gap : Nat.sqrt (1310542^2-4*N)=197424 := (Nat.eq_sqrt'.mpr (by decide +kernel)).symm
  rw [gap]
  exact ⟨(through43 _).mpr rfl,by decide +kernel,by decide +kernel,SquareDivisorClueWindow.seeded_control.1⟩

end PrimeFactors.PublicSumSieveControl
