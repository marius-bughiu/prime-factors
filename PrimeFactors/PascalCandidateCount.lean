import PrimeFactors.QuotientPascalMasks
import PrimeFactors.WeightedPrimeBudget

/-! Count all full-width primes for which a low ordinary Pascal coefficient
could vanish. Each possible zero belongs to one of the exposed public labels. -/
namespace PrimeFactors.PascalCandidateCount
open Finset

set_option exponentiation.threshold 8192

noncomputable def large (x : ℕ) := x.primeFactors.filter (fun p => 2^1023≤p ∧ p<2^1024)
noncomputable def row (m k : ℕ) := (Ico (2^1023) (2^1024)).filter (fun p => p.Prime ∧ p∣m.choose k)

private theorem member {x p : ℕ} (xp : 0<x) :
    p∈large x ↔ (2^1023≤p ∧ p<2^1024) ∧ p.Prime ∧ p∣x := by
  simp only [large,mem_filter,Nat.mem_primeFactors,xp.ne',not_false_eq_true,and_true]
  have nz : x≠0 := xp.ne'
  tauto

private theorem bits {x : ℕ} (xp : 0<x) :
    1023*(large x).card ≤ x.log2 := by
  have subset : large x ⊆ x.primeFactors := filter_subset _ x.primeFactors
  have total := WeightedPrimeBudget.bit_budget xp subset
  calc _ = ∑ _p∈large x, 1023 := by simp [Nat.mul_comm]
       _ ≤ ∑ p∈large x, p.log2 := sum_le_sum fun p hp =>
         (Nat.le_log2 ((member xp).mp hp).2.1.ne_zero).mpr ((member xp).mp hp).1.1
       _ ≤ x.log2 := total

theorem single_label {x : ℕ} (xp : 0<x) (ht : x<2^2048) : (large x).card≤2 := by
  have h := bits xp
  have l := (Nat.log2_lt xp.ne').mpr ht
  omega

/-- The public AP can use any start and stride; only positivity and
the stated height bound on its actual terms enter the count. -/
theorem labels_bound {I : Type*} (S : Finset I) (term : I→ℕ)
    (valid : ∀ i∈S, 0<term i ∧ term i<2^2048) :
    (S.biUnion (fun i => large (term i))).card≤2*S.card := by
  have c := card_biUnion_le_card_mul S (fun i => large (term i)) 2
    (fun i hi => single_label (valid i hi).1 (valid i hi).2)
  simpa only [mul_comm] using c

/-- A full-width prime divides the coefficient exactly when it divides
one of the k positive integers m-k+1 through m. -/
theorem row_labels {m k : ℕ} (km : k≤m) (short : k<2^1023) :
    row m k=(range k).biUnion (fun j => large (m-k+1+j)) := by
  ext p
  simp only [row,mem_filter,mem_Ico,mem_biUnion,mem_range]
  constructor
  · rintro ⟨⟨lo,hi⟩,pr,hit⟩
    have root := (QuotientPascalMasks.low_column pr (short.trans_le lo)).mp hit
    refine ⟨k-1-m%p,by omega,(member (by omega)).mpr ⟨⟨lo,hi⟩,pr,?_⟩⟩
    have eq := Nat.mod_add_div m p
    exact ⟨m/p,by omega⟩
  · rintro ⟨j,jk,h⟩
    obtain ⟨width,pr,⟨a,eq⟩⟩ := (member (by omega)).mp h
    have id : m=p*a+(k-1-j) := by omega
    have root : m%p<k := by rw [id,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt (by omega)]; omega
    exact ⟨width,pr,(QuotientPascalMasks.low_column pr (short.trans_le width.1)).mpr root⟩

/-- A coefficient with k>m is zero and has gcd N for any positive N. -/
theorem zero_column {m k : ℕ} (lt : m<k) (n : ℕ) : (m.choose k).gcd n=n := by
  simp [Nat.choose_eq_zero_of_lt lt]

theorem row_bound {m k n : ℕ} (km : k≤m) (short : k<2^1023)
    (height : m<n) (cap : n≤2^2048) : (row m k).card≤2*k := by
  rw [row_labels km short]
  simpa using labels_bound (range k) (fun j => m-k+1+j) (by
    intro j hj
    have := mem_range.mp hj
    dsimp
    omega)

/-- Along any realized transcript, the union bound charges the sum of
the chosen low column indices. The choices can depend on earlier results. -/
theorem transcript {I : Type*} (S : Finset I) (m k : I→ℕ) {n : ℕ} (cap : n≤2^2048)
    (valid : ∀ i∈S, k i≤m i ∧ k i<2^1023 ∧ m i<n) :
    (S.biUnion (fun i => row (m i) (k i))).card ≤ 2*∑ i∈S, k i := by
  apply card_biUnion_le.trans
  rw [mul_sum]
  exact sum_le_sum fun i hi =>
    row_bound (valid i hi).1 (valid i hi).2.1 (valid i hi).2.2 cap

/-- If the exposed integer has a public divisor 4≤r<2^1023, its remaining
cofactor is too small for two candidate primes. -/
theorem small_divisor {x r : ℕ} (xp : 0<x) (ht : x<2^2048)
    (four : 4≤r) (small : r<2^1023) (div : r∣x) : (large x).card≤1 := by
  let y := x/r
  have prod : r*y=x := Nat.mul_div_cancel' div
  have yp : 0<y := Nat.pos_of_ne_zero (fun z => by rw [z,mul_zero] at prod; omega)
  have size : y<2^2046 := by
    have h := Nat.mul_le_mul_right y four
    rw [prod] at h
    have cap : 4*2^2046=2^2048 := by norm_num
    omega
  have sub : large x⊆large y := by
    intro p inx
    obtain ⟨width,prime,dx⟩ := (member xp).mp inx
    rw [←prod] at dx
    have skip : ¬p∣r := Nat.not_dvd_of_pos_of_lt (by omega) (small.trans_le width.1)
    exact (member yp).mpr ⟨width,prime,(prime.dvd_mul.mp dx).resolve_left skip⟩
  have c := card_le_card sub
  have h := bits yp
  have b := (Nat.log2_lt yp.ne').mpr size
  omega

def charge (x : ℕ) := if x.gcd 60≤3 then 2 else 1

theorem charge_bound {x : ℕ} (xp : 0<x) (ht : x<2^2048) : (large x).card≤charge x := by
  unfold charge
  split
  · exact single_label xp ht
  · apply small_divisor xp ht (r:=x.gcd 60) (by omega) _ (Nat.gcd_dvd_left _ _)
    exact (Nat.le_of_dvd (by decide) (Nat.gcd_dvd_right x 60)).trans_lt (by decide +kernel)

private theorem complete_period (a : ℕ) : ∑ j∈range 60, charge (a+j)=92 := by
  have table : ∀ s : Fin 60, ∑ j∈range 60, charge ((s:ℕ)+j)=92 := by decide +kernel
  calc _ = ∑ j∈range 60, charge (a%60+j) := by
         apply sum_congr rfl
         intro j _
         unfold charge
         rw [((Nat.mod_modEq a 60).symm.add_right j).gcd_eq]
       _ = _ := table ⟨_,Nat.mod_lt _ (by decide)⟩

/-- A complete period of sixty positive consecutive labels can implicate
at most 92 distinct full-width primes. This counts a partial period at
two per label and includes every starting phase. -/
theorem consecutive {a k : ℕ} (valid : ∀ j<k,0<a+j ∧ a+j<2^2048) :
    ((range k).biUnion (fun j => large (a+j))).card≤92*(k/60)+2*(k%60) := by
  have full (b : ℕ) : ∑ j∈range (60*b), charge (a+j)=92*b := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [Nat.mul_succ,sum_range_add,ih,Nat.mul_succ]
      simpa only [←Nat.add_assoc] using congrArg (fun x => 92*b+x) (complete_period (a+60*b))
  have cap (c t : ℕ) : ∑ j∈range t, charge (c+j)≤2*t := by
    calc _ ≤ ∑ _j∈range t, 2 := sum_le_sum (fun i _ => by unfold charge; split <;> decide)
         _ = _ := by simp [Nat.mul_comm]
  apply card_biUnion_le.trans
  apply (sum_le_sum (fun j hj => charge_bound (valid j (mem_range.mp hj)).1 (valid j (mem_range.mp hj)).2)).trans
  have split : k = 60*(k/60)+k%60 := by omega
  conv_lhs => rw [split,sum_range_add,full]
  exact Nat.add_le_add_left (by simpa only [←Nat.add_assoc] using cap (a+60*(k/60)) (k%60)) _

theorem wheel_row {m k n : ℕ} (km : k≤m) (short : k<2^1023)
    (height : m<n) (cap : n≤2^2048) : (row m k).card≤92*(k/60)+2*(k%60) := by
  rw [row_labels km short]
  exact consecutive (fun j hj => ⟨by omega,by omega⟩)

theorem wheel_transcript {I : Type*} (S : Finset I) (m k : I→ℕ) {n : ℕ} (cap : n≤2^2048)
    (valid : ∀ i∈S, k i≤m i ∧ k i<2^1023 ∧ m i<n) :
    (S.biUnion (fun i => row (m i) (k i))).card ≤ ∑ i∈S, (92*(k i/60)+2*(k i%60)) := by
  exact card_biUnion_le.trans (sum_le_sum fun i hi =>
    wheel_row (valid i hi).1 (valid i hi).2.1 (valid i hi).2.2 cap)

end PrimeFactors.PascalCandidateCount
