import PrimeFactors.FractionalNonunitPrefix
import PrimeFactors.BitMarginals
import Mathlib.Tactic.NormNum.Prime

/-! Adjacent counts of nonunits at dyadic cutoffs encode a column of the two
binary factors. This file classifies the possible completions of one missing
interior count using its two neighbors, and gives balanced prime examples
where a second completion really occurs. -/

namespace PrimeFactors.DyadicNonunitReadings

open Finset

/-- The measured count at the cutoff floor(N/2^j). -/
noncomputable def reading (n j : ℕ) := FractionalNonunitPrefix.prefixCount n (2^j)

/-- The sum of the two remaining binary words after removing j low bits. -/
def level (a b j : ℕ) := a/2^j+b/2^j

theorem reading_eq {p q j : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q) (pos : 0<j) :
    reading (p*q) j=level p q j :=
  FractionalNonunitPrefix.quotient_sum hp hq diff (Nat.one_lt_pow (by omega) (by decide))

private theorem halves (x j : ℕ) :
    x/2^j=2*(x/2^(j+1))+(x.testBit j).toNat := by
  rw [Nat.toNat_testBit,pow_succ,←Nat.div_div_eq_div_mul]
  have := Nat.mod_add_div (x/2^j) 2
  omega

/-- A difference of two actual public counts is precisely the binary column
sum also obtained from the accepted factor orientations in BitMarginals. -/
theorem column {p q j : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q) (pos : 0<j) :
    reading (p*q) j=2*reading (p*q) (j+1)+(p.testBit j).toNat+(q.testBit j).toNat := by
  rw [reading_eq hp hq diff pos,reading_eq hp hq diff (by omega),level,level]
  have a := halves p j
  have b := halves q j
  omega

/-- The integer difference equals the same digit count delivered by the
two orientations of the accepted factor box. -/
theorem column_eq_bitMarginal {p q B j : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ordered : p < q) (inside : q < B) (upper : B ≤ p*q) (pos : 0 < j) :
    reading (p*q) j-2*reading (p*q) (j+1)=(bitMarginal (p*q) B j).val := by
  rw [bitMarginal_val_semiprime hp hq ordered inside upper]
  have := column hp hq ordered.ne pos
  omega

/-- Counts at level zero would include N itself. The first actual dyadic
count already determines the sum of any two distinct odd primes. -/
theorem first_reading {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q)
    (op : p≠2) (oq : q≠2) : 2*reading (p*q) 1+2=p+q := by
  rw [reading_eq hp hq diff (by decide),level,pow_one]
  obtain ⟨a,pa⟩ := hp.odd_of_ne_two op
  obtain ⟨b,qb⟩ := hq.odd_of_ne_two oq
  omega

/-- Possible offsets of the missing middle count above twice its last
neighbor. Its two adjacent binary columns must each contribute 0, 1 or 2. -/
noncomputable def choices (d : ℕ) := (range 3).filter fun v => 2*v≤d ∧ d≤2*v+2

/-- The seven possible two-column totals and their exact middle-count offsets. -/
theorem table :
    (List.range 7).map choices = [{0},{0},{0,1},{1},{1,2},{2},{2}] := by decide +kernel

theorem choice_count {d : ℕ} (bound : d≤6) :
    (choices d).card = if d=2 ∨ d=4 then 2 else 1 := by
  interval_cases d <;> decide

/-- The range conditions are complete for arbitrary binary words. For every
listed offset, actual words realize both endpoint counts and the chosen middle
count. No primality or fixed product is assumed in this converse. -/
theorem choices_iff (b d v : ℕ) :
    v∈choices d ↔ ∃ x y : ℕ, x+y=4*b+d ∧ x/2+y/2=2*b+v ∧ x/4+y/4=b := by
  simp only [choices,mem_filter,mem_range]
  constructor
  · rintro ⟨vsmall,lo,hi⟩
    let a := d-2*v
    have asmall : a≤2 := by dsimp [a]; omega
    refine ⟨4*b+2*min 1 v+min 1 a,2*(v-min 1 v)+(a-min 1 a),?_⟩
    dsimp only [a] at *
    omega
  · rintro ⟨x,y,sum,mid,last⟩
    omega

private theorem column_bound {p q j : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q) (pos : 0<j) :
    2*reading (p*q) (j+1)≤reading (p*q) j ∧ reading (p*q) j≤2*reading (p*q) (j+1)+2 := by
  rw [column hp hq diff pos]
  cases p.testBit j <;> cases q.testBit j <;> simp +arith

/-- At a deleted interior position, subtract four times the last neighbor
from the first. The table contains the exact observed offset. -/
theorem missing_middle {p q j : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q) (pos : 0<j) :
    let a := reading (p*q) j
    let b := reading (p*q) (j+2)
    let c := reading (p*q) (j+1)
    4*b≤a ∧ a-4*b≤6 ∧ c-2*b∈choices (a-4*b) ∧ c=2*b+(c-2*b) := by
  have h := column_bound hp hq diff pos
  have g := column_bound hp hq diff (by omega : 0<j+1)
  rw [show j+1+1=j+2 by omega] at g
  dsimp only
  simp only [choices,mem_filter,mem_range]
  omega

/-- A single parity bit for the next count suffices even when only the
preceding count is available. -/
def repair (previous parity : ℕ) : ℕ :=
  if previous/2%2=parity then previous/2 else previous/2-1

theorem parity_repair {p q j : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q) (pos : 0<j) :
    repair (reading (p*q) j) (reading (p*q) (j+1)%2)=reading (p*q) (j+1) := by
  have h := column_bound hp hq diff pos
  unfold repair
  split_ifs <;> omega

private theorem level_zero {a b j : ℕ} (ha : a<2^j) (hb : b<2^j) : level a b j=0 := by
  rw [level,Nat.div_eq_of_lt ha,Nat.div_eq_of_lt hb,zero_add]

/-- Both local ambiguities occur in actual balanced prime transcripts.
The two product pairs differ, but each pair of products agrees modulo
2 raised to one more than the erased index. -/
theorem prime_examples :
    (∀ j, 0<j → j≠3 → reading (67*107) j=reading (71*103) j) ∧
    reading (67*107) 3=21 ∧ reading (71*103) 3=20 ∧
    reading (67*107) 2-4*reading (67*107) 4=2 ∧ (67*107)%16=(71*103)%16 ∧
    (∀ j, 0<j → j≠4 → reading (139*191) j=reading (151*179) j) ∧
    reading (139*191) 4=19 ∧ reading (151*179) 4=20 ∧
    reading (139*191) 3-4*reading (139*191) 5=4 ∧ (139*191)%32=(151*179)%32 := by
  have a {j : ℕ} (pos : 0<j) : reading (67*107) j=level 67 107 j :=
    reading_eq (by norm_num) (by norm_num) (by decide) pos
  have b {j : ℕ} (pos : 0<j) : reading (71*103) j=level 71 103 j :=
    reading_eq (by norm_num) (by norm_num) (by decide) pos
  have c {j : ℕ} (pos : 0<j) : reading (139*191) j=level 139 191 j :=
    reading_eq (by norm_num) (by norm_num) (by decide) pos
  have d {j : ℕ} (pos : 0<j) : reading (151*179) j=level 151 179 j :=
    reading_eq (by norm_num) (by norm_num) (by decide) pos
  refine ⟨?_,by rw [a (by decide)]; decide,by rw [b (by decide)]; decide,
    by rw [a (by decide),a (by decide)]; decide,by decide,?_,
    by rw [c (by decide)]; decide,by rw [d (by decide)]; decide,
    by rw [c (by decide),c (by decide)]; decide,by decide⟩
  · intro j pos ne
    rw [a pos,b pos]
    by_cases short : j<7
    · interval_cases j <;> first | contradiction | decide
    · have cap := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 7≤j)
      rw [level_zero (by omega) (by omega),level_zero (by omega) (by omega)]
  · intro j pos ne
    rw [c pos,d pos]
    by_cases short : j<8
    · interval_cases j <;> first | contradiction | decide
    · have cap := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 8≤j)
      rw [level_zero (by omega) (by omega),level_zero (by omega) (by omega)]

end PrimeFactors.DyadicNonunitReadings
