import PrimeFactors.UniversalSumStride
import PrimeFactors.CyclotomicRadixLift
import PrimeFactors.ChebyshevQuarticScale

/-! A necessary budget for one specific type of decoder: isolate at most one admissible
trace in every translate of a digit progression, using a fixed local modulus. The modulus
may depend on the public input and the digit. The starting trace in the collision is
existential; this yields no lower bound for a decoder that uses the actual starting trace. -/
namespace PrimeFactors.UniversalPackingBudget
open CyclotomicRadixLift FactorSumSpacing
set_option exponentiation.threshold 4096

/-- A digit samples one residue of the index modulo this exact period. -/
def period (g M : ℕ) := M/(M.gcd g)

/-- First positive index separation whose corresponding trace displacement is a
multiple of 20160. This limits each universal uniqueness statement for a fixed step. -/
def repeatAfter (step : ℕ) := 20160/(Nat.gcd 20160 step)

def UniformWindow (n : ℤ) (m step count : ℕ) : Prop :=
  ∀ a : ZMod m, ∀ i j : Fin count,
    AdmissibleSum (n : ZMod m) (a+(step : ZMod m)*(i.val : ZMod m)) →
    AdmissibleSum (n : ZMod m) (a+(step : ZMod m)*(j.val : ZMod m)) → i=j

/-- Reversing the sign of every factor leaves its product unchanged. Thus uniformity
over translated increasing progressions is equivalent to uniformity over the
decreasing progressions used by the cyclotomic sum decoder. -/
theorem descending_iff (n : ℤ) (m step count : ℕ) : UniformWindow n m step count ↔
    ∀ a : ZMod m, ∀ i j : Fin count,
      AdmissibleSum (n : ZMod m) (a-(step : ZMod m)*(i.val : ZMod m)) →
      AdmissibleSum (n : ZMod m) (a-(step : ZMod m)*(j.val : ZMod m)) → i=j := by
  have neg {s : ZMod m} (h : AdmissibleSum (n : ZMod m) s) : AdmissibleSum (n : ZMod m) (-s) := by
    obtain ⟨x,y,prod,rfl⟩ := h
    exact ⟨-x,-y,by simpa only [neg_mul_neg] using prod,by ring⟩
  have flip (a x : ZMod m) : -a+x=-(a-x) := by ring
  constructor
  · intro h a i j ai aj
    exact h (-a) i j (by rw [flip]; exact neg ai) (by rw [flip]; exact neg aj)
  · intro h a i j ai aj
    exact h (-a) i j (by simpa only [neg_add_rev,sub_eq_add_neg,add_comm] using neg ai)
      (by simpa only [neg_add_rev,sub_eq_add_neg,add_comm] using neg aj)

private theorem lcm_eq (a b : ℕ) : a.lcm b=a*(b/(b.gcd a)) := by
  rw [Nat.lcm,Nat.gcd_comm,Nat.mul_div_assoc _ (Nat.gcd_dvd_left ..)]

private theorem mul_period {a : ℕ} (pos : 0<a) (b i : ℕ) : a∣b*i ↔ period b a∣i := by
  constructor
  · intro d
    have z : b*i ≡ b*0 [MOD a] := by simpa only [Nat.mul_zero] using Nat.modEq_zero_iff_dvd.mpr d
    exact Nat.modEq_zero_iff_dvd.mp (z.cancel_left_div_gcd pos)
  · rintro ⟨j,rfl⟩
    have dv : a∣b*period b a := by rw [show b*period b a=b.lcm a from (lcm_eq ..).symm]; exact Nat.dvd_lcm_right ..
    exact Nat.mul_assoc .. ▸ dvd_mul_of_dvd_left dv j

/-- The equal cyclotomic digit bins are exactly the classes of this index period. -/
theorem same_digit {M : ℕ} (pos : 0<M) (g start d : ℕ) :
    g*start ≡ g*(start+d) [MOD M] ↔ period g M∣d := by
  rw [←mul_period pos g d,Nat.mul_add]
  constructor
  · intro h
    have z := Nat.ModEq.add_left_cancel' (g*start)
      (show g*start+0 ≡ g*start+g*d [MOD M] by simpa only [Nat.add_zero] using h)
    exact Nat.modEq_zero_iff_dvd.mp z.symm
  · intro dv
    simpa only [Nat.add_zero] using (Nat.modEq_zero_iff_dvd.mpr dv).symm.add_left (g*start)

/-- Precisely the multiples of K are guaranteed collisions for every product and
modulus simultaneously; the starting trace can depend on the chosen modulus. -/
theorem recurrent_iff (step i : ℕ) :
    (∀ (n : ℤ) (m : ℕ), 0<m → Gap m n (((step*i:ℕ):ℤ) : ZMod m)) ↔ repeatAfter step∣i := by
  rw [UniversalSumStride.universal_iff]
  exact (show ((20160:ℤ)∣((step*i:ℕ):ℤ)) ↔ (20160:ℕ)∣step*i by exact_mod_cast Iff.rfl).trans
    (mul_period (by decide : 0<20160) step i)

theorem window_limit {n : ℤ} {m step count : ℕ} (mp : 0<m)
    (unique : UniformWindow n m step count) : count≤repeatAfter step := by
  let K := repeatAfter step
  have kp : 0<K := Nat.div_pos (Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left 20160 step))
    (Nat.gcd_pos_of_pos_left step (by decide))
  have divides : 20160∣step*K := by
    rw [show step*K=step.lcm 20160 from (lcm_eq ..).symm]
    exact Nat.dvd_lcm_right ..
  have signed : (20160:ℤ)∣((step*K : ℕ):ℤ) := by exact_mod_cast divides
  obtain ⟨a,l,r⟩ := UniversalSumStride.all_moduli n ((step*K:ℕ):ℤ) signed m mp
  by_contra! short
  let i : Fin count := ⟨0,by omega⟩
  let j : Fin count := ⟨K,short⟩
  have neq := unique a i j (by simpa only [i,Nat.cast_zero,mul_zero,add_zero] using l)
    (by simpa only [j,Int.cast_natCast,Nat.cast_mul,Int.cast_mul] using r)
  have := congrArg Fin.val neq
  change 0=K at this
  omega

/-- Ceiling division for positive divisors, with exact endpoint rounding. -/
def ceilDiv (a b : ℕ) := (a+b-1)/b

theorem ceil_iff {a b c : ℕ} (bp : 0<b) : ceilDiv a b≤c ↔ a≤b*c := by
  rw [ceilDiv,←Nat.lt_succ_iff,Nat.div_lt_iff_lt_mul bp,Nat.succ_mul,Nat.mul_comm c b]
  omega

/-- If C consecutive indices are divided among P residue classes, the class of the
first index contains ceil(C/P) terms. Their offsets are 0,P,2P,... . -/
theorem first_bin {C P i : ℕ} (positive : 0<P) : i<ceilDiv C P ↔ P*i<C := by
  rw [←not_le,ceil_iff positive,not_le]

private theorem weight_dvd (N : ℕ) : (weight N)∣10080 := by
  rcases weights N with h|h|h|h <;> rw [h] <;> decide

private theorem stride_dvd (N : ℕ) : (stride N)∣20160 := by
  have d := Nat.mul_dvd_mul_left 2 (weight_dvd N)
  exact d

private theorem stride_pos (N : ℕ) : 0<stride N := by
  unfold stride
  rcases weights N with h|h|h|h <;> rw [h] <;> decide

private theorem ppos {g M : ℕ} (mp : 0<M) : 0<period g M := by
  apply Nat.div_pos (Nat.le_of_dvd mp (Nat.gcd_dvd_left ..)) (Nat.gcd_pos_of_pos_left _ mp)

/-- Total capacity of P bins of length K. The factor weight and repeat period cancel,
leaving exactly the stated ratio of M to gcd(M,10080). -/
theorem capacity (N M : ℕ) :
    let W := stride N
    let P := period (weight N) M
    P*repeatAfter (W*P)=(20160/W)*(M/(M.gcd 10080)) := by
  let g := weight N
  let W := stride N
  let P := period g M
  have step : W*P=2*(g.lcm M) := by
    change (2*g)*(M/(M.gcd g))=2*(g.lcm M)
    rw [lcm_eq,Nat.mul_assoc]
  have nested : (g.lcm M).lcm 10080=M.lcm 10080 := by
    change (g.lcm M).lcm 10080=M.lcm 10080
    have h := Nat.dvd_antisymm (Nat.lcm_dvd (weight_dvd N) (dvd_refl 10080)) (Nat.dvd_lcm_right g 10080)
    rw [Nat.lcm_comm g M,Nat.lcm_assoc,h]
  have total : (W*P)*repeatAfter (W*P)=2*(10080*(M/(M.gcd 10080))) := calc
    _ = (W*P).lcm 20160 := (lcm_eq ..).symm
    _ = (2*(g.lcm M)).lcm (2*10080) := by rw [step]
    _ = 2*((g.lcm M).lcm 10080) := Nat.lcm_mul_left
    _ = _ := by rw [nested,Nat.lcm_comm M 10080,lcm_eq]
  apply Nat.mul_left_cancel (n:=W) (stride_pos N)
  change W*(P*repeatAfter (W*P))=W*((20160/W)*(M/(M.gcd 10080)))
  rw [←Nat.mul_assoc,←Nat.mul_assoc,Nat.mul_div_cancel' (stride_dvd N),total]
  ring

/-- Number of digit classes required by a uniform argument, for a given M. The
largest bin contains the first progression index; it may start anywhere modulo m. -/
theorem bins_needed {n : ℤ} {m W g M C : ℕ} (mp : 0<m) (radix : 0<M)
    (unique : UniformWindow n m (W*period g M) (ceilDiv C (period g M))) :
    ceilDiv C (repeatAfter (W*period g M))≤period g M := by
  have limit := window_limit mp unique
  have width := (ceil_iff (ppos radix)).mp limit
  apply (ceil_iff ?_).mpr (by rwa [Nat.mul_comm])
  exact Nat.div_pos (Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left ..)) (Nat.gcd_pos_of_pos_left _ (by decide))

/-- Necessary effective radix for a uniformly unique bin at this product. -/
theorem radix_needed {N m M C : ℕ} (mp : 0<m) (radix : 0<M)
    (unique : UniformWindow N m (stride N*period (weight N) M) (ceilDiv C (period (weight N) M))) :
    ceilDiv C (20160/stride N)≤M/(M.gcd 10080) := by
  have l := window_limit mp unique
  have c := (ceil_iff (ppos radix)).mp l
  rw [capacity] at c
  exact (ceil_iff (Nat.div_pos (Nat.le_of_dvd (by decide) (stride_dvd N)) (stride_pos N))).mpr c

/-- The single-digit radix from the direct decoder has a squared modulus less than
2^25 times the square of any radix meeting this budget. Both radices are positive. -/
theorem uniform_comparison {N C M : ℕ} (mp : 0<M)
    (needed : ceilDiv C (20160/stride N)≤M/(M.gcd 10080)) :
    (radix N C)^2<2^25*M^2 := by
  have width := (ceil_iff (Nat.div_pos (Nat.le_of_dvd (by decide) (stride_dvd N)) (stride_pos N))).mp needed
  have short : 20160/stride N≤5040 := by
    unfold stride
    rcases weights N with h|h|h|h <;> rw [h] <;> decide
  have c := width.trans (Nat.mul_le_mul short (Nat.div_le_self M _))
  have fit := (radix_spec N C).2.1
  have bound : radix N C≤5043*M := by omega
  calc _ ≤ (5043*M)^2 := Nat.pow_le_pow_left bound 2
       _ = 5043^2*M^2 := by ring
       _ < _ := Nat.mul_lt_mul_of_pos_right (by decide : 5043^2<2^25) (pow_pos mp 2)

/-- The only inputs to the two population bounds below are the public product and
the common lower endpoint for its prime factors. -/
def positions (N A : ℕ) :=
  choices N (stride N) (ProductDeficitBand.lower N A) (ProductDeficitBand.upper N A)

/-- This tests only whether the radix satisfies the necessary capacity inequality. -/
def Fits (q M : ℕ) : Prop := q≤M/(M.gcd 10080)

def ThreeSkips (q : ℕ) : Prop :=
  ¬Fits q q ∧ ¬Fits q (q+1) ∧ ¬Fits q (q+2) ∧ Fits q (q+3)

theorem least_after_three {q : ℕ} (test : ThreeSkips q) :
    Fits q (q+3) ∧ ∀ M, Fits q M → q+3≤M := by
  obtain ⟨a,b,c,good⟩ := test
  refine ⟨good,fun M fits => ?_⟩
  have start := (show q≤M/(M.gcd 10080) from fits).trans (Nat.div_le_self ..)
  by_contra! bad
  rcases (by omega : M=q ∨ M=q+1 ∨ M=q+2) with rfl|rfl|rfl
  · exact a fits
  · exact b fits
  · exact c fits

/-- The exact number of bits in a positive integer, expressed by its endpoints. -/
def Bits (v b : ℕ) : Prop := 2^(b-1)≤v ∧ v<2^b

/-- Bit lengths for the initial count, smallest arithmetically feasible radix and
its squared modulus. The last length prices the previous direct decoder. -/
def Report (N W Cbits Mbits precision direct : ℕ) : Prop :=
  let C := positions N (2^1023)
  let q := ceilDiv C (20160/stride N)
  let P := period (weight N) (q+3)
  stride N=W ∧ Bits C Cbits ∧ ThreeSkips q ∧
    Bits (q+3) Mbits ∧ Bits ((q+3)^2) precision ∧ Bits ((radix N C)^2) direct ∧
    repeatAfter (W*P)=20160/W ∧ ceilDiv C P=20160/W

private theorem ceil_sqrt_check {N r : ℕ} (below : (r-1)^2<N) (above : N≤r^2) : ceilSqrt N=r := by
  have hi := ceilSqrt_le_iff.mpr above
  by_contra! ne
  have small := ceilSqrt_le_iff.mp (show ceilSqrt N≤r-1 by omega)
  omega

theorem fresh_report : Report ChebyshevQuarticScale.fresh 8 1015 1004 2008 2030 := by
  let r : ℕ := 158327039176966334715448284019718823474497913662177975160442996009439310669941017429676080400185006424773254142252582891257193029659269227070095120289800339855421063931472090621260003180611046788905349147963313017385074143012442899089952314244753217806428276920663827209779196401916113023989449483782760844630
  have sr : ceilSqrt ChebyshevQuarticScale.fresh=r :=
    ceil_sqrt_check (by decide +kernel) (by decide +kernel)
  unfold Report positions ProductDeficitBand.lower
  rw [sr]
  unfold ThreeSkips Fits Bits
  decide +kernel

theorem crossed_report : Report ChebyshevQuarticScale.crossed 4 1018 1006 2012 2036 := by
  let r : ℕ := 135037911685235586269825030135549325391376915966798636179319977077209993450011760943044181307768476527897818717675959823440307553022185653953812606479930673789391793187765141283074720630433120513417190939648203494531748575804685158519937612233285802863014656458801051235008057526662884995918450838938076904615
  have sr : ceilSqrt ChebyshevQuarticScale.crossed=r :=
    ceil_sqrt_check (by decide +kernel) (by decide +kernel)
  unfold Report positions ProductDeficitBand.lower
  rw [sr]
  unfold ThreeSkips Fits Bits
  decide +kernel

end PrimeFactors.UniversalPackingBudget
