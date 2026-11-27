import PrimeFactors.UniversalPackingBudget
import PrimeFactors.FactorSumCRT
import PrimeFactors.WeightedPrimeBins
import PrimeFactors.GeometricWheelBlocks
import PrimeFactors.CyclotomicDigitPeriod
import PrimeFactors.TrueTraceTableCost

/-! Count locally admissible sum candidates in the digit bin that is actually
selected. Full periods contribute their exact number of accepting residues;
the tail can be counted too. The sieve modulus can depend on the supplied digit. -/
namespace PrimeFactors.ActualDigitMultiplicity
open Finset CyclotomicRadixLift UniversalPackingBudget
open GeometricWheelBlocks (laneLength index_lt)
set_option exponentiation.threshold 4096

private theorem period_pos {m : ℕ} (pos : 0<m) (step : ℕ) : 0<period step m :=
  Nat.div_pos (Nat.le_of_dvd pos (Nat.gcd_dvd_left ..)) (Nat.gcd_pos_of_pos_left _ pos)

private theorem period_dvd (m step : ℕ) : m∣step*period step m := by
  obtain ⟨u,eq⟩ := Nat.gcd_dvd_right m step
  have cancel : m.gcd step*period step m=m := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  exact ⟨u,by calc
    _ = (m.gcd step*u)*period step m := congrArg (·*period step m) eq
    _ = ((m.gcd step)*period step m)*u := by ring
    _ = m*u := by rw [cancel]⟩

private theorem reduce_step (m step j : ℕ) :
    (step:ZMod m)*((j%period step m:ℕ):ZMod m)=(step:ZMod m)*(j:ZMod m) := by
  let Q := period step m
  have kill : (step:ZMod m)*(Q:ZMod m)=0 := by
    rw [←Nat.cast_mul]
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr (period_dvd m step)
  have h := congrArg (fun x : ℕ => (x:ZMod m)) (Nat.div_add_mod j Q)
  simp only [Nat.cast_add,Nat.cast_mul] at h
  change (step:ZMod m)*((j%Q:ℕ):ZMod m)=_
  rw [←h,mul_add,←mul_assoc,kill,zero_mul,zero_add]

/-- Indices in a particular bin which have locally compatible factor sums. -/
noncomputable def hits {m : ℕ} (n a : ZMod m) (step L : ℕ) : Finset ℕ := by
  classical exact (range L).filter fun j => AdmissibleSum n (a-(step:ZMod m)*(j:ZMod m))

theorem mem_hits {m j step L : ℕ} {n a : ZMod m} :
    j∈hits n a step L ↔ j<L ∧ AdmissibleSum n (a-(step:ZMod m)*(j:ZMod m)) := by
  classical simp only [hits,mem_filter,mem_range]

/-- The exact result for this starting residue counts every full orbit and
then the prefix of the final orbit. No uniformity across other starts is assumed. -/
theorem exact_count {m : ℕ} (mp : 0<m) (n a : ZMod m) (step L : ℕ) :
    let Q := period step m
    let R := hits n a step Q
    (hits n a step L).card = (L/Q)*R.card + (R.filter (· < L%Q)).card := by
  classical
  let Q := period step m
  let R := hits n a step Q
  have qp : 0<Q := period_pos mp step
  have sub : R⊆range Q := fun j hj => mem_range.mpr (mem_hits.mp hj).1
  have eq : hits n a step L=(range L).filter (fun j => j%Q∈R) := by
    ext j
    simp only [mem_hits,mem_filter,mem_range,R,Q,mem_hits,reduce_step,
      Nat.mod_lt _ qp,true_and]
  rw [eq]
  exact WeightedPrimeBins.prefix_exact qp R sub L

/-- An occupied bin receives at least one candidate from every full local orbit. -/
theorem occupied {m : ℕ} (mp : 0<m) {n a : ZMod m} {step L : ℕ}
    (hit : (hits n a step L).Nonempty) : L/period step m ≤ (hits n a step L).card := by
  let Q := period step m
  obtain ⟨i,hi⟩ := hit
  have inp : i%Q∈hits n a step Q := mem_hits.mpr
    ⟨Nat.mod_lt _ (period_pos mp _),by simpa only [Q,reduce_step] using (mem_hits.mp hi).2⟩
  have positive := card_pos.mpr (show (hits n a step Q).Nonempty from ⟨_,inp⟩)
  have count := exact_count mp n a step L
  change (hits n a step L).card=(L/Q)*(hits n a step Q).card+_ at count
  unfold Q at *
  rw [count]
  exact (Nat.le_mul_of_pos_right _ positive).trans (Nat.le_add_right ..)

def start (N A : ℕ) := bottom N (stride N) (ProductDeficitBand.upper N A)

/-- The bin for a canonical relative index residue r < P. Its first sum is determined by
the public start of the actual interval and the selected digit residue. -/
noncomputable def bin (N A M m r : ℕ) : Finset ℕ :=
  let P := period (weight N) M
  let W := stride N
  hits (N:ZMod m) ((N:ZMod m)+1-(W:ZMod m)*(start N A+r:ℕ)) (W*P)
    (laneLength P (positions N A) r)

theorem lower_in_bin {N A M m r : ℕ} (mp : 0<m)
    (nonempty : (bin N A M m r).Nonempty) :
    let P := period (weight N) M
    let Q := period (stride N*P) m
    positions N A/(P*Q) ≤ (bin N A M m r).card := by
  let P := period (weight N) M
  let Q := period (stride N*P) m
  have lower : positions N A/P≤laneLength P (positions N A) r := by unfold laneLength; omega
  change positions N A/(P*Q)≤_
  rw [←Nat.div_div_eq_div_mul]
  exact (Nat.div_le_div_right lower).trans (occupied mp nonempty)

/-- Recover the natural candidate sum at a retained position. -/
def candidate (N A M r j : ℕ) :=
  N+1-stride N*(start N A+r+period (weight N) M*j)

/-- Every counted position gives a physical sum within the stated bounds. -/
theorem physical {N A M m r j : ℕ} (rl : r<period (weight N) M)
    (low : ProductDeficitBand.lower N A≤N) (high : ProductDeficitBand.upper N A≤N)
    (hit : j∈bin N A M m r) : let S := candidate N A M r j
    ProductDeficitBand.lower N A < S ∧ S ≤ ProductDeficitBand.upper N A ∧
      AdmissibleSum (N:ZMod m) (S:ZMod m) := by
  let L := ProductDeficitBand.lower N A
  let H := ProductDeficitBand.upper N A
  let B := start N A
  let W := stride N
  let P := period (weight N) M
  let x := B+r+P*j
  have wp : 0<W := by dsimp [W,stride]; rcases weights N with e|e|e|e <;> omega
  obtain ⟨jl,ok⟩ := mem_hits.mp hit
  have before := (index_lt rl (positions N A) j).mpr jl
  change r+P*j < (N-L)/W+1-B at before
  have xu : x≤(N-L)/W := by dsimp [x]; omega
  have prod : W*x≤N-L := by simpa only [mul_comm x W] using (Nat.le_div_iff_mul_le wp).mp xu
  have bottomEq : B=(N-H)/W+1 := by
    change (N+W-H)/W=_
    rw [show N+W-H=(N-H)+W by omega,Nat.add_div_right _ wp]
  have xl : (N-H)/W<x := by dsimp only [x]; omega
  have past := (Nat.div_lt_iff_lt_mul wp).mp xl
  rw [Nat.mul_comm x W] at past
  have bound : W*x≤N+1 := by omega
  change L<N+1-W*x ∧ N+1-W*x≤H ∧ _
  refine ⟨by omega,by omega,?_⟩
  change AdmissibleSum (N:ZMod m) ((N+1-W*x:ℕ):ZMod m)
  change AdmissibleSum (N:ZMod m) ((N:ZMod m)+1-(W:ZMod m)*(B+r:ℕ)-(W*P:ℕ)*(j:ZMod m)) at ok
  convert ok using 1
  rw [Nat.cast_sub bound]
  dsimp only [x]
  push_cast
  ring

/-- Distinct retained indices give distinct integer sums. -/
theorem candidate_injective {N A M m r i j : ℕ} (mp : 0<M) (rl : r<period (weight N) M)
    (low : ProductDeficitBand.lower N A≤N) (high : ProductDeficitBand.upper N A≤N)
    (hi : i∈bin N A M m r) (hj : j∈bin N A M m r) (same : candidate N A M r i=candidate N A M r j) : i=j := by
  have ip := (physical rl low high hi).1
  have jp := (physical rl low high hj).1
  let W := stride N
  let P := period (weight N) M
  have wp : 0<W := by dsimp [W,stride]; rcases weights N with h|h|h|h <;> omega
  have pp : 0<P := period_pos mp _
  unfold candidate at ip jp same
  have ix : W*(start N A+r+P*i)=W*(start N A+r+P*j) := by
    dsimp [W,P]
    omega
  exact Nat.eq_of_mul_eq_mul_left pp (Nat.add_left_cancel (Nat.eq_of_mul_eq_mul_left wp ix))

/-- Every position counted in a bin matches its digit and therefore every
smaller radix dividing the combined one. -/
theorem position_digit (N A M r j : ℕ) {D : ℕ} (div : D∣M) :
    weight N*(start N A+r+period (weight N) M*j) ≡ weight N*(start N A+r) [MOD D] := by
  apply Nat.ModEq.of_dvd div
  have dv := dvd_mul_of_dvd_left (period_dvd M (weight N)) j
  have eq := (Nat.modEq_zero_iff_dvd.mpr dv).add_left (weight N*(start N A+r))
  simpa only [Nat.mul_add,←Nat.mul_assoc,Nat.add_zero] using eq

/-- A surviving physical sum satisfies every local admissibility test whose
modulus divides the combined one. Different tests may use different witnesses. -/
theorem position_modulus {N A M m r j d : ℕ} (div : d∣m) (rl : r<period (weight N) M)
    (low : ProductDeficitBand.lower N A≤N) (high : ProductDeficitBand.upper N A≤N)
    (hit : j∈bin N A M m r) :
    AdmissibleSum (N:ZMod d) (candidate N A M r j:ZMod d) := by
  obtain ⟨x,y,prod,sum⟩ := (physical rl low high hit).2.2
  let f := ZMod.castHom div (ZMod d)
  exact ⟨f x,f y,by rw [←map_mul,prod,map_natCast],by rw [←map_add,sum,map_natCast]⟩

/-- The displayed index residue gives precisely the same digit as the source
index, even when the weight and radix share a factor. -/
theorem digit_residue (N A M i : ℕ) :
    let P := period (weight N) M
    weight N*(start N A+i%P) ≡ weight N*(start N A+i) [MOD M] := by
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  simp only [Nat.cast_mul,Nat.cast_add,mul_add,reduce_step]

/-- The true factor sum occupies its actual bin within the public width
interval. The chosen residue also specifies the half-totient digit. -/
theorem actual {p q A M m : ℕ} (mp : 0<M) (ap : 0<A) (even : Even A)
    (po : Odd p) (qo : Odd q) (pl : A≤p) (ql : A≤q) (pu : p<2*A) (qu : q<2*A) :
    let N := p*q
    let P := period (weight N) M
    ∃ r<P, weight N*(start N A+r) ≡ ((p-1)*(q-1)/2) [MOD M] ∧ (bin N A M m r).Nonempty := by
  let N := p*q
  let W := stride N
  let g := weight N
  let B := start N A
  let P := period g M
  have pp : 0<P := period_pos mp g
  have wp : 0<W := by dsimp only [W,stride]; rcases weights N with h|h|h|h <;> omega
  obtain ⟨x,fx⟩ := divides po qo
  change (p-1)*(q-1)=W*x at fx
  obtain ⟨lo,hi⟩ := ProductDeficitBand.contains ap even po qo pl ql pu qu
  have posp : 0<p := ap.trans_le pl
  have posq : 0<q := ap.trans_le ql
  have offset := PowerImageWidth.offset posp posq
  change N=(p-1)*(q-1)+(p+q-1) at offset
  rw [fx] at offset
  have interval := in_range (N:=N) (W:=W) (x:=x) (L:=ProductDeficitBand.lower N A)
    (H:=ProductDeficitBand.upper N A) wp (by omega) (by simpa only [show N-W*x=p+q-1 by omega] using lo)
    (by simpa only [show N-W*x=p+q-1 by omega] using hi)
  change B≤x ∧ x<B+positions N A at interval
  let i := x-B
  let r := i%P
  let j := i/P
  have rsmall : r<P := Nat.mod_lt _ pp
  have rep : r+P*j=i := Nat.mod_add_div i P
  have bi : B+i=x := by dsimp only [i]; omega
  have short : j<laneLength P (positions N A) r :=
    (index_lt rsmall _ j).mp (rep ▸ (by omega : i<positions N A))
  have half : (p-1)*(q-1)/2=g*x := by
    rw [fx,show W=2*g from rfl,Nat.mul_assoc,Nat.mul_div_cancel_left _ (by decide : 0<2)]
  refine ⟨r,rsmall,?_,j,mem_hits.mpr ⟨short,?_⟩⟩
  · rw [half,←bi]
    exact digit_residue N A M i
  · have total : N+1=W*x+(p+q) := by omega
    have tot := congrArg (fun h : ℕ => (h:ZMod m)) total
    have idx := congrArg (fun h : ℕ => (h:ZMod m)) (show B+r+P*j=x by omega)
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at tot idx
    have isSum := admissibleSum_of_factor_pair m (p:=p) (q:=q) rfl
    push_cast at isSum
    change AdmissibleSum (N:ZMod m) ((N:ZMod m)+1-(W:ZMod m)*(B+r:ℕ)-(W*P:ℕ)*(j:ZMod m))
    have same : (N:ZMod m)+1-(W:ZMod m)*(B+r:ℕ)-(W*P:ℕ)*(j:ZMod m)=(p:ZMod m)+q := by
      push_cast
      linear_combination tot - (W:ZMod m)*idx
    rw [same]
    simpa only [N,Nat.cast_mul] using isSum

/-- A consistent digit specifies a unique relative residue less than its period. -/
theorem residue_unique {N A M r s : ℕ} (mp : 0<M) (rl : r<period (weight N) M)
    (sl : s<period (weight N) M) (same : weight N*(start N A+r) ≡ weight N*(start N A+s) [MOD M]) :
    r=s :=
  (Nat.ModEq.add_left_cancel' (start N A) (same.cancel_left_div_gcd mp)).eq_of_lt_of_lt rl sl

/-- For distinct primes the residue in `actual` is the actual cyclotomic digit. -/
theorem cyclotomic_value {p q M : ℕ} (mp : 0<M) (hp : p.Prime) (hq : q.Prime) (neq : p≠q) :
    CyclotomicDigitPeriod.value M (p*q) = ((((p-1)*(q-1)/2)%M:ℕ):ℤ) := by
  rw [CyclotomicDigitPeriod.value_eq mp hp hq neq]
  push_cast [hp.one_le,hq.one_le]
  rfl

/-- A usable bound for any occupied actual bin, without computing its local table. -/
theorem size_of_budgets {N A M m r K : ℕ} (mp : 0<M) (modulus : 0<m)
    (fit : K*(M*m)≤positions N A) (hit : (bin N A M m r).Nonempty) :
    K≤(bin N A M m r).card := by
  let P := period (weight N) M
  let Q := period (stride N*P) m
  have bounds : P*Q≤M*m := Nat.mul_le_mul (Nat.div_le_self ..) (Nat.div_le_self ..)
  apply le_trans _ (lower_in_bin modulus hit)
  exact (Nat.le_div_iff_mul_le (Nat.mul_pos (period_pos mp _) (period_pos modulus _))).mpr
    ((Nat.mul_le_mul_left K bounds).trans fit)

/-- Every index congruent to the true digit selects the same nonempty bin.
The local sieve modulus is arbitrary and may be chosen after the digit is seen. -/
theorem for_factors {p q N A M m K : ℕ} (factor : p*q=N)
    (mp : 0<M) (modulus : 0<m) (ap : 0<A) (even : Even A)
    (po : Odd p) (qo : Odd q) (pl : A≤p) (ql : A≤q) (pu : p<2*A) (qu : q<2*A)
    (fit : K*(M*m)≤positions N A) :
    ∀ r<period (weight N) M, weight N*(start N A+r) ≡ ((p-1)*(q-1)/2) [MOD M] →
      K≤(bin N A M m r).card := by
  subst N
  obtain ⟨s,sl,digit,hit⟩ := actual (m:=m) mp ap even po qo pl ql pu qu
  intro r rl data
  have eq := residue_unique mp rl sl (data.trans digit.symm)
  exact eq ▸ size_of_budgets mp modulus fit hit

open TrueTraceTableCost (freshP freshQ crossedP crossedQ)
open ChebyshevQuarticScale (fresh crossed)

/-- 128 bits of radix and 256 bits of combined local modulus leave at least
2^630 candidate positions in the bin selected by the true fresh product digit. -/
theorem fresh_bound {M m : ℕ} (mp : 0<M) (modulus : 0<m) (radixCap : M≤2^128) (sieveCap : m≤2^256) :
    ∀ r<period (weight fresh) M,
    weight fresh*(start fresh (2^1023)+r) ≡ ((freshP-1)*(freshQ-1)/2) [MOD M] →
      2^630≤(bin fresh (2^1023) M m r).card := by
  apply for_factors TrueTraceTableCost.fresh_price.1 mp modulus (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (Nat.mul_le_mul_left _ (Nat.mul_le_mul radixCap sieveCap)).trans
    ((by decide +kernel : 2^630*(2^128*2^256)≤2^1014).trans fresh_report.2.1.1)

/-- The same caps for the independently generated crossed control. -/
theorem crossed_bound {M m : ℕ} (mp : 0<M) (modulus : 0<m) (radixCap : M≤2^128) (sieveCap : m≤2^256) :
    ∀ r<period (weight crossed) M,
    weight crossed*(start crossed (2^1023)+r) ≡ ((crossedP-1)*(crossedQ-1)/2) [MOD M] →
      2^633≤(bin crossed (2^1023) M m r).card := by
  apply for_factors TrueTraceTableCost.crossed_price.1 mp modulus (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (Nat.mul_le_mul_left _ (Nat.mul_le_mul radixCap sieveCap)).trans
    ((by decide +kernel : 2^633*(2^128*2^256)≤2^1017).trans crossed_report.2.1.1)

private noncomputable def sumDec {m : ℕ} [NeZero m] (n s : ZMod m) :
    Decidable (AdmissibleSum n s) := by unfold AdmissibleSum; infer_instance
attribute [local instance] sumDec

/-- With step coprime to the sieve modulus, every full orbit has exactly
the full local trace count, including singular traces. -/
theorem coprime_orbit {m : ℕ} (pos : 0<m) {step : ℕ} (cop : step.Coprime m)
    (n a : ZMod m) : (hits n a step (period step m)).card =
      Nat.card {s : ZMod m // AdmissibleSum n s} := by
  letI : NeZero m := ⟨pos.ne'⟩
  let R := univ.filter (AdmissibleSum n)
  have card : R.card=Nat.card {s : ZMod m // AdmissibleSum n s} := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [←card,show period step m=m by simp only [period,cop.symm.gcd_eq_one,Nat.div_one]]
  let u := ZMod.unitOfCoprime step cop
  let revertSum := fun s : ZMod m => (a-s)*((u⁻¹: (ZMod m)ˣ):ZMod m)
  have inverse (t : ZMod m) : revertSum (a-(step:ZMod m)*t)=t := by
    calc _=t*((u:ZMod m)*↑(u⁻¹)) := by dsimp [revertSum,u,ZMod.coe_unitOfCoprime]; ring
         _=t := by simp
  refine card_bij (s:=hits n a step m) (t:=R) (fun (i : ℕ) _ => a-(step:ZMod m)*(i:ZMod m)) ?_ ?_ ?_
  · intro i h
    exact mem_filter.mpr ⟨mem_univ _,(mem_hits.mp h).2⟩
  · intro i hi j hj eq
    have same := congrArg revertSum eq
    simp only [inverse] at same
    exact ((ZMod.natCast_eq_natCast_iff ..).mp same).eq_of_lt_of_lt
      (mem_hits.mp hi).1 (mem_hits.mp hj).1
  · intro s hs
    have value : a-(step:ZMod m)*revertSum s=s := by
      calc _=a-(a-s)*((u:ZMod m)*↑(u⁻¹)) := by dsimp [revertSum,u,ZMod.coe_unitOfCoprime]; ring
           _=s := by simp
    refine ⟨(revertSum s).val,mem_hits.mpr ⟨ZMod.val_lt _,?_⟩,?_⟩
    · rw [ZMod.natCast_zmod_val,value]
      exact (mem_filter.mp hs).2
    · simpa only [ZMod.natCast_zmod_val] using value

private theorem count315 (n u v w : ℕ)
    (nine : Nat.card {s : ZMod 9 // AdmissibleSum (n:ZMod 9) s}=u)
    (five : Nat.card {s : ZMod 5 // AdmissibleSum (n:ZMod 5) s}=v)
    (seven : Nat.card {s : ZMod 7 // AdmissibleSum (n:ZMod 7) s}=w) :
    Nat.card {s : ZMod 315 // AdmissibleSum (n:ZMod 315) s}=u*(v*w) := by
  rw [card_admissibleSum_crt (a:=9) (b:=5*7) (by decide) n,
    card_admissibleSum_crt (a:=5) (b:=7) (by decide) n,nine,five,seven]

theorem fresh_classes : Nat.card {s : ZMod 315 // AdmissibleSum (fresh:ZMod 315) s}=18 := by
  rw [show (fresh:ZMod 315) = ((19:ℕ):ZMod 315) by decide +kernel]
  apply count315 19 2 3 3 <;> rw [Nat.card_eq_fintype_card] <;> decide +kernel

theorem crossed_classes : Nat.card {s : ZMod 315 // AdmissibleSum (crossed:ZMod 315) s}=24 := by
  rw [show (crossed:ZMod 315) = ((274:ℕ):ZMod 315) by decide +kernel]
  apply count315 274 2 3 4 <;> rw [Nat.card_eq_fintype_card] <;> decide +kernel

/-- Every realizable digit bin has this bound when its sum step is invertible
at the wheel. The starting residue and the digit value do not affect it. -/
theorem from_local_count {N A M m c K : ℕ} (mp : 0<m)
    (cop : (stride N*period (weight N) M).Coprime m)
    (localCount : Nat.card {s : ZMod m // AdmissibleSum (N:ZMod m) s}=c)
    (budget : K≤(positions N A/period (weight N) M/m)*c) (r : ℕ) : K≤(bin N A M m r).card := by
  let P := period (weight N) M
  let S := stride N*P
  let a := (N:ZMod m)+1-(stride N:ZMod m)*(start N A+r:ℕ)
  let L := laneLength P (positions N A) r
  have unitPeriod : period S m=m := by
    change m/m.gcd (stride N*period (weight N) M)=m
    rw [cop.symm.gcd_eq_one,Nat.div_one]
  have cnt := (coprime_orbit mp cop (N:ZMod m) a).trans localCount
  have eq := exact_count mp (N:ZMod m) a S L
  dsimp only at eq
  change (hits (N:ZMod m) a S (period S m)).card=c at cnt
  rw [cnt,unitPeriod] at eq
  have short : positions N A/P≤L := by dsimp only [L,laneLength]; omega
  have first := Nat.mul_le_mul_right c (Nat.div_le_div_right (c:=m) short)
  change K ≤ (hits (N:ZMod m) a S L).card
  rw [eq]
  exact (budget.trans first).trans (Nat.le_add_right ..)

theorem fresh_315 (r : Fin (period (weight fresh) (2^128))) : 2^883≤(bin fresh (2^1023) (2^128) 315 r).card := by
  apply from_local_count (by decide) (by decide +kernel) fresh_classes _ r
  have pp : period (weight fresh) (2^128)=2^126 := by decide +kernel
  rw [pp]
  have lower := fresh_report.2.1.1
  exact (by decide +kernel : 2^883≤(2^1014/2^126/315)*18).trans
    (Nat.mul_le_mul_right _ (Nat.div_le_div_right (Nat.div_le_div_right lower)))

theorem crossed_315 (r : Fin (period (weight crossed) (2^128))) : 2^886≤(bin crossed (2^1023) (2^128) 315 r).card := by
  apply from_local_count (by decide) (by decide +kernel) crossed_classes _ r
  have pp : period (weight crossed) (2^128)=2^127 := by decide +kernel
  rw [pp]
  have lower := crossed_report.2.1.1
  exact (by decide +kernel : 2^886≤(2^1017/2^127/315)*24).trans
    (Nat.mul_le_mul_right _ (Nat.div_le_div_right (Nat.div_le_div_right lower)))

end PrimeFactors.ActualDigitMultiplicity
