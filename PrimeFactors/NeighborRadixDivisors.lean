import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! Divisor counts for the linear forms that arise at a radix dividing
one of the two neighbors of the input. Each small divisor occurs in at most
one congruence class of radices, without a primality assumption on the radix. -/

namespace PrimeFactors.NeighborRadixDivisors
open Finset

/-- Both signs of the integer linear form, including the absolute value of −1. -/
def value (t D : ℕ) (plus : Bool) : ℕ :=
  (if plus then (t : ℤ)*D+1 else (t : ℤ)*D-1).natAbs

@[simp] theorem value_zero (D : ℕ) (plus : Bool) : value 0 D plus = 1 := by
  cases plus <;> simp [value]

/-- Cancel the coefficient without an inverse: subtract the two divisibilities
after multiplying each one by the opposite radix. -/
theorem same_residue {m t x y : ℕ} (plus : Bool) (hx : m ∣ value t x plus)
    (hy : m ∣ value t y plus) : x ≡ y [MOD m] := by
  rw [Nat.modEq_iff_dvd]
  have cast (z : ℕ) (h : m ∣ value t z plus) :
      (m:ℤ) ∣ (if plus then (t:ℤ)*z+1 else (t:ℤ)*z-1) := by
    simpa only [value, ← Int.natCast_dvd_natCast, Int.natCast_natAbs,
      dvd_abs] using h
  have dx := cast x hx
  have dy := cast y hy
  cases plus <;> simp only [Bool.false_eq_true,↓reduceIte] at dx dy
  · convert dvd_sub (dvd_mul_of_dvd_right dy (x:ℤ)) (dvd_mul_of_dvd_right dx (y:ℤ)) using 1
    ring
  · convert dvd_sub (dvd_mul_of_dvd_right dx (y:ℤ)) (dvd_mul_of_dvd_right dy (x:ℤ)) using 1
    ring

/-- A slab of P consecutive radices contains at most P/m+1 occurrences. -/
theorem progression_card {P m t : ℕ} (plus : Bool) :
    ((Ico P (2*P)).filter (fun D => m ∣ value t D plus)).card ≤ P/m+1 := by
  let s := (Ico P (2*P)).filter (fun D => m ∣ value t D plus)
  suffices s.card ≤ (range (P/m+1)).card by simpa using this
  apply card_le_card_of_injOn (fun D => (D-P)/m)
  · intro D hD
    obtain ⟨hD,_⟩ := mem_filter.mp hD
    obtain ⟨_,hi⟩ := mem_Ico.mp hD
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
  · intro a ha b hb same
    obtain ⟨wa,da⟩ := mem_filter.mp ha
    obtain ⟨wb,db⟩ := mem_filter.mp hb
    have la := (mem_Ico.mp wa).1
    have lb := (mem_Ico.mp wb).1
    have rel := same_residue plus da db
    have shifted : P+(a-P) ≡ P+(b-P) [MOD m] := by
      simpa [Nat.add_sub_of_le la, Nat.add_sub_of_le lb] using rel
    have rem : (a-P)%m = (b-P)%m := Nat.ModEq.add_left_cancel' P shifted
    change (a-P)/m=(b-P)/m at same
    have full := Nat.div_add_mod (a-P) m
    rw [same,rem,Nat.div_add_mod] at full
    omega

private theorem divisor_pairs {n P : ℕ} (cap : n≤P^2) :
    n.divisors.card ≤ 2*((Icc 1 P).filter (· ∣ n)).card := by
  by_cases zero : n=0
  · simp [zero]
  let small := (Icc 1 P).filter (· ∣ n)
  have subset : n.divisors ⊆ small ∪ small.image (n/·) := by
    intro d hd
    have divides := Nat.dvd_of_mem_divisors hd
    have dp := Nat.pos_of_mem_divisors hd
    by_cases low : d≤P
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨dp,low⟩,divides⟩)
    · have mul := Nat.mul_div_cancel' divides
      have copos : 0<n/d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero zero) divides) dp
      have cohi : n/d≤P := by
        apply le_of_not_gt
        intro h
        have big := Nat.mul_lt_mul_of_lt_of_lt (by omega : P<d) h
        nlinarith only [big,mul,cap]
      exact mem_union_right _ (mem_image.mpr ⟨n/d,
        mem_filter.mpr ⟨mem_Icc.mpr ⟨copos,cohi⟩,Nat.div_dvd_of_dvd divides⟩,
        Nat.div_div_self divides zero⟩)
  have size := (card_le_card subset).trans (card_union_le ..)
  have map : (small.image (n/·)).card≤small.card := card_image_le
  change n.divisors.card≤2*small.card
  omega

/-- Each dyadic denominator block costs at most P after summing floor(P/m). -/
private theorem reciprocal_blocks (P j : ℕ) :
    ∑ m ∈ Ico 1 (2^j), P/m ≤ j*P := by
  induction j with
  | zero => simp
  | succ j ih =>
    let B := (2:ℕ)^j
    have bp : 0<B := by positivity
    have tail := sum_le_sum (s:=Ico B (B*2)) (fun m hm =>
      Nat.div_le_div_left (a:=P) (mem_Ico.mp hm).1 bp)
    have width : B*2-B=B := by omega
    simp only [sum_const,Nat.card_Ico,width,nsmul_eq_mul] at tail
    have price := tail.trans (Nat.mul_div_le P B)
    rw [pow_succ,← sum_Ico_consecutive (fun m => P/m) (by change 1≤B; omega)
      (by change B≤B*2; omega)]
    change (∑ m ∈ Ico 1 (2^j), P/m) + (∑ m ∈ Ico B (B*2), P/m) ≤ (j+1)*P
    rw [Nat.add_mul,one_mul]
    omega

private theorem reciprocal (P : ℕ) :
    ∑ m ∈ Icc 1 P, P/m ≤ (P.log2+1)*P := by
  have cap := Nat.lt_pow_succ_log_self (b:=2) (by decide) P
  rw [← Nat.log2_eq_log_two] at cap
  exact (sum_le_sum_of_subset_of_nonneg (f:=fun m => P/m) (t:=Ico 1 (2^(P.log2+1))) (fun m hm =>
    mem_Ico.mpr ⟨(mem_Icc.mp hm).1,(mem_Icc.mp hm).2.trans_lt cap⟩) (fun _ _ _ => Nat.zero_le _)).trans
    (reciprocal_blocks ..)

/-- Divisor bound summed over all radices in the slab. The sign, coefficient
and modulus are unrestricted except for twice the coefficient fitting in P. -/
theorem sum_tau {P t : ℕ} (pos : 0<P) (bound : 2*t≤P) (plus : Bool) :
    (∑ D ∈ Ico P (2*P), (value t D plus).divisors.card) ≤ 2*P*(P.log2+2) := by
  have cap {D : ℕ} (hd : D ∈ Ico P (2*P)) : value t D plus≤P^2 := by
    have hi := (mem_Ico.mp hd).2
    have one : 1≤P^2 := Nat.one_le_pow 2 P pos
    by_cases zero : t=0
    · simpa [zero] using one
    have prod := Nat.mul_le_mul bound (show D+1≤2*P by omega)
    have room : t*D+1≤P^2 := by nlinarith only [prod,show 1≤t by omega]
    have dm : 1≤t*D := Nat.mul_pos (by omega) (pos.trans_le (mem_Ico.mp hd).1)
    cases plus
    · have id : ((t:ℤ)*D-1) = ((t*D-1:ℕ):ℤ) := by
        rw [Nat.cast_sub dm]; simp
      simpa only [value,Bool.false_eq_true,↓reduceIte,id,Int.natAbs_ofNat] using
        (show t*D-1≤P^2 by omega)
    · have id : ((t:ℤ)*D+1) = ((t*D+1:ℕ):ℤ) := by push_cast; rfl
      simpa only [value,↓reduceIte,id,Int.natAbs_ofNat] using room
  have count := sum_le_sum (s:=Ico P (2*P)) (fun D hd => divisor_pairs (cap hd))
  simp_rw [card_filter] at count
  rw [← mul_sum, sum_comm] at count
  have per := sum_le_sum (s:=Icc 1 P) (fun m _ => progression_card (P:=P) (m:=m) (t:=t) plus)
  simp_rw [card_filter] at per
  rw [sum_add_distrib,sum_const,Nat.card_Icc,nsmul_eq_mul,mul_one] at per
  have cost := reciprocal P
  have widths : P+1-1=P := by omega
  rw [widths] at per
  calc
    _ ≤ _ := count
    _ ≤ 2*((P.log2+1)*P+P) := Nat.mul_le_mul_left 2 (per.trans (Nat.add_le_add_right cost P))
    _ = _ := by ring

end PrimeFactors.NeighborRadixDivisors
