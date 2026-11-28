import PrimeFactors.CoprimeGuessTables

/-! Absolute coverage and guesswork bounds for weights on one complete
product of residue spaces. Each sampling unit is one ordered modular pair. -/

namespace PrimeFactors.JointSumGuessFloor

open Finset PrimeSquareSumWeights PrimeSquareExpectedRank CoprimeGuessTables
open scoped Classical

/-- No one residue can receive more than the product of the local weight caps. -/
noncomputable def cap {ι : Type*} [Fintype ι] (p : ι→ℕ) := ∏ i, p i

/-- Number of maximally weighted labels that would be needed to hold all the mass. -/
noncomputable def spread {ι : Type*} [Fintype ι] (p : ι→ℕ) := ∏ i, (p i-1)

private theorem sum_labels {m n : ℕ} [NeZero m] :
    (∑ s : Labels m n, weight n s.val)=Nat.card (Pairs n m) := by
  have none (s : {s : ZMod m // ¬AdmissibleSum (n:ZMod m) s}) : weight n s.val=0 :=
    Nat.eq_zero_of_not_pos (fun h => s.property ((positive_iff s.val).mp h))
  have split := Fintype.sum_subtype_add_sum_subtype (AdmissibleSum (n:ZMod m)) (weight n)
  simp only [none,sum_const_zero,add_zero] at split
  exact split.trans ((LocalSumGuessCoverage.covered_eq_sum n univ).symm.trans
    (LocalSumGuessCoverage.covered_univ n))

variable {ι : Type*} [Fintype ι] (p : ι→ℕ) [∀ i, Fact (p i).Prime]

private theorem cap_pos : 0<cap p := prod_pos (fun i _ => (Fact.out : (p i).Prime).pos)

private theorem spread_pos : 0<spread p :=
  prod_pos (fun i _ => Nat.sub_pos_of_lt (Fact.out : (p i).Prime).one_lt)

/-- Exact total mass at any fixed unit product. -/
theorem total_pairs (distinct : Function.Injective p) (n : ℕ) (unit : ∀ i, ¬p i∣n) :
    Nat.card (Pairs n (modulus p))=cap p*spread p := by
  let e := allowedEquiv p distinct n
  have local_sum (i : ι) : (∑ s : Allowed (p i) n, weight n s.val)=p i*(p i-1) :=
    sum_labels.trans (pair_count (unit i))
  rw [←sum_labels]
  calc
    _ = ∑ s : Labels (modulus p) n, ∏ i, weight n (e s i).val :=
      sum_congr rfl (fun s _ => weight_equiv p distinct n s)
    _ = ∑ x : (∀ i, Allowed (p i) n), ∏ i, weight n (x i).val :=
      e.sum_comp (fun x : (∀ i, Allowed (p i) n) => ∏ i, weight n (x i).val)
    _ = _ := by rw [←Fintype.prod_sum (fun i (s : Allowed (p i) n) => weight n s.val)]
                simp only [local_sum,prod_mul_distrib,cap,spread]

/-- The cap applies even at residues never attained, and needs no square condition on the product. -/
theorem weight_le (distinct : Function.Injective p) (n : ℕ) (odd : ∀ i, p i≠2)
    (s : ZMod (modulus p)) : weight n s≤cap p := by
  by_cases pass : AdmissibleSum (n:ZMod (modulus p)) s
  · let e := allowedEquiv p distinct n
    rw [weight_equiv p distinct n (⟨s,pass⟩ : Labels (modulus p) n)]
    apply prod_le_prod' (fun i _ => ?_)
    rw [weight_formula (odd i)]
    have two := (Fact.out : (p i).Prime).two_le
    split_ifs <;> omega
  · have zero := Nat.eq_zero_of_not_pos (fun h => pass ((positive_iff s).mp h))
    rw [zero]
    exact Nat.zero_le _

theorem point_probability (distinct : Function.Injective p) (n : ℕ) (odd : ∀ i, p i≠2)
    (unit : ∀ i, ¬p i∣n) (s : ZMod (modulus p)) :
    (weight n s:ℚ)/Nat.card (Pairs n (modulus p)) ≤ 1/(spread p:ℚ) := by
  rw [total_pairs p distinct n unit,Nat.cast_mul]
  have c : 0<(cap p:ℚ) := by exact_mod_cast cap_pos p
  have h : 0<(spread p:ℚ) := by exact_mod_cast spread_pos p
  apply (div_le_div_iff₀ (mul_pos c h) h).mpr
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (show (weight n s:ℚ)≤cap p by exact_mod_cast weight_le p distinct n odd s) h.le

/-- Distinct guesses attaining at least half the mass must number at least
the ceiling of half the spread. Repeated guesses can be discarded. -/
theorem half_coverage (distinct : Function.Injective p) (n : ℕ) (odd : ∀ i, p i≠2)
    (unit : ∀ i, ¬p i∣n) (S : Finset (ZMod (modulus p)))
    (half : Nat.card (Pairs n (modulus p))≤2*LocalSumGuessCoverage.covered n S) :
    (spread p+1)/2≤S.card := by
  rw [total_pairs p distinct n unit,LocalSumGuessCoverage.covered_eq_sum] at half
  have small := sum_le_sum (s:=S) (fun s _ => weight_le p distinct n odd s)
  simp only [sum_const,nsmul_eq_mul] at small
  have both : cap p*spread p≤cap p*(2*S.card) := by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using half.trans (Nat.mul_le_mul_left 2 small)
  have h := Nat.le_of_mul_le_mul_left both (cap_pos p)
  omega

/-- A finite table with each individual mass at most C has weighted
one-based rank at least T(T+C)/(2C), where T denotes its total mass. -/
private theorem capped_ranks {k : ℕ} (C : ℕ) (w : Fin k→ℕ) (bound : ∀ i,w i≤C) :
    (∑ i,w i)*((∑ i,w i)+C) ≤ 2*C*∑ i,(i.val+1)*w i := by
  induction k with
  | zero => simp
  | succ k ih =>
    let v (i : Fin k) := w i.castSucc
    let T := ∑ i,v i
    let z := w (Fin.last k)
    have prior := ih v (fun i => bound i.castSucc)
    have room : T≤k*C := by
      simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using
        sum_le_sum (s:=univ) (fun (i : Fin k) _ => bound i.castSucc)
    have step : (2*T+z+C)*z ≤ (2*C*(k+1))*z :=
      Nat.mul_le_mul_right _ (by nlinarith only [room,bound (Fin.last k)])
    rw [Fin.sum_univ_castSucc (f:=w),Fin.sum_univ_castSucc (f:=fun i => (i.val+1)*w i)]
    change (T+z)*(T+z+C)≤2*C*((∑ i : Fin k,(i.val+1)*v i)+(k+1)*z)
    change T*(T+C)≤_ at prior
    nlinarith only [prior,step]

/-- Every permutation of all attained labels has mean one-based rank at
least (H+1)/2, where H is the product of the prime predecessors. -/
theorem mean_rank (distinct : Function.Injective p) (n : ℕ) (odd : ∀ i, p i≠2)
    (unit : ∀ i, ¬p i∣n) (e : Fin (Fintype.card (Labels (modulus p) n)) ≃ Labels (modulus p) n) :
    ((spread p:ℝ)+1)/2 ≤ IndependentGuessRanks.meanRank
      (fun s : Labels (modulus p) n => (weight n s.val:ℝ)) e := by
  let w := fun i => weight n (e i).val
  let T := cap p*spread p
  have mass : (∑ i,w i)=T :=
    (e.sum_comp (fun s => weight n s.val)).trans (sum_labels.trans (total_pairs p distinct n unit))
  have bound := capped_ranks (cap p) w (fun i => weight_le p distinct n odd (e i).val)
  rw [mass] at bound
  have lower : T*(spread p+1)≤2*∑ i,(i.val+1)*w i := by
    apply Nat.le_of_mul_le_mul_left (c:=cap p) _ (cap_pos p)
    calc
      cap p*(T*(spread p+1))=T*(T+cap p) := by dsimp [T]; ring
      _ ≤ _ := by simpa only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using bound
  have total : IndependentGuessRanks.total (fun s : Labels (modulus p) n => (weight n s.val:ℝ))=T := by
    change (∑ s : Labels (modulus p) n, (weight n s.val:ℝ))=(T:ℝ)
    rw [←Nat.cast_sum]
    exact congrArg (fun a : ℕ => (a:ℝ)) (sum_labels.trans (total_pairs p distinct n unit))
  have pos : (0:ℝ)<T := by exact_mod_cast Nat.mul_pos (cap_pos p) (spread_pos p)
  rw [IndependentGuessRanks.meanRank,total]
  apply (div_le_div_iff₀ (by norm_num) pos).mpr
  have converted : (T:ℝ)*((spread p:ℝ)+1) ≤ 2*∑ i,((i.val:ℝ)+1)*(w i:ℝ) := by
    exact_mod_cast lower
  simpa only [mul_comm] using converted

omit [∀ i, Fact (p i).Prime] in
/-- For any finite family of primes at or above b+1 the spread is at
least b to the number of coordinates. -/
theorem spread_growth (b : ℕ) (threshold : ∀ i, b<p i) : b^(Fintype.card ι)≤spread p := by
  simpa only [prod_const,card_univ] using
    (prod_le_prod' (s:=univ) (fun i _ => (show b≤p i-1 by have := threshold i; omega)))

/-- In the large-prime tail, half coverage already needs exponentially
many distinct labels in the number of included coordinates. -/
theorem tail_half (distinct : Function.Injective p) (n : ℕ) (large : ∀ i, 11≤p i)
    (unit : ∀ i, ¬p i∣n) (S : Finset (ZMod (modulus p)))
    (half : Nat.card (Pairs n (modulus p))≤2*LocalSumGuessCoverage.covered n S) :
    (10^Fintype.card ι+1)/2 ≤ S.card := by
  have floor := half_coverage p distinct n (fun i => by have := large i; omega) unit S half
  have size := spread_growth p 10 (fun i => by have := large i; omega)
  omega

def fivePrimes : Fin 5 → ℕ := ![5,7,11,13,17]

instance (i : Fin 5) : Fact (fivePrimes i).Prime :=
  ⟨(by decide +kernel : ∀ j, (fivePrimes j).Prime) i⟩

/-- Numerical specialization of the two universal bounds at the five
prime squares used for the exact optimal-order control. -/
theorem five :
    (∀ S : Finset (ZMod (modulus fivePrimes)),
      Nat.card (Pairs 1 (modulus fivePrimes))≤2*LocalSumGuessCoverage.covered 1 S → 23040≤S.card) ∧
    (∀ e : Fin (Fintype.card (Labels (modulus fivePrimes) 1)) ≃ Labels (modulus fivePrimes) 1,
      (46081:ℝ)/2 ≤ IndependentGuessRanks.meanRank
        (fun s : Labels (modulus fivePrimes) 1 => (weight 1 s.val:ℝ)) e) := by
  have different : Function.Injective fivePrimes := by decide +kernel
  have odd : ∀ i,fivePrimes i≠2 := by decide +kernel
  have units : ∀ i,¬fivePrimes i∣1 := fun i => (Fact.out : (fivePrimes i).Prime).not_dvd_one
  have H : spread fivePrimes=46080 := by decide +kernel
  constructor
  · intro S half
    have bound := half_coverage fivePrimes different 1 odd units S half
    rw [H] at bound
    exact bound
  · intro e
    have bound := mean_rank fivePrimes different 1 odd units e
    rw [H] at bound
    norm_num only [Nat.cast_ofNat, Nat.cast_one, Nat.reduceAdd, Nat.cast_add] at bound
    exact le_trans (le_of_eq (by norm_num)) bound

end PrimeFactors.JointSumGuessFloor
