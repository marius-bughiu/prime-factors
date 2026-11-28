import PrimeFactors.FiveSquareGuessRanks
import PrimeFactors.LocalSumGuessCoverage

/-! Optimal sum-remainder ranks for every unit product at the five prime
squares. The product is given before guessing. The bits record whether it
is a square in each of the five residue fields. -/

namespace PrimeFactors.FiveSquareSignRanks

open Finset PrimeSquareSumWeights PrimeSquareExpectedRank
open FiveSquareGuessRanks (primes score)
open private PrimeFactors.FiveSquareGuessRanks.overlap
  PrimeFactors.FiveSquareGuessRanks.least_of_overlap from PrimeFactors.FiveSquareGuessRanks
open scoped Classical

abbrev Pattern := Fin 5→Bool
noncomputable def sign (n : ℕ) (i : Fin 5) : Bool := decide (IsSquare (n : ZMod (primes i)))

/-- One square-unit coordinate yields two weight-p labels. A nonsquare
coordinate yields only weight-two labels. -/
def branch (p : ℕ) (sq : Bool) (f : ℕ→ℕ) :=
  if sq then 2*f p+(classes p-2)*f 2 else pairs p/2*f 2

def fold : List (ℕ×Bool) → (ℕ→ℕ) → ℕ
  | [], f => f 1
  | (p,sq)::rest,f => branch p sq (fun z => fold rest (fun w => f (z*w)))

def rows (b : Pattern) (f : ℕ→ℕ) := fold (List.ofFn (fun i => (primes i,b i))) f
def labels (b : Pattern) := rows b (fun _ => 1)
def mass (b : Pattern) := rows b id
def pairMin (b : Pattern) := rows b (fun a => rows b (min a))
def rankMass (b : Pattern) := (mass b+pairMin b)/2
noncomputable def mean (b : Pattern) : ℚ := (rankMass b:ℚ)/mass b
noncomputable def baseline (b : Pattern) : ℚ := ((labels b:ℚ)+1)/2

private theorem local_sum {p n : ℕ} [Fact p.Prime] (odd : p≠2) (unit : ¬p∣n) (f : ℕ→ℕ) :
    (∑ a : Allowed p n, f (weight n a.val))=branch p (decide (IsSquare (n:ZMod p))) f := by
  classical
  by_cases sq : IsSquare (n:ZMod p)
  · simp only [branch,sq,decide_true,if_true]
    have form := PrimeSquareGuessAffinity.sum_weights (fun w => (f w:ℝ)) odd unit sq
    have fit : 2≤classes p := by unfold classes; omega
    rw [← show ((classes p-2:ℕ):ℝ)=(classes p:ℝ)-2 by rw [Nat.cast_sub fit]; norm_num] at form
    dsimp only at form
    exact_mod_cast form
  · simp only [branch,decide_eq_false sq,Bool.false_eq_true,if_false]
    have table (a : Allowed p n) : weight n a.val=2 := by
      rw [LocalSumGuessCoverage.nonsquare_weight (by decide : 0<2) odd sq,if_pos a.2]
    have cnt := LocalSumGuessCoverage.nonsquare_coverage (by decide : 0<2) odd sq univ
    rw [LocalSumGuessCoverage.covered_univ,pair_count unit] at cnt
    have fc : Fintype.card (Allowed p n)=(univ.filter (AdmissibleSum (n:ZMod (p^2)))).card :=
      Fintype.card_subtype _
    have size : Fintype.card (Allowed p n)=pairs p/2 := by omega
    simp only [table,sum_const,card_univ,nsmul_eq_mul,size,Nat.cast_id]

private theorem coordinates {k : ℕ} (p : Fin k→ℕ) [∀ i, Fact (p i).Prime] (n : ℕ)
    (unit : ∀ i,¬p i∣n) (odd : ∀ i,p i≠2) (f : ℕ→ℕ) :
    (∑ x : ∀ i, Allowed (p i) n, f (∏ i,weight n (x i).val))=
      fold (List.ofFn (fun i => (p i,decide (IsSquare (n:ZMod (p i)))))) f := by
  induction k generalizing f with
  | zero => simp [fold]
  | succ k ih =>
    let q := fun i : Fin k => p i.succ
    let T := fun x : ∀ i, Allowed (q i) n => ∏ i, weight n (x i).val
    let rest := List.ofFn (fun i => (q i,decide (IsSquare (n:ZMod (q i)))))
    let e := Fin.consEquiv (fun i => Allowed (p i) n)
    let w := fun x : ∀ i, Allowed (p i) n => f (∏ i,weight n (x i).val)
    have split (v : Allowed (p 0) n × (∀ i, Allowed (q i) n)) :
        w (e v)=f (weight n v.1.val*T v.2) := by
      dsimp only [w,e,T,Fin.consEquiv_apply]
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ]
    have inner (a : Allowed (p 0) n) :
        (∑ x, f (weight n a.val*T x))=fold rest (fun t => f (weight n a.val*t)) :=
      ih q (fun i => unit i.succ) (fun i => odd i.succ) (fun t => f (weight n a.val*t))
    change (∑ x,w x)=_
    rw [←e.sum_comp w]
    simp_rw [split]
    rw [Fintype.sum_prod_type]
    change (∑ a : Allowed (p 0) n, ∑ x, f (weight n a.val*T x))=_
    simp_rw [inner]
    rw [List.ofFn_succ,fold]
    exact local_sum (odd 0) (unit 0) (fun t => fold rest (fun y => f (t*y)))

noncomputable abbrev Modulus : ℕ := CoprimeGuessTables.modulus primes
abbrev Labels (n : ℕ) := CoprimeGuessTables.Labels Modulus n

/-- Exact 1–32-leaf multiplicity calculation for the fixed product. -/
theorem histogram (n : ℕ) (unit : ∀ i, ¬primes i∣n) (f : ℕ→ℕ) :
    (∑ s : Labels n, f (weight n s.val))=rows (sign n) f := by
  have distinct : Function.Injective primes := by decide +kernel
  let e := CoprimeGuessTables.allowedEquiv primes distinct n
  let g := fun x : ∀ i, Allowed (primes i) n => f (∏ i, weight n (x i).val)
  have reindex (s : Labels n) : f (weight n s.val)=g (e s) :=
    congrArg f (CoprimeGuessTables.weight_equiv primes distinct n s)
  simp_rw [reindex]
  exact (e.sum_comp g).trans (coordinates primes n unit (by decide) f)

/-- The pair count is independent of the unit product, and the pairwise
minimum expression is even in every one of the 32 cases. -/
theorem row_totals (b : Pattern) : mass b=3920716800 ∧ mass b+pairMin b=2*rankMass b :=
  (by decide +kernel : ∀ b : Pattern, mass b=3920716800 ∧ mass b+pairMin b=2*rankMass b) b

noncomputable def meanRank {α : Type*} [Fintype α] (w : α→ℕ) (e : Fin (Fintype.card α)≃α) : ℚ :=
  (score w e:ℚ)/((∑ i,w i : ℕ):ℚ)

private theorem from_rows {α : Type*} [Fintype α] (w : α→ℕ) (b : Pattern)
    (law : ∀ f : ℕ→ℕ, (∑ x, f (w x))=rows b f) :
    Fintype.card α=labels b ∧ IsLeast (Set.range (meanRank w)) (mean b) := by
  have sz : Fintype.card α=labels b := by simpa [labels] using law (fun _ => 1)
  have count : (∑ i,w i)=mass b := law id
  have pairs : PrimeFactors.FiveSquareGuessRanks.overlap w=pairMin b := by
    have inner (x : α) := law (min (w x))
    unfold PrimeFactors.FiveSquareGuessRanks.overlap
    simp_rw [inner]
    exact law (fun x => rows b (min x))
  have hs := PrimeFactors.FiveSquareGuessRanks.least_of_overlap w
    ((congrArg₂ Nat.add count pairs).trans (row_totals b).2)
  obtain ⟨⟨e,hit⟩,least⟩ := hs
  refine ⟨sz,⟨e,?_⟩,?_⟩
  · simp only [meanRank,mean,hit,count]
  · rintro _ ⟨order,rfl⟩
    unfold meanRank mean
    rw [count]
    exact div_le_div_of_nonneg_right (by exact_mod_cast least ⟨order,rfl⟩)
      (Nat.cast_nonneg (mass b) (α:=ℚ))

/-- The compressed optimum is achieved on actual labels modulo the full
product, and bounds every fixed ordering from below. -/
theorem optimum (n : ℕ) (unit : ∀ i,¬primes i∣n) : Fintype.card (Labels n)=labels (sign n) ∧
    IsLeast (Set.range (meanRank (fun s : Labels n => weight n s.val))) (mean (sign n)) :=
  from_rows (fun s : Labels n => weight n s.val) (sign n) (histogram n unit)

/-- A global unit product meets all five local unit conditions. -/
theorem local_units {n : ℕ} (h : IsUnit (n:ZMod Modulus)) (i : Fin 5) : ¬primes i∣n := by
  have cop := (ZMod.isUnit_iff_coprime n Modulus).mp h
  have div : primes i∣Modulus := (by decide +kernel : ∀ j, primes j∣Modulus) i
  intro fail
  have common := Nat.dvd_gcd fail div
  rw [cop.gcd_eq_one] at common
  exact (Fact.out : (primes i).Prime).not_dvd_one common

/-- Pattern indices use one bit per prime; the bit for 5 is the most significant. -/
def decode (k : Fin 32) : Pattern := fun i => k.val.testBit (4-i.val)

theorem decoded_all : Function.Bijective decode := by
  constructor
  · intro i j eq
    exact (by decide +kernel : ∀ i j : Fin 32, decode i=decode j → i=j) i j eq
  · exact (by decide +kernel : ∀ b : Pattern, ∃ i, decode i=b)

/-- Each entry gives the attained label count and the exact minimum mean
number of guesses. Entries are in increasing binary pattern order. -/
theorem outcomes : List.ofFn (fun k : Fin 32 => (labels (decode k),mean (decode k))) =
  [(122522400,122522401/2), (109008900,194369177/4), (105243600,90844601/2),
   (93635850,579426933/16), (102473280,86433985/2), (91171080,34486043),
   (88021920,64772177/2), (78313620,207688499/8), (93350400,73902401/2),
   (83054400,29559888), (80185600,166878803/6), (71341600,178775029/8),
   (78074880,53266305/2), (69463680,42826603/2), (67064320,121294051/6),
   (59667520,195789599/12), (85765680,67387321/2), (76306230,431395973/16),
   (73670520,50749931/2), (65545095,1305357547/64), (71731296,243039893/10),
   (63819756,782054111/40), (61615344,184591377/10), (54819534,2385142021/160),
   (65345280,42980081/2), (58138080,138649229/8), (56129920,98246063/6),
   (49939120,1272331273/96), (54652416,157373221/10), (48624576,50981933/4),
   (46945024,362102327/30), (41767264,470695147/48)] := by decide +kernel

/-- The all-square and all-nonsquare products give the best and worst
relative savings and mean ranks in this five-prime model. -/
theorem extremes (b : Pattern) :
    470695147/48≤mean b ∧ mean b≤122522401/2 ∧
    0≤1-mean b/baseline b ∧ 1-mean b/baseline b≤531719213/1002414360 :=
  (by decide +kernel : ∀ b : Pattern, 470695147/48≤mean b ∧ mean b≤122522401/2 ∧
    0≤1-mean b/baseline b ∧ 1-mean b/baseline b≤531719213/1002414360) b

/-- Averaging test counts equally over the 32 square/nonsquare patterns. -/
theorem pooled :
    (∑ b : Pattern,mean b)/32=159599216429/6144 ∧
    (∑ b : Pattern,baseline b)/32=2367408217/64 ∧
    1-(∑ b : Pattern,mean b)/(∑ b : Pattern,baseline b)=67671972403/227271188832 := by
  decide +kernel

end PrimeFactors.FiveSquareSignRanks
