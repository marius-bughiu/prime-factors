import PrimeFactors.CoprimeGuessTables

/-! Exact optimal guesswork for the sum of a uniformly sampled ordered pair
with product one at five prime squares. A 32-leaf multiplicity table is
sufficient for the integer certificate. -/

namespace PrimeFactors.FiveSquareGuessRanks

open Finset PrimeSquareExpectedRank PrimeSquareSumWeights
open scoped Classical

private noncomputable def rankSum {k : ℕ} (w : Fin k→ℕ) := ∑ i, (i.val+1)*w i

private noncomputable def overlap {α : Type*} [Fintype α] (w : α→ℕ) := ∑ a, ∑ b, min (w a) (w b)

private theorem overlap_succ {k : ℕ} (w : Fin (k+1)→ℕ) :
    overlap w=overlap (fun i : Fin k => w i.castSucc)+
      2*(∑ i : Fin k,min (w i.castSucc) (w (Fin.last k)))+w (Fin.last k) := by
  let v (i : Fin k) := w i.castSucc
  let z := w (Fin.last k)
  have row (x : ℕ) : (∑ j, min x (w j))=(∑ j : Fin k, min x (v j))+min x z :=
    Fin.sum_univ_castSucc _
  unfold overlap
  simp_rw [row]
  rw [Fin.sum_univ_castSucc]
  simp only [sum_add_distrib,min_self]
  have swap : (∑ i, min z (v i))=∑ i, min (v i) z := sum_congr rfl (fun _ _ => min_comm ..)
  rw [show min (w (Fin.last k)) z=z by exact min_self _]
  change ((∑ i, ∑ j, min (v i) (v j))+(∑ i, min (v i) z))+((∑ i, min z (v i))+z)=_
  rw [swap]
  dsimp only [z,v]
  omega

/-- For every ordering, twice the rank mass is at least the total mass
plus the pairwise minimum sum. Decreasing order attains equality. -/
private theorem rank_identity {k : ℕ} (w : Fin k→ℕ) :
    (∑ i,w i)+overlap w≤2*rankSum w ∧
    (Antitone w → (∑ i,w i)+overlap w=2*rankSum w) := by
  induction k with
  | zero => simp [overlap,rankSum]
  | succ k ih =>
    let v (i : Fin k) := w i.castSucc
    let z := w (Fin.last k)
    have old := ih v
    have cross : (∑ i,min (v i) z)≤k*z := by
      simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using
        (sum_le_sum (s:=univ) (fun (i : Fin k) _ => min_le_right (v i) z))
    have cost : rankSum w=rankSum v+(k+1)*z := by
      unfold rankSum
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [cost,overlap_succ,Fin.sum_univ_castSucc (f:=w)]
    change (∑ i,v i)+z+(overlap v+2*(∑ i,min (v i) z)+z)≤_ ∧ _
    constructor
    · have h := old.1
      nlinarith only [h,cross]
    · intro order
      have eq := old.2 (fun _ _ h => order (Fin.castSucc_le_castSucc_iff.mpr h))
      have last (i : Fin k) : min (v i) z=z := min_eq_right (order (Fin.le_last _))
      have sum : (∑ i,min (v i) z)=k*z := by simp [last]
      change (∑ i,v i)+z+(overlap v+2*(∑ i,min (v i) z)+z)=_
      rw [sum]
      nlinarith only [eq]

noncomputable def score {α : Type*} [Fintype α] (w : α→ℕ) (e : Fin (Fintype.card α) ≃ α) :=
  rankSum (w ∘ e)

private theorem least_of_overlap {α : Type*} [Fintype α] (w : α→ℕ) {r : ℕ}
    (mass : (∑ x,w x)+overlap w=2*r) : IsLeast (Set.range (score w)) r := by
  have moved (e : Fin (Fintype.card α) ≃ α) :
      (∑ i,(w ∘ e) i)+overlap (w ∘ e)=2*r := by
    have inner (x : α) := e.sum_comp (fun y => min (w x) (w y))
    have outer := e.sum_comp (fun x => ∑ y, min (w x) (w y))
    simpa only [overlap,Function.comp_apply,inner,outer,e.sum_comp w] using
      (show (∑ i,w (e i))+(∑ i,∑ j,min (w (e i)) (w (e j)))=2*r by
        simp only [inner,outer,e.sum_comp w]
        exact mass)
  constructor
  · let e₀ := (Fintype.equivFin α).symm
    let f := fun i => OrderDual.toDual (w (e₀ i))
    let e := (Tuple.sort f).trans e₀
    have sorted : Antitone (w ∘ e) := fun _ _ h => Tuple.monotone_sort f h
    refine ⟨e,?_⟩
    have h := (rank_identity (w ∘ e)).2 sorted
    rw [moved e] at h
    unfold score
    omega
  · rintro _ ⟨e,rfl⟩
    have h := (rank_identity (w ∘ e)).1
    rw [moved e] at h
    unfold score
    omega

/-- Weight multiplicities under each local choice of a singular or regular
label. Applying the recursion to five primes evaluates 32 leaves. -/
def compressed : List ℕ → (ℕ→ℕ) → ℕ
  | [], f => f 1
  | p::ps,f => 2*compressed ps (fun w => f (p*w))+
      (classes p-2)*compressed ps (fun w => f (2*w))

private theorem local_sum {p : ℕ} [Fact p.Prime] (odd : p≠2) (f : ℕ→ℕ) :
    (∑ x : Allowed p 1, f (weight 1 x.val))=2*f p+(classes p-2)*f 2 := by
  have unit := (Fact.out : p.Prime).not_dvd_one
  have form := PrimeSquareGuessAffinity.sum_weights (fun w => (f w:ℝ)) odd unit (by norm_num)
  have fit : 2≤classes p := by unfold classes; omega
  rw [← show ((classes p-2:ℕ):ℝ)=(classes p:ℝ)-2 by rw [Nat.cast_sub fit]; norm_num] at form
  dsimp only at form
  exact_mod_cast form

/-- Summing a function of the product weight over actual local labels is
exactly the compressed sum over the binary multiplicity choices. -/
private theorem coordinate_sum {k : ℕ} (p : Fin k→ℕ) [∀ i,Fact (p i).Prime]
    (odd : ∀ i, p i≠2) (f : ℕ→ℕ) :
    (∑ x : ∀ i, Allowed (p i) 1, f (∏ i,weight 1 (x i).val))=compressed (List.ofFn p) f := by
  induction k generalizing f with
  | zero => simp [compressed]
  | succ k ih =>
    let q := fun i : Fin k => p i.succ
    let tail := fun x : ∀ i, Allowed (q i) 1 => ∏ i, weight 1 (x i).val
    let e := Fin.consEquiv (fun i => Allowed (p i) 1)
    let w := fun x : ∀ i, Allowed (p i) 1 => f (∏ i,weight 1 (x i).val)
    have split (v : Allowed (p 0) 1 × (∀ i, Allowed (q i) 1)) :
        w (e v)=f (weight 1 v.1.val*tail v.2) := by
      dsimp only [w,e,tail,Fin.consEquiv_apply]
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ]
    change (∑ x,w x)=_
    rw [← e.sum_comp w]
    simp_rw [split]
    rw [Fintype.sum_prod_type, sum_comm]
    have col (x : ∀ i, Allowed (q i) 1) : (∑ a : Allowed (p 0) 1,f (weight 1 a.val*tail x))=
        2*f (p 0*tail x)+(classes (p 0)-2)*f (2*tail x) := local_sum (odd 0) (fun t => f (t*tail x))
    change (∑ x, ∑ a : Allowed (p 0) 1, f (weight 1 a.val*tail x))=_
    simp_rw [col]
    rw [sum_add_distrib,←mul_sum,←mul_sum]
    have left := ih q (fun i => odd i.succ) (fun t => f (p 0*t))
    have right := ih q (fun i => odd i.succ) (fun t => f (2*t))
    change (∑ x, f (p 0*tail x))=compressed (List.ofFn q) (fun t => f (p 0*t)) at left
    change (∑ x, f (2*tail x))=compressed (List.ofFn q) (fun t => f (2*t)) at right
    rw [left,right,List.ofFn_succ,compressed]

def primes : Fin 5→ℕ := ![5,7,11,13,17]
private instance prime_facts (i : Fin 5) : Fact (primes i).Prime :=
  ⟨(by decide +kernel : ∀ j, (primes j).Prime) i⟩

abbrev Labels := ∀ i, Allowed (primes i) 1
noncomputable def labelWeight (x : Labels) := ∏ i, weight 1 (x i).val

theorem histogram (f : ℕ→ℕ) :
    (∑ x : Labels, f (labelWeight x))=compressed [5,7,11,13,17] f := by
  exact coordinate_sum primes (by decide) f

private theorem totals :
    compressed [5,7,11,13,17] (fun _ => 1)=41767264 ∧
    compressed [5,7,11,13,17] id=3920716800 ∧
    compressed [5,7,11,13,17] (fun w => compressed [5,7,11,13,17] (min w))=
      76894261517673600 := by decide +kernel

abbrev GlobalLabels := CoprimeGuessTables.Labels (CoprimeGuessTables.modulus primes) 1

private noncomputable def labelFintype : Fintype GlobalLabels := inferInstance
attribute [local instance 2000] labelFintype

theorem modulus_value : CoprimeGuessTables.modulus primes=7239457225 := by
  decide +kernel

/-- The same 32 leaves count the weights on actual attained residues modulo
7,239,457,225, for ordered pairs of product one modulo that modulus. -/
theorem global_histogram (f : ℕ→ℕ) :
    (∑ s : GlobalLabels,f (weight 1 s.val))=compressed [5,7,11,13,17] f := by
  have dist : Function.Injective primes := by decide +kernel
  let e := CoprimeGuessTables.allowedEquiv primes dist 1
  have local_table (s : GlobalLabels) : f (weight 1 s.val)=f (labelWeight (e s)) :=
    congrArg f (CoprimeGuessTables.weight_equiv primes dist 1 s)
  simp_rw [local_table]
  exact (e.sum_comp (fun x => f (labelWeight x))).trans (histogram f)

attribute [local irreducible] CoprimeGuessTables.modulus Fintype.card labelFintype score

private theorem count_of_ones {α : Type*} [Fintype α] {k : ℕ}
    (h : (∑ _ : α, (1:ℕ))=k) : Fintype.card α=k := by simpa using h

theorem label_count : Fintype.card GlobalLabels=41767264 :=
  count_of_ones (α:=GlobalLabels) ((global_histogram (fun _ => 1)).trans totals.1)

theorem total_weight : (∑ x : GlobalLabels,weight 1 x.val)=3920716800 :=
  (global_histogram id).trans totals.2.1

private theorem pair_overlap : overlap (fun x : GlobalLabels => weight 1 x.val)=76894261517673600 := by
  have inner (x : GlobalLabels) := global_histogram (min (weight 1 x.val))
  unfold overlap
  simp_rw [inner]
  exact (global_histogram (fun w => compressed [5,7,11,13,17] (min w))).trans totals.2.2

/-- Minimum possible one-based weighted rank sum, including the successful guess. -/
private theorem optimal_from_histogram {α : Type*} [Fintype α] (w : α→ℕ)
    (one : (∑ i,w i)=3920716800) (two : overlap w=76894261517673600) :
    IsLeast (Set.range (score w)) 38447132719195200 :=
  least_of_overlap w ((congrArg₂ Nat.add one two).trans
    (by decide +kernel : 3920716800+76894261517673600=2*38447132719195200))

theorem optimal_mass : IsLeast (Set.range (@score GlobalLabels labelFintype (fun s => weight 1 s.val)))
    38447132719195200 :=
  @optimal_from_histogram GlobalLabels labelFintype (fun s => weight 1 s.val) total_weight pair_overlap

/-- Exact expected guesses for optimal fixed ordering, when every ordered
residue pair with product one has the same probability. -/
noncomputable def mean (e : Fin (Fintype.card GlobalLabels) ≃ GlobalLabels) : ℚ :=
  (score (fun s : GlobalLabels => weight 1 s.val) e:ℚ)/((∑ x : GlobalLabels,weight 1 x.val : ℕ):ℚ)

theorem optimum : IsLeast (Set.range mean) (470695147/48) := by
  obtain ⟨⟨e,hit⟩,least⟩ := optimal_mass
  have expected : (470695147/48:ℚ)=38447132719195200/3920716800 := by norm_num
  rw [expected]
  constructor
  · refine ⟨e,?_⟩
    unfold mean
    rw [total_weight,hit]
    norm_num
  · rintro _ ⟨order,rfl⟩
    have le := least ⟨order,rfl⟩
    unfold mean
    rw [total_weight]
    norm_num only [Nat.cast_ofNat]
    have bound : (38447132719195200:ℚ)≤(score (fun s : GlobalLabels => weight 1 s.val) order : ℚ) := by exact_mod_cast le
    exact expected.le.trans (div_le_div_of_nonneg_right bound (by norm_num : (0:ℚ)≤3920716800))

/-- Fraction of the uniform random-order mean saved by optimal ordering. -/
theorem relative_saving :
    1-(470695147/48:ℚ)/((Fintype.card GlobalLabels+1:ℚ)/2)=531719213/1002414360 := by
  have cards : (Fintype.card GlobalLabels:ℚ)=41767264 := Nat.cast_inj.mpr label_count
  rw [cards]
  norm_num

end PrimeFactors.FiveSquareGuessRanks
