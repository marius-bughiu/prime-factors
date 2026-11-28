import PrimeFactors.FiveSquareFactorGuessing
import PrimeFactors.FiveSquareSumClueMoments
import PrimeFactors.SumClueOrbitRanks

/-! Guessing either prime's residue when the correct sum residue modulo
7,239,457,225 is supplied for free along with the public product. The
population consists of all pairs of distinct 1,024-bit primes whose product
has 2,048 bits. The prime-count transfer assumes the stated Dirichlet-GRH
endpoint estimates. -/

namespace PrimeFactors.FiveSquareActualSumClue

open Finset
open FiveSquarePolicy (U)
open FiveSquarePrimeSupply (Endpoints)
open FiveSquareAllPrimeRanks (actual uniform)
open FiveSquareFactorGuessing (T)
open private PrimeFactors.FiveSquareFactorGuessing.lift
  PrimeFactors.FiveSquareFactorGuessing.error PrimeFactors.FiveSquareFactorGuessing.uniform_by_product
  from PrimeFactors.FiveSquareFactorGuessing
open scoped Classical

set_option maxRecDepth 4096
attribute [local irreducible] CoprimeGuessTables.modulus Fintype.card

private theorem minimum_transfer {I : Type*} [Finite I] (f : I→U→U→ℕ)
    (sym : ∀ i a b, f i a b=f i b a) (bound : ∀ i a b, f i a b≤2^33)
    {center : ℝ} (best : IsLeast (Set.range fun i => uniform (PrimeFactors.FiveSquareFactorGuessing.lift (f i))) center)
    {li : ℕ→ℝ} (h : Endpoints li) :
    ∃ i : I, IsLeast (Set.range fun k => actual (PrimeFactors.FiveSquareFactorGuessing.lift (f k)))
      (actual (PrimeFactors.FiveSquareFactorGuessing.lift (f i))) ∧
      |actual (PrimeFactors.FiveSquareFactorGuessing.lift (f i))-center|≤1/(2:ℝ)^347 := by
  let orig (i : I) := uniform (PrimeFactors.FiveSquareFactorGuessing.lift (f i))
  let score (i : I) := actual (PrimeFactors.FiveSquareFactorGuessing.lift (f i))
  have err (i : I) : |score i-orig i|≤1/(2:ℝ)^347 :=
    PrimeFactors.FiveSquareFactorGuessing.error h (f i) (sym i) (bound i)
  obtain ⟨⟨p,hit⟩,floor⟩ := best
  letI : Nonempty I := ⟨p⟩
  letI := Fintype.ofFinite I
  obtain ⟨i,_,least⟩ := univ.exists_min_image score univ_nonempty
  have lower : center≤orig i := floor ⟨i,rfl⟩
  have upper : score p-center≤1/(2:ℝ)^347 := hit ▸ (abs_le.mp (err p)).2
  exact ⟨i,⟨⟨i,rfl⟩,fun v ⟨x,e⟩ => e ▸ least x (mem_univ x)⟩,abs_le.mpr
    ⟨(abs_le.mp (err i)).1.trans (sub_le_sub_left lower _),
      (sub_le_sub_right (least p (mem_univ p)) _).trans upper⟩⟩

/-- The public product selects a family of lists. Within that family the
supplied true sum residue selects a single list of complementary orbits. -/
abbrev Policy := ∀ n : U, SumClueOrbitRanks.Policy n

noncomputable def rank (policy : Policy) (a b : U) :=
  SumClueOrbitRanks.rank (policy (a*b)) a

noncomputable def primeMean (policy : Policy) :=
  actual (PrimeFactors.FiveSquareFactorGuessing.lift (rank policy))

private theorem rank_sym (policy : Policy) (a b : U) : rank policy a b=rank policy b a := by
  unfold rank
  rw [mul_comm b a]
  have h := SumClueOrbitRanks.rank_partner (policy (a*b)) a
  rw [mul_div_cancel_left] at h
  exact h.symm

private theorem card_units (i : Fintype U) : @Fintype.card U i=T := by
  apply Eq.trans _ FiveSquarePolicy.unit_count.1
  exact congrArg (@Fintype.card U) (Subsingleton.elim _ _)

private theorem rank_bound (policy : Policy) (a b : U) : rank policy a b≤2^33 :=
  (SumClueOrbitRanks.rank_bound (policy (a*b)) a).trans
    ((card_units _).trans_le (by decide : T≤2^33))

private theorem rank_row (policy : Policy) (u a : U) :
    rank policy a (a⁻¹*u)=SumClueOrbitRanks.rank (policy u) a :=
  congrArg (fun n => SumClueOrbitRanks.rank (policy n) a) (mul_inv_cancel_left a u)

private theorem uniform_policy (policy : Policy) :
    uniform (PrimeFactors.FiveSquareFactorGuessing.lift (rank policy))=
      (((∑ u : U,SumClueOrbitRanks.mean (policy u))/(T:ℚ):ℚ):ℝ) := by
  apply PrimeFactors.FiveSquareFactorGuessing.uniform_by_product
  intro u
  simp only [rank_row,SumClueOrbitRanks.mean,card_units]

/-- Exact mean number of guesses in the independent uniform unit model. -/
noncomputable abbrev center : ℝ := 95858834947/1960358400

private theorem pooled :
    (((∑ n : U,FiveSquareSumClueMoments.expected n)/(T:ℚ):ℚ):ℝ)=center := by
  have h := FiveSquareSumClueMoments.pooled
  rw [FiveSquarePolicy.unit_count.1] at h
  unfold T
  rw [h]
  norm_num [center]

private theorem best : IsLeast (Set.range fun e : Policy =>
    uniform (PrimeFactors.FiveSquareFactorGuessing.lift (rank e))) center := by
  let e : Policy := fun n => Classical.choose (FiveSquareSumClueMoments.optimal n).1
  have row (n : U) : SumClueOrbitRanks.mean (e n)=FiveSquareSumClueMoments.expected n :=
    Classical.choose_spec (FiveSquareSumClueMoments.optimal n).1
  constructor
  · exact ⟨e,(uniform_policy e).trans (by simpa only [row] using pooled)⟩
  · rintro _ ⟨policy,rfl⟩
    change center≤uniform (PrimeFactors.FiveSquareFactorGuessing.lift (rank policy))
    rw [uniform_policy,←pooled]
    exact_mod_cast div_le_div_of_nonneg_right (sum_le_sum (fun n _ =>
      (FiveSquareSumClueMoments.optimal n).2 ⟨policy n,rfl⟩)) (by norm_num : (0:ℚ)≤T)

/-- The minimum over all product-and-true-sum conditioned orderings on the
actual prime population. Each guess names one orbit and hits either factor's
residue. The measurement excludes the cost of obtaining the true sum. -/
theorem actual_optimum {li : ℕ→ℝ} (h : Endpoints li) :
    ∃ policy : Policy, IsLeast (Set.range primeMean) (primeMean policy) ∧
      |primeMean policy-center|≤1/(2:ℝ)^347 :=
  minimum_transfer rank rank_sym rank_bound best h

theorem within_thousandth {li : ℕ→ℝ} (h : Endpoints li) :
    ∃ policy : Policy, IsLeast (Set.range primeMean) (primeMean policy) ∧
      |primeMean policy-95858834947/1960358400|<1/1000 := by
  obtain ⟨p,minimal,close⟩ := actual_optimum h
  exact ⟨p,minimal,close.trans_lt (by norm_num)⟩

end PrimeFactors.FiveSquareActualSumClue
