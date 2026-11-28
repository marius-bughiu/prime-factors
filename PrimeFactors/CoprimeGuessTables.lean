import PrimeFactors.CombinedSumWeights
import PrimeFactors.PrimeSquareGuessAffinity
import PrimeFactors.HalfMassFive
import Mathlib.Data.ZMod.QuotientRing

/-! Guessing a sum label of a uniform ordered pair with a fixed product
residue. All counts refer to one complete modular residue space. -/

namespace PrimeFactors.CoprimeGuessTables

open Finset PrimeSquareSumWeights PrimeSquareExpectedRank
open scoped Classical
open private PrimeFactors.CombinedSumWeights.weight_first from PrimeFactors.CombinedSumWeights
open private PrimeFactors.HalfMassFive.positive_iff from PrimeFactors.HalfMassFive

abbrev Labels (m n : ℕ) := {s : ZMod m // AdmissibleSum (n : ZMod m) s}

theorem positive_iff {m n : ℕ} [NeZero m] (s : ZMod m) :
    0<weight n s ↔ AdmissibleSum (n : ZMod m) s := PrimeFactors.HalfMassFive.positive_iff s

instance {m n : ℕ} : Nonempty (Labels m n) :=
  ⟨⟨1+n,1,n,one_mul _,rfl⟩⟩

variable {ι : Type*} [Fintype ι]

/-- The number of ordered pairs with a fixed product and specified sum is
the product of the corresponding counts at any pairwise coprime moduli. -/
theorem weight_pi (m : ι → ℕ) (cop : Pairwise fun i j => (m i).Coprime (m j)) (n : ℕ)
    (s : ZMod (∏ i, m i)) :
    weight n s = ∏ i, weight n (ZMod.prodEquivPi m cop s i) := by
  let e := ZMod.prodEquivPi m cop
  simp only [PrimeFactors.CombinedSumWeights.weight_first]
  rw [←Nat.card_pi]
  apply Nat.card_congr
  refine Equiv.trans ?_ Equiv.subtypePiEquivPi
  apply e.toEquiv.subtypeEquiv
  intro x
  change x*(s-x)=n ↔ ∀ i, (e x i)*(e s i-e x i)=n
  rw [←e.injective.eq_iff,map_mul,map_sub,map_natCast]
  exact funext_iff

noncomputable def modulus (p : ι → ℕ) := ∏ i, (p i)^2

variable (p : ι → ℕ) [∀ i, Fact (p i).Prime]

instance : NeZero (modulus p) :=
  ⟨prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero 2 (Fact.out : (p i).Prime).ne_zero)⟩

omit [Fintype ι] in
private theorem coprime (distinct : Function.Injective p) :
    Pairwise fun i j => ((p i)^2).Coprime ((p j)^2) :=
  fun _ _ ne => (((Nat.coprime_primes Fact.out Fact.out).mpr (fun h => ne (distinct h))).pow_left 2).pow_right 2

/-- The attained global sum labels biject to the full Cartesian product of
the local attained labels, also when the index set is empty. -/
noncomputable def allowedEquiv (distinct : Function.Injective p) (n : ℕ) :
    Labels (modulus p) n ≃ (∀ i, Allowed (p i) n) := by
  let m := fun i => (p i)^2
  let e := ZMod.prodEquivPi m (coprime p distinct)
  refine Equiv.trans ?_ Equiv.subtypePiEquivPi
  apply e.toEquiv.subtypeEquiv
  intro s
  change AdmissibleSum (n : ZMod (modulus p)) s ↔ ∀ i, AdmissibleSum (n : ZMod (m i)) (e s i)
  rw [←positive_iff, weight_pi m (coprime p distinct) n s]
  simp_rw [←positive_iff,Nat.pos_iff_ne_zero]
  simp only [prod_ne_zero_iff,mem_univ,true_implies]
  rfl

theorem weight_equiv (distinct : Function.Injective p) (n : ℕ) (s : Labels (modulus p) n) :
    weight n s.val = ∏ i, weight n ((allowedEquiv p distinct n s) i).val :=
  weight_pi (fun i => (p i)^2) (coprime p distinct) n s.val

/-- Reindex any statistic of a label and its weight, including a supplied
rank times weight, by the exact CRT equivalence. -/
theorem sum_equiv (distinct : Function.Injective p) (n : ℕ) (f : Labels (modulus p) n → ℕ → ℝ) :
    (∑ s, f s (weight n s.val)) = ∑ x : (∀ i, Allowed (p i) n),
       f ((allowedEquiv p distinct n).symm x) (∏ i, weight n (x i).val) := by
  let e := allowedEquiv p distinct n
  refine Eq.trans ?_ (e.sum_comp (fun x => f (e.symm x) (∏ i, weight n (x i).val)))
  apply sum_congr rfl
  intro s _
  simp only [e,Equiv.symm_apply_apply,weight_equiv p distinct n]

/-- Exact affinity on the actual attained residues of the product modulus. -/
theorem global_affinity (distinct : Function.Injective p) (n : ℕ)
    (odd : ∀ i, p i≠2) (unit : ∀ i, ¬p i∣n) (sq : ∀ i, IsSquare (n:ZMod (p i))) :
    IndependentGuessRanks.affinity (fun s : Labels (modulus p) n => (weight n s.val:ℝ)) =
      ∏ i, PrimeSquareGuessAffinity.affinity (p i) := by
  let localMass (x : ∀ i, Allowed (p i) n) : ℝ := ∏ i, (weight n (x i).val:ℝ)
  have total := sum_equiv p distinct n (fun _ k => (k:ℝ))
  have roots := sum_equiv p distinct n (fun _ k => Real.sqrt k)
  simp only [Nat.cast_prod] at total roots
  have card := Fintype.card_congr (allowedEquiv p distinct n)
  calc
    _ = IndependentGuessRanks.affinity localMass := by
      unfold IndependentGuessRanks.affinity IndependentGuessRanks.rootTotal IndependentGuessRanks.total
      rw [total,roots,card]
    _ = _ := PrimeSquareGuessAffinity.product_affinity p n odd unit sq

/-- Decreasing global weight order attains the independent-table rank bound
for a uniform ordered pair of residues with the stated fixed product. -/
theorem global_rank_bound (distinct : Function.Injective p) (n : ℕ)
    (odd : ∀ i, p i≠2) (unit : ∀ i, ¬p i∣n) (sq : ∀ i, IsSquare (n:ZMod (p i))) :
    let w := fun s : Labels (modulus p) n => (weight n s.val:ℝ)
    ∃ e : Fin (Fintype.card (Labels (modulus p) n)) ≃ Labels (modulus p) n,
      Antitone (w ∘ e) ∧ 2*IndependentGuessRanks.meanRank w e ≤
        1+(Fintype.card (Labels (modulus p) n):ℝ)*(∏ i, PrimeSquareGuessAffinity.affinity (p i)) := by
  dsimp only
  rw [←global_affinity p distinct n odd unit sq]
  apply IndependentGuessRanks.exists_rank_bound
  · exact fun _ => Nat.cast_nonneg _
  · apply sum_pos
    · exact fun s _ => by exact_mod_cast (positive_iff s.val).mpr s.property
    · exact univ_nonempty

end PrimeFactors.CoprimeGuessTables
