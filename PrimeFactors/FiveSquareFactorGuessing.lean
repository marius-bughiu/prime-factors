import PrimeFactors.FiveSquarePolicy
import PrimeFactors.FactorOrbitGuessRanks
import PrimeFactors.PooledFactorOrbitRanks
import PrimeFactors.FiveSquareOrbitKernel

/-! Guessing either factor residue, once per complementary orbit, on the
population of all ordered-by-size pairs of distinct 1,024-bit primes with
2,048-bit product. The transfer from uniform residues uses the explicit
Dirichlet-GRH endpoint estimates in FiveSquarePrimeSupply.Endpoints. -/

namespace PrimeFactors.FiveSquareFactorGuessing

open Finset FactorOrbitGuessRanks
open FiveSquarePrimeSupply (m Endpoints)
open FiveSquarePolicy (U)
open FiveSquareAllPrimeRanks (actual uniform)
open scoped Classical

set_option maxRecDepth 4096
attribute [local irreducible] CoprimeGuessTables.modulus Fintype.card
open private PrimeFactors.FiveSquarePolicy.change_product PrimeFactors.FiveSquarePolicy.normalize
  from PrimeFactors.FiveSquarePolicy

variable {G : Type*} [CommGroup G] [Fintype G]

abbrev PolicyFor (G : Type*) [CommGroup G] [Fintype G] := ∀ n : G, Order n
abbrev Policy := PolicyFor U
abbrev T : ℕ := 3920716800

private noncomputable def rankAt (policy : PolicyFor G) (n a : G) := ((policy n) (label n a)).val+1

/-- One-based position of the actual orbit in the observed product's list. -/
noncomputable def rank (policy : PolicyFor G) (a b : G) : ℕ :=
  rankAt policy (a*b) a

private noncomputable def lift (f : U→U→ℕ) (a b : ZMod m) : ℕ :=
  if ha : IsUnit a then if hb : IsUnit b then f ha.unit hb.unit else 0 else 0

private theorem lift_units (f : U→U→ℕ) (a b : U) : lift f a b=f a b := by
  simp only [lift,dif_pos a.isUnit,dif_pos b.isUnit,IsUnit.unit_of_val_units]

private theorem lift_sym {f : U→U→ℕ} (sym : ∀ a b,f a b=f b a) (a b : ZMod m) :
    lift f a b=lift f b a := by
  by_cases x : IsUnit a <;> by_cases y : IsUnit b <;> simp [lift,x,y,sym]

private theorem rank_sym (policy : PolicyFor G) (a b : G) : rank policy a b=rank policy b a := by
  unfold rank
  rw [mul_comm b a]
  have hits : label (a*b) a=label (a*b) b := (hit_iff ..).mpr (Or.inr (mul_div_cancel_right a b).symm)
  unfold rankAt
  rw [hits]

noncomputable def twiceRandom (a b : G) := Fintype.card (Label (a*b))+1

private theorem random_row (n : G) :
    (Fintype.card (Label n):ℚ)+1=2*random n := by
  have h : (2:ℚ)*Fintype.card (Label n)=Fintype.card G+fixed n := by exact_mod_cast count n
  unfold random
  linarith only [h]

/-- This doubled natural cost is the exact mean over all random orderings
for each fixed pair, before any averaging over primes. -/
theorem twice_random_target (a b : G) :
    (twiceRandom a b:ℚ)=2*uniformRank (label (a*b) a) := by
  rw [random_target]
  simpa only [twiceRandom,Nat.cast_add,Nat.cast_one] using random_row (a*b)

noncomputable def primeMean (policy : Policy) := actual (lift (rank policy))
noncomputable def primeRandom := actual (lift twiceRandom)/2

private theorem label_bound (n : G) : Fintype.card (Label n)≤Fintype.card G := by
  apply Fintype.card_le_of_surjective (label n)
  rintro ⟨s,a,h⟩
  exact ⟨a,Subtype.ext h⟩

private theorem rank_bound (policy : PolicyFor G) (a b : G) : rank policy a b≤Fintype.card G :=
  (Nat.succ_le_of_lt (Fin.isLt _)).trans (label_bound (a*b))

private theorem random_bound (a b : G) : twiceRandom a b≤Fintype.card G+1 :=
  Nat.add_le_add_right (label_bound (a*b)) 1

private theorem rank_row (policy : PolicyFor G) (n a : G) :
    rank policy a (a⁻¹*n)=rankAt policy n a := congrArg (fun u => rankAt policy u a) (mul_inv_cancel_left a n)

private theorem twice_row (n a : G) : (twiceRandom a (a⁻¹*n):ℚ)=2*random n := by
  simpa only [twiceRandom,mul_inv_cancel_left,Nat.cast_add,Nat.cast_one] using random_row n

private theorem uniform_by_product (f : U→U→ℕ) (g : U→ℚ)
    (row : ∀ u, g u=((∑ a : U, f a (a⁻¹*u) : ℕ):ℚ)/T) :
    uniform (lift f)=(((∑ n : U,g n)/(T:ℚ):ℚ):ℝ) := by
  unfold uniform
  simp only [lift_units]
  rw [PrimeFactors.FiveSquarePolicy.change_product f]
  exact PrimeFactors.FiveSquarePolicy.normalize FiveSquarePolicy.unit_count.1 _ _ row

private theorem uniform_policy (policy : Policy) :
    uniform (lift (rank policy))=(((∑ n : U,mean n (policy n))/(T:ℚ):ℚ):ℝ) := by
  apply uniform_by_product
  intro n
  simp only [rank_row,rankAt,mean,FiveSquarePolicy.unit_count.1,T]

private theorem uniform_random :
    uniform (lift twiceRandom)=(((2*(∑ n : U,random n))/(T:ℚ):ℚ):ℝ) := by
  rw [mul_sum]
  apply uniform_by_product
  intro n
  push_cast only [Nat.cast_sum]
  simp only [twice_row,sum_const,card_univ,nsmul_eq_mul,FiveSquarePolicy.unit_count.1,T]
  ring


private theorem error {li : ℕ→ℝ} (h : Endpoints li) (f : U→U→ℕ)
    (sym : ∀ a b,f a b=f b a) (bound : ∀ a b,f a b≤2^33) :
    |actual (lift f)-uniform (lift f)|≤1/(2:ℝ)^347 := by
  have lim := FiveSquareAllPrimeRanks.every_cost_bound h _ (lift_sym sym)
    (fun a b => (lift_units f a b).trans_le (bound a b))
  exact lim.trans (by norm_num [FiveSquarePrimeSupply.F])

private theorem policy_error {li : ℕ→ℝ} (h : Endpoints li) (policy : Policy) :
    |primeMean policy-uniform (lift (rank policy))|≤1/(2:ℝ)^347 :=
  error h (rank policy) (rank_sym policy) (fun a b =>
    (rank_bound policy a b).trans (FiveSquarePolicy.unit_count.1.trans_le (by decide : T≤2^33)))

private theorem random_error {li : ℕ→ℝ} (h : Endpoints li) :
    |actual (lift twiceRandom)-uniform (lift twiceRandom)|≤1/(2:ℝ)^347 :=
  error h twiceRandom (fun a b => by rw [twiceRandom,twiceRandom,mul_comm a b])
    (fun a b => (random_bound a b).trans (by rw [FiveSquarePolicy.unit_count.1]; decide))

/-- Uniform-unit centers, in guesses per prime pair. -/
noncomputable abbrev optimalCenter : ℝ := (T:ℝ)/4+1/2+32/(4*T)
noncomputable abbrev randomCenter : ℝ := (T:ℝ)/4+3/4

private theorem centers :
    (((∑ n : U,optimum n)/(T:ℚ):ℚ):ℝ)=optimalCenter ∧
      (((∑ n : U,random n)/(T:ℚ):ℚ):ℝ)=randomCenter := by
  have rootCount : fixed (1:U)=32 := FiveSquareOrbitKernel.count
  have a := PooledFactorOrbitRanks.optimal_mean U
  have b := PooledFactorOrbitRanks.random_mean U
  rw [FiveSquarePolicy.unit_count.1,rootCount] at a
  rw [FiveSquarePolicy.unit_count.1] at b
  unfold T
  constructor
  · rw [a]
    norm_num [optimalCenter,T]
  · rw [b]
    norm_num [randomCenter,T]

private theorem uniform_lower (policy : Policy) :
    optimalCenter≤uniform (lift (rank policy)) := by
  rw [uniform_policy,←centers.1]
  exact_mod_cast div_le_div_of_nonneg_right (sum_le_sum (fun n _ =>
    (optimal n).2 ⟨policy n,rfl⟩)) (by norm_num : (0:ℚ)≤T)

private theorem uniform_attains : ∃ policy : Policy, (∀ n, mean n (policy n)=optimum n) ∧
    uniform (lift (rank policy))=optimalCenter := by
  let policy : Policy := fun n => Classical.choose (optimal n).1
  have each (n : U) : mean n (policy n)=optimum n := Classical.choose_spec (optimal n).1
  exact ⟨policy,each,by rw [uniform_policy]; simpa only [each] using centers.1⟩

/-- Mean for uniformly random order of the orbits of each observed product. -/
theorem actual_random {li : ℕ→ℝ} (h : Endpoints li) :
    |primeRandom-randomCenter|≤1/(2:ℝ)^348 := by
  have center : uniform (lift twiceRandom)=2*randomCenter := by
    rw [uniform_random,mul_div_assoc,Rat.cast_mul,Rat.cast_ofNat,centers.2]
  have e := abs_le.mp (random_error h)
  rw [center] at e
  unfold primeRandom
  apply abs_le.mpr
  constructor <;> linarith only [e.1,e.2]

/-- Existence of a modularly optimal family achieving the modular center
also on the prime population up to the stated endpoint error. -/
theorem attaining_family {li : ℕ→ℝ} (h : Endpoints li) :
    ∃ policy : Policy, (∀ n, mean n (policy n)=optimum n) ∧
      |primeMean policy-optimalCenter|≤1/(2:ℝ)^347 := by
  obtain ⟨e,each,eq⟩ := uniform_attains
  exact ⟨e,each,eq ▸ policy_error h e⟩

/-- A family minimizing the actual prime-population mean exists. Its
mean differs from the uniform optimum by at most the transfer error. -/
theorem actual_optimum {li : ℕ→ℝ} (h : Endpoints li) :
    ∃ policy : Policy, IsLeast (Set.range primeMean) (primeMean policy) ∧
      |primeMean policy-optimalCenter|≤1/(2:ℝ)^347 := by
  obtain ⟨p,_,close⟩ := attaining_family h
  letI : Nonempty Policy := ⟨p⟩
  obtain ⟨e,_,le⟩ := univ.exists_min_image primeMean univ_nonempty
  have ep := le p (mem_univ p)
  have low := (abs_le.mp (policy_error h e)).1
  have floor := uniform_lower e
  exact ⟨e,⟨⟨e,rfl⟩,fun y ⟨q,eq⟩ => eq ▸ le q (mem_univ q)⟩,
    abs_le.mpr ⟨low.trans (sub_le_sub_left floor _),(sub_le_sub_right ep _).trans (abs_le.mp close).2⟩⟩

/-- No product-conditioned family of orbit orders can save one quarter
of a guess per prime pair in this population, relative to random order. -/
theorem saved_lt_quarter {li : ℕ→ℝ} (h : Endpoints li) (policy : Policy) :
    primeRandom-primeMean policy<1/4 := by
  have a := (abs_le.mp (actual_random h)).2
  have b := (abs_le.mp (policy_error h policy)).1
  have c := uniform_lower policy
  have gap : randomCenter-optimalCenter+(1/(2:ℝ)^348+1/(2:ℝ)^347)<1/4 := by
    norm_num [randomCenter,optimalCenter,T]
  have combine {r s b u t e f g : ℝ} (one : r-s≤e) (two : -f≤b-u) (three : t≤u)
      (four : s-t+(e+f)<g) : r-b<g := by linarith
  exact combine a b c gap

end PrimeFactors.FiveSquareFactorGuessing
