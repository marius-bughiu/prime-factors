import PrimeFactors.ExtendedModulusPrimeSupply
import PrimeFactors.FiveSquareAllPrimeRanks

/-! Transfer a bounded symmetric residue-pair statistic at any modulus
through 2^161 from uniform units to distinct full-width prime products.
The analytic hypotheses are the published prime-count inequalities for
the particular modulus being read. -/
namespace PrimeFactors.ExtendedProductCosts

open Finset
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open PrimeProductRegion (K)
open PrimeResidueRankTransfer (cell)
open private PrimeFactors.FiveSquareAllPrimeRanks.actual_weighted
  PrimeFactors.FiveSquareAllPrimeRanks.reweight PrimeFactors.FiveSquareAllPrimeRanks.raw
  from PrimeFactors.FiveSquareAllPrimeRanks
open scoped Classical
set_option maxRecDepth 4096
set_option exponentiation.threshold 4096

variable {d : ℕ} [NeZero d]

private noncomputable def lift (f : (ZMod d)ˣ→(ZMod d)ˣ→ℕ) (a b : ZMod d) :=
  if ha : IsUnit a then if hb : IsUnit b then f ha.unit hb.unit else 0 else 0

private theorem lift_units (f : (ZMod d)ˣ→(ZMod d)ˣ→ℕ) (a b : (ZMod d)ˣ) :
    lift f a b=f a b := by
  simp only [lift,dif_pos a.isUnit,dif_pos b.isUnit,IsUnit.unit_of_val_units]

private theorem lift_sym {f : (ZMod d)ˣ→(ZMod d)ˣ→ℕ} (sym : ∀ a b,f a b=f b a)
    (a b : ZMod d) : lift f a b=lift f b a := by
  by_cases x : IsUnit a <;> by_cases y : IsUnit b <;> simp [lift,x,y,sym]

noncomputable def actual (f : (ZMod d)ˣ→(ZMod d)ˣ→ℕ) := FiveSquareAllPrimeRanks.actual (lift f)

noncomputable def uniform (f : (ZMod d)ˣ→(ZMod d)ˣ→ℕ) : ℝ :=
  ((∑ v : (ZMod d)ˣ×(ZMod d)ˣ,f v.1 v.2:ℕ):ℝ)/Fintype.card ((ZMod d)ˣ×(ZMod d)ˣ)

private theorem unit_of_prime (cap : d≤2^161) {p : ℕ} (lo : X<p) (prime : p.Prime) :
    IsUnit (p:ZMod d) := by
  apply (ZMod.isUnit_iff_coprime p d).mpr
  exact prime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (NeZero.ne d))
    (cap.trans_lt ((by decide +kernel : 2^161≤X).trans_lt lo)))

/-- The same bound is valid simultaneously for every symmetric cost
in the indicated range, including a policy chosen with knowledge of
the population frequencies. -/
theorem close (low : 3≤d) (cap : d≤2^161) {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints d li) (f : (ZMod d)ˣ→(ZMod d)ˣ→ℕ)
    (sym : ∀ a b,f a b=f b a) {C : ℕ} (bound : ∀ a b,f a b≤C) :
    |actual f-uniform f|≤(C:ℝ)/(2:ℝ)^146 := by
  obtain ⟨l,u,lp,scale,cells⟩ := ExtendedModulusPrimeSupply.cell_bounds low cap h
  let w (v : (ZMod d)ˣ×(ZMod d)ˣ) := (cell X B K ((v.1:ZMod d),(v.2:ZMod d)):ℝ)
  let c (v : (ZMod d)ˣ×(ZMod d)ˣ) := (f v.1 v.2:ℝ)
  have weights (v) : (l:ℝ)≤w v ∧ w v≤(u:ℝ) :=
    ⟨Nat.cast_le.mpr (cells v).1,Nat.cast_le.mpr (cells v).2⟩
  have costs (v) : 0≤c v ∧ c v≤(C:ℝ) := ⟨Nat.cast_nonneg _,Nat.cast_le.mpr (bound _ _)⟩
  have err := PrimeFactors.FiveSquareAllPrimeRanks.reweight w c
    (by exact_mod_cast lp : 0<(l:ℝ)) (by positivity : (0:ℝ)<2^146)
    (by exact_mod_cast scale : (2:ℝ)^146*u≤((2:ℝ)^146+1)*l) weights costs
  rw [actual,PrimeFactors.FiveSquareAllPrimeRanks.actual_weighted (lift f) (lift_sym sym) (unit_of_prime cap),uniform,Nat.cast_sum]
  simpa only [w,c,PrimeFactors.FiveSquareAllPrimeRanks.raw,lift_units] using err

end PrimeFactors.ExtendedProductCosts
