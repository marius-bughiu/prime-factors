import PrimeFactors.WithinResidueSearchFloor
import PrimeFactors.SixSquareAuxiliarySieve

/-! Exact square-test counts for the existing score order after filtering
on the six additional prime squares. The true factor sum serves only to
measure the prefix ending at success. -/

namespace PrimeFactors.SixSquareScoreVisits

open Finset WithinResidueSearchFloor SixSquareAuxiliarySieve
open MixedPrefixSample (eligible)
open FullRangeResidueEstimates (X)
open WideResiduePrimeSupply (B)
open private PrimeFactors.WithinResidueSearchFloor.rare_of_long
  PrimeFactors.WithinResidueSearchFloor.eligible_hit from PrimeFactors.WithinResidueSearchFloor
open scoped Classical

set_option exponentiation.threshold 4096
attribute [local irreducible] eligible

/-- Candidates through the successful score, restricted by an additional
sum-residue condition determined by the product alone. -/
noncomputable def visits (v : ℕ×ℕ) : Finset ℕ :=
  (scoreVisits v).filter (fun t => (t:ZMod L)∈A (v.1*v.2))

private theorem coprime_small {v : ℕ×ℕ} (hv : v∈eligible) {d : ℕ} (pos : 0<d) (small : d<X) :
    (v.1*v.2).Coprime d := by
  obtain ⟨pl,pq,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp hv
  have left := pp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt pos (small.trans_le pl))
  have right := qp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt pos ((small.trans_le pl).trans pq))
  exact Nat.coprime_mul_iff_left.mpr ⟨left,right⟩

theorem product_coprime {v : ℕ×ℕ} (hv : v∈eligible) : (v.1*v.2).Coprime L :=
  coprime_small hv (NeZero.pos _) (by rw [value]; decide +kernel)

theorem mod_five {v : ℕ×ℕ} (hv : v∈eligible) : (v.1*v.2)%5≠0 := by
  have cop := coprime_small hv (by decide : 0<5) (by decide +kernel : 5<X)
  exact fun hz => Nat.prime_five.coprime_iff_not_dvd.mp cop.symm (Nat.dvd_of_mod_eq_zero hz)

theorem covers {v : ℕ×ℕ} (hv : v∈eligible) :
    WithinResidueSearchFloor.Covers (visits v) (100*L) (low v) (target v) := by
  obtain ⟨cap,passes⟩ := PrimeFactors.WithinResidueSearchFloor.eligible_hit hv
  intro t lo hi same
  have h : Nat.ModEq (100*L) t (target v) := same
  have m100 := h.of_dvd (dvd_mul_right 100 L)
  have aux := h.of_dvd (dvd_mul_left L 100)
  have keep : t∈scoreVisits v := score_covers cap passes t lo hi m100
  have sameAux : (t:ZMod L)=(target v:ZMod L) := (ZMod.natCast_eq_natCast_iff ..).mpr aux
  exact mem_filter.mpr ⟨keep,sameAux ▸ true_sum v.1 v.2⟩

private theorem restrict_unique {S : Finset ℕ} {p q : ℕ→Prop} [DecidablePred p] [DecidablePred q]
    {x : ℕ} (old : S.filter p={x}) (pass : q x) : (S.filter q).filter p={x} := by
  ext t
  have h := Finset.ext_iff.mp old t
  simp only [mem_filter,mem_singleton] at h ⊢
  constructor
  · rintro ⟨⟨inside,_⟩,test⟩
    exact h.mp ⟨inside,test⟩
  · rintro rfl
    obtain ⟨inside,test⟩ := h.mpr rfl
    exact ⟨⟨inside,pass⟩,test⟩

/-- The successful discriminant square is preserved, and its sum is
the unique verified hit in the filtered prefix. -/
theorem unique_hit {v : ℕ×ℕ} (hv : v∈eligible) :
    (visits v).filter (fun t => IsSquare (t^2-4*(v.1*v.2)))={target v} := by
  obtain ⟨pl,pq,qu,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp hv
  have top : v.2<2*X := (by decide +kernel : B=2*X) ▸ qu
  exact restrict_unique (ScoreSumOrder.unique_hit (by decide +kernel : 3≤X) pl pq top pp qp)
    (true_sum v.1 v.2)

theorem period_bound : 100*L<2^47 := by rw [value]; decide +kernel

/-- Fewer than one pair in 2³⁵ requires fewer than 2⁸⁵³ exact square
tests in the filtered score order. This is unconditional on the stated
finite prime population. -/
theorem population_floor :
    2^35*(eligible.filter (fun v => (visits v).card<2^853)).card<eligible.card := by
  apply PrimeFactors.WithinResidueSearchFloor.rare_of_long
  intro v hv long
  have pos : 0<100*L := Nat.mul_pos (by decide) (NeZero.pos L)
  have floor := prefix_floor pos (by omega : low v≤target v) (covers hv)
  have fit : 2^853*(100*L)≤2^900 := (Nat.mul_le_mul_left (2^853) period_bound.le).trans_eq
    (by decide +kernel : (2:ℕ)^853*2^47=2^900)
  have count : 2^853≤(target v-low v)/(100*L) := (Nat.le_div_iff_mul_le pos).mpr (fit.trans (by omega))
  omega

end PrimeFactors.SixSquareScoreVisits
