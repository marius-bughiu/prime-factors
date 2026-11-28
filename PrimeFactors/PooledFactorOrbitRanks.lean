import PrimeFactors.FactorOrbitGuessRanks
import PrimeFactors.SquareFiberMoments

/-! The effect of optimizing a list of complementary modular factor pairs
when the product is observed. The input population consists of two uniform
group elements; either factor residue is an acceptable answer. -/
namespace PrimeFactors.PooledFactorOrbitRanks

open Finset FactorOrbitGuessRanks
open scoped Classical
variable (G : Type*) [CommGroup G] [Fintype G]

private theorem moments :
    (∑ n : G, (fixed n:ℚ))=Fintype.card G ∧
    (∑ n : G, (fixed n:ℚ)^2)=(Fintype.card G:ℚ)*fixed (1:G) := by
  exact ⟨by exact_mod_cast (SquareFiberMoments.first (G:=G)),
    by exact_mod_cast (SquareFiberMoments.second (G:=G))⟩

/-- Mean over the possible known products of the cost of an optimal
orbit list. Every product has equally many ordered preimages. -/
theorem optimal_mean :
    (∑ n : G,optimum n)/(Fintype.card G:ℚ)=
      (Fintype.card G:ℚ)/4+1/2+fixed (1:G)/(4*(Fintype.card G:ℚ)) := by
  obtain ⟨_,sq⟩ := moments G
  have size : (0:ℚ)<Fintype.card G := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card G)
  simp only [optimum,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,←sum_div,sq]
  field_simp
  ring

theorem random_mean :
    (∑ n : G,random n)/(Fintype.card G:ℚ)=(Fintype.card G:ℚ)/4+3/4 := by
  obtain ⟨first,_⟩ := moments G
  have size : (0:ℚ)<Fintype.card G := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card G)
  simp only [random,←sum_div,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,first]
  field_simp
  ring

/-- Averaged over all products, ordering the actual unordered factor-pair
guesses optimally saves strictly less than one quarter of one guess. -/
theorem saving :
    (∑ n : G,(random n-optimum n))/(Fintype.card G:ℚ)=
      1/4-(fixed (1:G):ℚ)/(4*(Fintype.card G:ℚ)) ∧
    (∑ n : G,(random n-optimum n))/(Fintype.card G:ℚ)<1/4 := by
  have positive : 0<fixed (1:G) := by
    apply card_pos.mpr
    exact ⟨1,mem_filter.mpr ⟨mem_univ _,by simp⟩⟩
  have size : (0:ℚ)<Fintype.card G := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card G)
  rw [sum_sub_distrib,sub_div,optimal_mean,random_mean]
  constructor
  · ring
  · have extra : (0:ℚ)<fixed (1:G)/(4*(Fintype.card G:ℚ)) := by positivity
    linarith only [extra]

end PrimeFactors.PooledFactorOrbitRanks
