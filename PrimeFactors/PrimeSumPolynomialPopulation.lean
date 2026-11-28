import PrimeFactors.SquareRootPhasePopulation
import PrimeFactors.PrimeSumPolynomialGrid

/-! A symmetric relation on product and sum has two ordered witnesses for
each hit among sorted pairs of distinct primes. The population denominator
uses elementary finite prime-count estimates. -/

namespace PrimeFactors.PrimeSumPolynomialPopulation

open Finset MixedPrefixSample

set_option exponentiation.threshold 2048

/-- The full ordered grid, including the diagonal. -/
noncomputable def grid (A : Finset ℕ) (R : ℕ → ℕ → Prop) : Finset (ℕ × ℕ) := by
  classical exact (A ×ˢ A).filter fun z => R (z.1*z.2) (z.1+z.2)

private theorem mem_grid {A : Finset ℕ} {R : ℕ → ℕ → Prop} {z : ℕ × ℕ} :
    z∈grid A R ↔ z∈A×ˢA ∧ R (z.1*z.2) (z.1+z.2) := by
  classical simp only [grid,mem_filter]

/-- The eligible population counts each pair of distinct primes once. -/
noncomputable def hits (R : ℕ → ℕ → Prop) : Finset (ℕ × ℕ) := by
  classical exact eligible.filter fun z => R (z.1*z.2) (z.1+z.2)

attribute [local irreducible] eligible primes

private theorem hit_data {R : ℕ → ℕ → Prop} {z : ℕ × ℕ} (mem : z∈hits R) :
    z.1∈primes ∧ z.2∈primes ∧ z.1<z.2 ∧ R (z.1*z.2) (z.1+z.2) := by
  classical
  rw [hits,mem_filter] at mem
  obtain ⟨m,h⟩ := mem
  rw [eligible,sample,mem_filter] at m
  obtain ⟨ord,lt⟩ := m
  obtain ⟨hp,hq,_⟩ := mem_ordered.mp ord
  exact ⟨hp,hq,lt,h⟩

attribute [local irreducible] hits

/-- Reversing each hit gives a second ordered root, disjoint from every
sorted hit. Diagonal roots in the grid may also occur. -/
theorem twice_hits (R : ℕ → ℕ → Prop) :
    2*(hits R).card≤(grid primes R).card := by
  classical
  let flip := (Equiv.prodComm ℕ ℕ).toEmbedding
  have dis : Disjoint (hits R) ((hits R).map flip) := by
    apply disjoint_left.mpr
    intro z hz hz'
    obtain ⟨w,hw,rfl⟩ := mem_map.mp hz'
    have fwd := (hit_data hw).2.2.1
    have rev : w.2<w.1 := (hit_data hz).2.2.1
    omega
  have sub : hits R ∪ (hits R).map flip ⊆ grid primes R := by
    intro z hz
    rcases mem_union.mp hz with m|m
    · obtain ⟨hp,hq,_,rel⟩ := hit_data m
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hp,hq⟩,rel⟩
    · obtain ⟨w,hw,rfl⟩ := mem_map.mp m
      obtain ⟨hp,hq,_,rel⟩ := hit_data hw
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hq,hp⟩,by
        change R (w.2*w.1) (w.2+w.1)
        rwa [mul_comm,add_comm]⟩
  simpa only [card_union_of_disjoint dis,card_map,two_mul] using card_le_card sub

/-- Population transfer for any ordered-grid root bound of the form 2d|A|.
The probability is over all eligible products of distinct 1,024-bit primes. -/
theorem fraction (R : ℕ → ℕ → Prop) {d : ℕ} (pos : 0<d)
    (bound : (grid primes R).card≤2*d*primes.card) :
    2^1007*(hits R).card < d*eligible.card := by
  have per : (hits R).card ≤ d*primes.card := by
    have h : 2*(hits R).card≤2*(d*primes.card) := by
      simpa only [Nat.mul_assoc] using (twice_hits R).trans bound
    omega
  have norm : X*(hits R).card < 41056*(d*eligible.card) := by
    calc
      _ ≤ X*(d*primes.card) := Nat.mul_le_mul_left _ per
      _ = (X*primes.card)*d := by ac_rfl
      _ < (41056*eligible.card)*d := Nat.mul_lt_mul_of_pos_right SquareRootPhasePopulation.marginal pos
      _ = _ := by ac_rfl
  have room : 41056*2^1007 ≤ X := by decide +kernel
  apply Nat.lt_of_mul_lt_mul_left (a:=41056)
  simpa only [Nat.mul_assoc] using (Nat.mul_le_mul_right (hits R).card room).trans_lt norm

/-- With a degree cap of 2^k, the failed coverage exponent is 1007−k.
Degree zero is included in the cap. -/
theorem budget (R : ℕ → ℕ → Prop) {k d : ℕ} (limit : k≤1007) (cap : d≤2^k)
    (bound : (grid primes R).card≤2*d*primes.card) :
    2^(1007-k)*(hits R).card < eligible.card := by
  have relaxed := bound.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 cap))
  have f := fraction R (d:=2^k) (by positivity) relaxed
  have eq : 2^1007 = 2^k*2^(1007-k) := by
    rw [←pow_add, Nat.add_sub_of_le limit]
  rw [eq,Nat.mul_assoc] at f
  exact Nat.lt_of_mul_lt_mul_left f

/-- This single rational polynomial is fixed for the entire population.
The zero polynomial is excluded. -/
noncomputable abbrev zeros (F : MvPolynomial (Fin 2) ℚ) :=
  hits fun n s => MvPolynomial.eval ![(n:ℚ),(s:ℚ)] F=0

/-- A fixed polynomial of total degree at most 2^k can vanish on fewer
than one in 2^(1007−k) of the eligible prime pairs. -/
theorem polynomial_budget (F : MvPolynomial (Fin 2) ℚ) (nz : F≠0) {k : ℕ}
    (limit : k≤1007) (cap : F.totalDegree≤2^k) :
    2^(1007-k)*(zeros F).card < eligible.card := by
  apply budget _ limit cap
  apply le_trans _ (PrimeSumPolynomialGrid.nat_grid_bound primes F nz)
  apply card_le_card
  intro z hz
  exact mem_filter.mpr (mem_grid.mp hz)

/-- Even allowing degree 2^128 yields coverage below one in 2^879.
For degree at most 2^32 or 2^16, the exponents are 975 or 991. -/
theorem degree_examples (F : MvPolynomial (Fin 2) ℚ) (nz : F≠0) :
    (F.totalDegree≤2^128 → 2^879*(zeros F).card<eligible.card) ∧
    (F.totalDegree≤2^32 → 2^975*(zeros F).card<eligible.card) ∧
    (F.totalDegree≤2^16 → 2^991*(zeros F).card<eligible.card) :=
  ⟨polynomial_budget F nz (k:=128) (by decide),
   polynomial_budget F nz (k:=32) (by decide),
   polynomial_budget F nz (k:=16) (by decide)⟩

end PrimeFactors.PrimeSumPolynomialPopulation
