import PrimeFactors.CircleMarkRationalProduct
import PrimeFactors.CircleMarkFirstTargetPopulation

/-! All rectangular aspect ratios may be chosen after the product is known.
A successful leaf somewhere in a rectangle of area at most B has ij ≤ B.
We count the union of these possibilities across actual prime products. -/
namespace PrimeFactors.CircleMarkRationalPopulation

open Finset MixedPrefixSample CircleMarkSmallTargetPopulation
open private PrimeFactors.CircleMarkSmallTargetPopulation.divisors
  PrimeFactors.CircleMarkSmallTargetPopulation.divisor_count from PrimeFactors.CircleMarkSmallTargetPopulation
open private PrimeFactors.CircleMarkSmallTargets.abs_sub_bound from PrimeFactors.CircleMarkSmallTargets
open private PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info from PrimeFactors.CyclotomicCoefficientProbePopulation
open private PrimeFactors.MixedPrefixSample.mem_primes from PrimeFactors.MixedPrefixSample

set_option exponentiation.threshold 8192
set_option maxRecDepth 8192
attribute [local irreducible] primes eligible

/-- Possible positive cells across every rectangle with the same area limit. -/
noncomputable def cells (K : ℕ) : Finset (ℕ×ℕ) :=
  ((Icc 1 (2^K)) ×ˢ (Icc 1 (2^K))).filter fun u => u.1*u.2≤2^K

theorem mem_cells {K i j : ℕ} : (i,j)∈cells K ↔ 0 < i ∧ 0 < j ∧ i*j ≤ 2^K := by
  simp only [cells,mem_filter,mem_product,mem_Icc]
  constructor
  · rintro ⟨⟨hi,hj⟩,cap⟩; exact ⟨hi.1,hj.1,cap⟩
  · rintro ⟨ip,jp,cap⟩
    exact ⟨⟨⟨ip,(Nat.le_mul_of_pos_right _ jp).trans cap⟩,
      ⟨jp,(Nat.le_mul_of_pos_left _ ip).trans cap⟩⟩,cap⟩

theorem cell_count (K : ℕ) : (cells K).card≤(K+1)*2^K := by
  let slabs (k : ℕ) := Icc 1 (2^(K-k)) ×ˢ Ico (2^k) (2^(k+1))
  have cover : cells K⊆(range (K+1)).biUnion slabs := by
    rintro ⟨i,j⟩ mem
    obtain ⟨ip,jp,cap⟩ := mem_cells.mp mem
    let k := j.log2
    have lo : 2^k≤j := (Nat.le_log2 jp.ne').mp le_rfl
    have hi : j<2^(k+1) := lt_of_not_ge fun bad => (by
      have := (Nat.le_log2 jp.ne').mpr bad
      dsimp [k] at *; omega)
    have lim : k≤K := by
      have := lo.trans ((Nat.le_mul_of_pos_left _ ip).trans cap)
      exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp this
    have eq : 2^(K-k)*2^k=2^K := by rw [←pow_add,Nat.sub_add_cancel lim]
    have bd : i*2^k≤2^(K-k)*2^k := by rw [eq]; exact (Nat.mul_le_mul_left i lo).trans cap
    exact mem_biUnion.mpr ⟨k,mem_range.mpr (by omega),mem_product.mpr
      ⟨mem_Icc.mpr ⟨ip,Nat.le_of_mul_le_mul_right bd (by positivity)⟩,mem_Ico.mpr ⟨lo,hi⟩⟩⟩
  apply (card_le_card cover).trans
  apply (card_biUnion_le_card_mul _ _ (2^K) _).trans_eq
  · simp
  · intro k hk
    change (Icc 1 (2^(K-k)) ×ˢ Ico (2^k) (2^(k+1)) : Finset (ℕ×ℕ)).card≤2^K
    rw [card_product,Nat.card_Icc,Nat.card_Ico,Nat.add_sub_cancel,pow_succ]
    rw [show 2^k*2-2^k=2^k by omega,←pow_add,Nat.sub_add_cancel (Nat.le_of_lt_succ (mem_range.mp hk))]

/-- The product and target are free to choose the most favorable cell. -/
noncomputable def successes (T : Finset ℕ) (C : Finset (ℕ×ℕ)) :=
  eligible.filter fun v => ∃ a∈T, ∃ u∈C, jacobiSym a (v.1*v.2)= -1 ∧
    ¬(v.1*v.2).Coprime (magnitude a u.1 u.2)

theorem actual_rectangles {T : Finset ℕ} {K p q : ℕ} :
    (p,q)∈successes T (cells K) ↔ (p,q)∈eligible ∧ ∃ a∈T, jacobiSym a (p*q)= -1 ∧
      ∃ H D : ℕ, H*D≤2^K ∧ ¬(p*q).Coprime (CircleMarkRationalProduct.product a H D) := by
  simp only [successes,mem_filter]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨a,atg,⟨i,j⟩,mem,neg,hit⟩
    obtain ⟨ip,jp,area⟩ := mem_cells.mp mem
    exact ⟨a,atg,neg,i,j,area,(CircleMarkRationalProduct.has_hit ..).mpr
      ⟨i,mem_Icc.mpr ⟨ip,le_rfl⟩,j,mem_Icc.mpr ⟨jp,le_rfl⟩,hit⟩⟩
  · rintro ⟨a,atg,neg,H,D,cap,hit⟩
    obtain ⟨i,hi,j,hj,leaf⟩ := (CircleMarkRationalProduct.has_hit ..).mp hit
    obtain ⟨ip,ib⟩ := mem_Icc.mp hi
    obtain ⟨jp,jb⟩ := mem_Icc.mp hj
    exact ⟨a,atg,(i,j),mem_cells.mpr ⟨ip,jp,(Nat.mul_le_mul ib jb).trans cap⟩,neg,leaf⟩

attribute [local irreducible] successes cells

private theorem small_value {a i j : ℕ} (cap : a≤A) (ilen : i≤2^1000) (jlen : j≤2^1000) :
    magnitude a i j<X^2 := by
  apply PrimeFactors.CircleMarkSmallTargets.abs_sub_bound (sq_nonneg _) (by positivity)
  · exact lt_of_le_of_lt (by exact_mod_cast Nat.pow_le_pow_left ilen 2) (by decide +kernel : ((2:ℤ)^1000)^2<((X^2:ℕ):ℤ))
  · exact lt_of_le_of_lt (by exact_mod_cast Nat.mul_le_mul cap (Nat.pow_le_pow_left jlen 2))
      (by decide +kernel : (A:ℤ)*((2:ℤ)^1000)^2<((X^2:ℕ):ℤ))

private theorem count (T : Finset ℕ) (C : Finset (ℕ×ℕ)) (targets : ∀ a∈T,a≤A)
    (shape : ∀ u∈C,0<u.2 ∧ u.1≤2^1000 ∧ u.2≤2^1000) :
    (successes T C).card≤(T.card*C.card)*primes.card := by
  classical
  let pool := (T ×ˢ C).biUnion fun t => PrimeFactors.CircleMarkSmallTargetPopulation.divisors (magnitude t.1 t.2.1 t.2.2)
  have size : pool.card≤T.card*C.card := by
    apply (card_biUnion_le_card_mul _ _ 1 (fun _ _ => PrimeFactors.CircleMarkSmallTargetPopulation.divisor_count _)).trans
    simp
  have incl : successes T C ⊆ CyclotomicCoefficientProbePopulation.hits pool := by
    intro v mem
    rw [successes, mem_filter] at mem
    obtain ⟨pair,a,atg,u,um,neg,hit⟩ := mem
    obtain ⟨p,q,_⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info pair
    obtain ⟨jp,ib,jb⟩ := shape u um
    have pos : 0<magnitude a u.1 u.2 := Int.natAbs_pos.mpr
      (CircleMarkSmallTargets.nonzero_component neg (Or.inr (by exact_mod_cast jp.ne')))
    have into {r : ℕ} (rm : r∈primes) (dv : r∣magnitude a u.1 u.2) : r∈pool :=
      mem_biUnion.mpr ⟨(a,u),mem_product.mpr ⟨atg,um⟩,
        mem_filter.mpr ⟨rm,pos,small_value (targets a atg) ib jb,dv⟩⟩
    apply CyclotomicCoefficientProbePopulation.mem_hits.mpr
    refine ⟨pair,?_⟩
    rw [Nat.coprime_mul_iff_left] at hit
    by_cases one : v.1.Coprime (magnitude a u.1 u.2)
    · have dv := ((PrimeFactors.MixedPrefixSample.mem_primes.mp q).2.coprime_iff_not_dvd.not).mp
          (fun two => hit ⟨one,two⟩)
      exact ⟨_,into q (Classical.not_not.mp dv),Or.inr (Or.inl rfl)⟩
    · have dv := ((PrimeFactors.MixedPrefixSample.mem_primes.mp p).2.coprime_iff_not_dvd.not).mp one
      exact ⟨_,into p (Classical.not_not.mp dv),Or.inl rfl⟩
  exact (card_le_card incl).trans ((CyclotomicCoefficientProbePopulation.count pool).trans
    (Nat.mul_le_mul_right _ size))

private theorem weight {c t d e m k : ℕ} (cost : c≤d*t)
    (marginal : X*t<41056*e) (fit : 41056*m*d≤k*X) (kp : 0<k) : m*c<k*e := by
  apply Nat.lt_of_mul_lt_mul_left (a:=41056)
  calc
    41056*(m*c) ≤ 41056*(m*(d*t)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ cost)
    _ = (41056*m*d)*t := by ring
    _ ≤ (k*X)*t := Nat.mul_le_mul_right _ fit
    _ = k*(X*t) := by ring
    _ < k*(41056*e) := Nat.mul_lt_mul_of_pos_left marginal kp
    _ = _ := by ring

theorem population (T : Finset ℕ) (K m k : ℕ) (targets : ∀ a∈T,a≤A) (bound : K≤1000)
    (fit : 41056*m*(T.card*((K+1)*2^K))≤k*X) (kp : 0<k) :
    m*(successes T (cells K)).card<k*eligible.card := by
  have shape (u : ℕ×ℕ) (mem : u∈cells K) : u.1 ∈ Icc 1 (2^K) ∧ u.2 ∈ Icc 1 (2^K) := by
    rw [cells, mem_filter] at mem
    exact mem_product.mp mem.1
  have hi : (2:ℕ)^K≤2^1000 := Nat.pow_le_pow_right (by decide) bound
  have base := count T (cells K) targets (fun u mem => by
    obtain ⟨i,j⟩ := shape u mem
    exact ⟨(mem_Icc.mp j).1,(mem_Icc.mp i).2.trans hi,(mem_Icc.mp j).2.trans hi⟩)
  exact weight (base.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left T.card (cell_count K))))
    SquareRootPhasePopulation.marginal fit kp

private theorem all_bound (B K m : ℕ) (bound : B≤A) (height : K≤1000)
    (fit : 41056*m*(B*((K+1)*2^K))≤X) :
    m*(successes (Icc 1 B) (cells K)).card<eligible.card := by
  have inputs : ∀ a∈Icc 1 B, a≤A := fun _ h => (mem_Icc.mp h).2.trans bound
  have cost : 41056*m*((Icc 1 B).card*((K+1)*2^K))≤1*X := by
    rw [Nat.card_Icc,Nat.add_sub_cancel,Nat.one_mul]
    exact fit
  exact (population (Icc 1 B) K m 1 inputs height cost (by decide)).trans_eq (Nat.one_mul _)

/-- Even a free selection of the target and of both rectangle dimensions is
allowed. Fewer than one in three eligible products succeeds at this area. -/
theorem all_targets : 3*(successes (Icc 1 A) (cells 975)).card<eligible.card := by
  exact all_bound A 975 3 le_rfl (by decide) (by decide +kernel)

/-- At the lower area the union of every possible aspect ratio still covers
fewer than one eligible pair in 2^76. -/
theorem area900 : 2^76*(successes (Icc 1 A) (cells 900)).card<eligible.card := by
  exact all_bound A 900 (2^76) le_rfl (by decide) (by decide +kernel)

theorem six_targets : 32*(successes CircleMarkFirstTarget.small (cells 994)).card<15*eligible.card := by
  apply population _ 994 32 15 _ (by decide) _ (by decide)
  · intro a m
    simp only [CircleMarkFirstTarget.small,mem_insert,mem_singleton] at m
    rcases m with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · rw [show CircleMarkFirstTarget.small.card=6 by decide]; decide +kernel

/-- Eligible products on which the least negative-Jacobi target succeeds for
some rectangle of the given area, with its shape allowed to depend on the input. -/
noncomputable def selected (K : ℕ) : Finset (ℕ×ℕ) := by
  classical
  exact eligible.filter fun v => ∃ a, CircleMarkFirstTarget.First (v.1*v.2) a ∧
    ∃ H D : ℕ, H*D≤2^K ∧ ¬(v.1*v.2).Coprime (CircleMarkRationalProduct.product a H D)

private theorem selected_cover (K : ℕ) : selected K ⊆
    successes CircleMarkFirstTarget.small (cells K) ∪ CircleMarkFirstTargetPopulation.population := by
  classical
  rintro ⟨p,q⟩ mem
  obtain ⟨pair,a,first,H,D,area,hit⟩ := mem_filter.mp mem
  by_cases late : 13<a
  · exact mem_union_right _ (CircleMarkFirstTargetPopulation.mem_late.mpr ⟨pair,a,first,late⟩)
  obtain ⟨pm,qm,_⟩ := PrimeFactors.CyclotomicCoefficientProbePopulation.pair_info pair
  have pp := (PrimeFactors.MixedPrefixSample.mem_primes.mp pm).2
  have qp := (PrimeFactors.MixedPrefixSample.mem_primes.mp qm).2
  have prime := CircleMarkFirstTarget.prime (pp.one_lt.trans_le (Nat.le_mul_of_pos_right _ qp.pos)) first
  have early : a≤13 := by omega
  have member : a∈CircleMarkFirstTarget.small := by
    interval_cases a <;> first | decide | norm_num at prime
  exact mem_union_left _ (actual_rectangles.mpr ⟨pair,a,member,first.1,H,D,area,hit⟩)

private theorem combine_shares {all early late found : ℕ} (pos : 0<all)
    (total : found≤early+late) (small : 32*early<15*all)
    (rare : |(late:ℝ)/all-1/64|≤1/(2:ℝ)^146) : 2*found<all := by
  have den : 0<(all:ℝ) := Nat.cast_pos.mpr pos
  have share := (abs_le.mp rare).2
  have late_bound : (late:ℝ)/all < 1/32 := by linarith
  have late_count := (div_lt_iff₀ den).mp late_bound
  have e : 32*(early:ℝ)<15*(all:ℝ) := by exact_mod_cast small
  have f : (found:ℝ)≤early+(late:ℝ) := by exact_mod_cast total
  exact_mod_cast (show 2*(found:ℝ)<all by linarith)

/-- The endpoint hypothesis for the six-prime character distribution is the
only analytic premise. On more than half of the products even an optimally
shaped rectangle of area at most 2^994 misses at the actual first target. -/
theorem selected_half {li : ℕ→ℝ}
    (h : ExtendedModulusPrimeSupply.Endpoints CircleMarkFirstTarget.modulus li) :
    2*(selected 994).card<eligible.card := by
  have total := (card_le_card (selected_cover 994)).trans (card_union_le ..)
  have pos : 0<eligible.card := by have := ChebyshevPrimeSample.eligible_count; omega
  exact combine_shares pos total six_targets (CircleMarkFirstTargetPopulation.close_ehp h)

end PrimeFactors.CircleMarkRationalPopulation
