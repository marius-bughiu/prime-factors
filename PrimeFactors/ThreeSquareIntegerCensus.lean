import PrimeFactors.FiniteThreeSquareTwists

/-! Cardinality of the ordered, signed integral representations of an arbitrary
nonnegative integer as three squares. Zero is counted once per coordinate. -/

namespace PrimeFactors.ThreeSquareIntegerCensus

open Finset FiniteThreeSquareTwists
open private PrimeFactors.ThreeSquareRadiusCounts.signs from PrimeFactors.ThreeSquareRadiusCounts

abbrev Triple := ℤ × ℤ × ℤ

def equation (n : ℕ) (v : Triple) : Prop :=
  v.1^2+v.2.1^2+v.2.2^2=(n:ℤ)

/-- Ordered signed solutions inside the integer cube [-n,n]³. -/
noncomputable def points (n : ℕ) : Finset Triple := by
  classical
  let I := Icc (-(n:ℤ)) (n:ℤ)
  exact (I ×ˢ (I ×ˢ I)).filter (equation n)

private theorem magnitude_eq (n : ℕ) (v : Triple) :
    equation n v ↔ v.1.natAbs^2+v.2.1.natAbs^2+v.2.2.natAbs^2=n := by
  unfold equation
  rw [←Int.ofNat_inj]
  push_cast
  simp only [Int.natCast_natAbs,sq_abs]

/-- Every integer solution lies in the cube, including at target zero. -/
@[simp] theorem mem_points (n : ℕ) (v : Triple) : v∈points n ↔ equation n v := by
  classical
  refine ⟨fun h => (mem_filter.mp h).2,?_⟩
  intro h
  have natural := (magnitude_eq n v).mp h
  have inside (a : ℤ) (ha : a.natAbs^2≤n) : a∈Icc (-(n:ℤ)) (n:ℤ) := by
    have bound : a.natAbs≤n := (Nat.le_self_pow (by decide : 2≠0) _).trans ha
    have cast : (a.natAbs:ℤ)≤(n:ℤ) := by exact_mod_cast bound
    exact mem_Icc.mpr (abs_le.mp (by simpa only [Int.natCast_natAbs] using cast))
  exact mem_filter.mpr ⟨mem_product.mpr ⟨inside _ (by omega),
    mem_product.mpr ⟨inside _ (by omega),inside _ (by omega)⟩⟩,h⟩

private noncomputable def signed (x : ℕ) : Finset ℤ := {(x:ℤ),-(x:ℤ)}

private theorem mem_signed (u : ℤ) (x : ℕ) : u∈signed x ↔ u.natAbs=x := by
  simp [signed,Int.natAbs_eq_iff]

private theorem card_signed (x : ℕ) :
    (signed x).card=PrimeFactors.ThreeSquareRadiusCounts.signs x := by
  by_cases zero : x=0
  · simp [signed,PrimeFactors.ThreeSquareRadiusCounts.signs,zero]
  · have ne : (x:ℤ)≠-(x:ℤ) := by omega
    simp [signed,PrimeFactors.ThreeSquareRadiusCounts.signs,zero,ne]

private theorem third {n x y z : ℕ} (eq : x^2+y^2+z^2=n) :
    (n-x^2-y^2).sqrt=z := by
  rw [show n-x^2-y^2=z^2 by omega,pow_two,Nat.sqrt_eq]

private def firstTwo (v : Triple) := (v.1.natAbs,v.2.1.natAbs)

private theorem fiber (n x y : ℕ) :
    ((points n).filter fun v => firstTwo v=(x,y)) =
      let z := (n-x^2-y^2).sqrt
      if x^2+y^2+z^2=n then signed x ×ˢ (signed y ×ˢ signed z) else ∅ := by
  let z := (n-x^2-y^2).sqrt
  change _ = if x^2+y^2+z^2=n then _ else _
  ext v
  simp only [mem_filter,mem_points,magnitude_eq,firstTwo,Prod.mk.injEq]
  by_cases good : x^2+y^2+z^2=n
  · rw [if_pos good]
    simp only [mem_product,mem_signed]
    constructor
    · rintro ⟨eq,ax,ay⟩
      rw [ax,ay] at eq
      exact ⟨ax,ay,(third eq).symm⟩
    · rintro ⟨ax,ay,az⟩
      exact ⟨by simpa only [ax,ay,az] using good,ax,ay⟩
  · rw [if_neg good]
    simp only [not_mem_empty,iff_false]
    rintro ⟨eq,ax,ay⟩
    rw [ax,ay] at eq
    exact good (by rwa [show z=v.2.2.natAbs from third eq])

/-- There is one possible last magnitude for each choice of the first two;
the nonempty fiber is the product of the three independent sign choices. -/
theorem card_points (n : ℕ) : (points n).card=r₃ n := by
  let S := range (n.sqrt+1)
  have bound : (points n : Set Triple).MapsTo firstTwo (S ×ˢ S : Finset (ℕ×ℕ)) := by
    intro v hv
    have row := (magnitude_eq n v).mp ((mem_points n v).mp hv)
    change (v.1.natAbs,v.2.1.natAbs)∈S ×ˢ S
    have hx : v.1.natAbs^2≤n := by omega
    have hy : v.2.1.natAbs^2≤n := by omega
    exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.le_sqrt'.mpr hx)),
      mem_range.mpr (Nat.lt_succ_of_le (Nat.le_sqrt'.mpr hy))⟩
  rw [card_eq_sum_card_fiberwise bound,sum_product]
  unfold r₃
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  rw [fiber]
  dsimp only
  split <;> simp [card_signed,mul_assoc]

/-- The same count on the unrestricted subtype of integer triples. -/
theorem signed_count (n : ℕ) : Nat.card {v : Triple // equation n v}=r₃ n := by
  let e := Equiv.subtypeEquivRight (fun v => (mem_points n v).symm)
  rw [←card_points,Nat.card_congr e,Nat.card_eq_finsetCard]

theorem zero : points 0={(0,0,0)} := by
  have hit : equation 0 (0 : Triple) := by norm_num [equation]
  simp [points,filter_singleton,hit]

theorem zero_count : r₃ 0=1 := by rw [←card_points,zero,card_singleton]

end PrimeFactors.ThreeSquareIntegerCensus
