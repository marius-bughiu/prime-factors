import PrimeFactors.DyadicPairSumWeight
import PrimeFactors.DyadicSquareValueCount
import PrimeFactors.LocalSumGuessCoverage

/-! Finite lists of sum residues for products congruent to one modulo eight.
The weights count ordered residue pairs of the given product. -/
namespace PrimeFactors.DyadicClusterMenu

open Finset PrimeSquareSumWeights DyadicSumPeak LocalSumGuessCoverage
open scoped Classical
open private PrimeFactors.DyadicSumPeak.doubles_disjoint PrimeFactors.DyadicSumPeak.square_of_double
  from PrimeFactors.DyadicSumPeak
open private PrimeFactors.DyadicPairSumWeight.gap_even PrimeFactors.DyadicPairSumWeight.gap_roots
  from PrimeFactors.DyadicPairSumWeight

/-- Scaled midpoint discriminants are indexed by distinct square values. -/
noncomputable def squares (j : ℕ) : Finset (ZMod (2^j)) := univ.filter IsSquare

/-- The sum residues associated with one scaled discriminant. -/
noncomputable def lane (t j N : ℕ) (d : ZMod (2^j)) :=
  doubles (2*t+j) (N+2^(2*t)*d.val)

/-- The list depends only on the product and the two chosen precisions. -/
noncomputable def menu (t j N : ℕ) := (squares j).biUnion (lane t j N)

private theorem lane_card {t j N : ℕ} (ht : 2≤t) (good : N%8=1) (d : ZMod (2^j)) :
    (lane t j N d).card=2 := by
  have level : 2*t+j=(2*t+j-1)+1 := by omega
  have div : 8∣2^(2*t)*d.val := dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega : 3≤2*t)) _
  unfold lane
  rw [level]
  apply doubles_count (by omega)
  rw [Nat.add_mod,good,Nat.mod_eq_zero_of_dvd div]

private theorem disjoint {t j N : ℕ} (ht : 2≤t) :
    Set.Pairwise (squares j : Set (ZMod (2^j))) (fun d f => Disjoint (lane t j N d) (lane t j N f)) := by
  intro d _ f _ ne
  unfold lane
  have level : 2*t+j=(2*t+j-1)+1 := by omega
  rw [level]
  apply PrimeFactors.DyadicSumPeak.doubles_disjoint (by omega)
  rw [←level,pow_add]
  intro same
  have reduced := (Nat.ModEq.add_left_cancel' N same).mul_left_cancel' (by positivity)
  exact ne (ZMod.val_injective _ (reduced.eq_of_lt_of_lt d.val_lt f.val_lt))

theorem lane_weight {t j N : ℕ} {d : ZMod (2^j)} {s : ZMod (2^(2*t+j))}
    (mem : s∈lane t j N d) : weight N s=roots j d*2^t := by
  obtain ⟨h,rfl,hh⟩ := (mem_filter.mp mem).2
  rw [DyadicSumPeak.midpoint,hh,Nat.cast_add,add_sub_cancel_left,scale,ZMod.natCast_zmod_val]

private theorem same_square {e : ℕ} (he : 2≤e) {x y : ZMod (2^e)}
    (same : 2*x=2*y) : x^2=y^2 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e≠0)
  exact PrimeFactors.DyadicSumPeak.square_of_double (by omega) same

/-- For an attained sum the discriminant divisibility detects membership
without choosing a square index from the list. -/
theorem mem_iff {t j N : ℕ} (ht : 2≤t) (h : ZMod (2^(2*t+j)))
    (hit : 0<weight N (2*h)) :
    2*h∈menu t j N ↔ (2:ZMod (2^(2*t+j)))^(2*t) ∣ h^2-N := by
  constructor
  · intro mem
    obtain ⟨d,_,hs⟩ := mem_biUnion.mp mem
    obtain ⟨y,hy,root⟩ := (mem_filter.mp hs).2
    refine ⟨(d.val:ℕ),?_⟩
    rw [same_square (by omega) hy,root]
    push_cast
    ring
  · rintro ⟨y,hy⟩
    let d : ZMod (2^j) := y.val
    have scaled : ((2^(2*t)*d.val:ℕ):ZMod (2^(2*t+j))) =
        (2:ZMod _)^(2*t)*y := by
      have shrink (q : ℕ) : 2^(2*t)*(q%2^j) ≡ 2^(2*t)*q [MOD 2^(2*t+j)] := by
        rw [pow_add]
        exact (Nat.mod_modEq q (2^j)).mul_left' _
      have con : 2^(2*t)*d.val ≡ 2^(2*t)*y.val [MOD 2^(2*t+j)] := by
        simpa only [d,ZMod.val_natCast] using shrink y.val
      have eq := (ZMod.natCast_eq_natCast_iff ..).mpr con
      simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,ZMod.natCast_zmod_val] using eq
    have w : weight N (2*h)=roots j d*2^t := by
      rw [DyadicSumPeak.midpoint,hy,←scaled,scale,ZMod.natCast_zmod_val]
    rw [w] at hit
    have pos := (Nat.mul_pos_iff_of_pos_right (by positivity : 0<2^t)).mp hit
    obtain ⟨⟨z,hz⟩⟩ := (Nat.card_pos_iff.mp pos).1
    apply mem_biUnion.mpr
    refine ⟨d,mem_filter.mpr ⟨mem_univ _,z,by simpa [pow_two] using hz.symm⟩,
      mem_filter.mpr ⟨mem_univ _,h,rfl,?_⟩⟩
    rw [Nat.cast_add,scaled]
    linear_combination hy

private theorem dvd_cast {m d n : ℕ} (div : d∣m) :
    (d:ZMod m)∣(n:ZMod m) ↔ d∣n := by
  constructor
  · rintro ⟨u,hu⟩
    have img := congrArg (ZMod.castHom div (ZMod d)) hu
    rw [map_natCast,map_mul,map_natCast,ZMod.natCast_self,zero_mul] at img
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp img
  · rintro ⟨v,rfl⟩
    exact ⟨v,Nat.cast_mul ..⟩

/-- For any particular ordered pair with the stated product the cluster is
exactly the event that its coordinates agree in their lowest t+1 bits. -/
theorem pair_mem_iff {t j N : ℕ} (ht : 2≤t) (odd : Odd N)
    {a b : ZMod (2^(2*t+j))} (prod : a*b=N) :
    a+b∈menu t j N ↔ 2^(t+1)∣(a-b).val := by
  obtain ⟨u,hu⟩ := PrimeFactors.DyadicPairSumWeight.gap_even (by omega) odd prod
  have diff : a-b=2*(u:ZMod _) := by
    rw [←ZMod.natCast_zmod_val (a-b),hu,Nat.cast_mul,Nat.cast_ofNat]
  have sum : a+b=2*(b+(u:ZMod _)) := by linear_combination diff
  have discr : (b+(u:ZMod (2^(2*t+j))))^2-(N:ZMod (2^(2*t+j)))=(u:ZMod (2^(2*t+j)))^2 := by
    rw [←prod]; linear_combination -b*diff
  have hit : 0<weight N (a+b) := (CoprimeGuessTables.positive_iff _).mpr ⟨a,b,prod,rfl⟩
  rw [sum] at hit ⊢
  rw [mem_iff ht _ hit,discr]
  have dc := dvd_cast (m:=2^(2*t+j)) (n:=u^2) (pow_dvd_pow 2 (by omega : 2*t≤2*t+j))
  simp only [Nat.cast_pow,Nat.cast_ofNat] at dc
  rw [dc,show 2^(2*t)=(2^t)^2 by rw [←pow_mul,mul_comm],
    Nat.pow_dvd_pow_iff (by decide : 2≠0),hu,pow_succ,mul_comm (2^t) 2]
  exact (mul_dvd_mul_iff_left (by decide : (2:ℕ)≠0)).symm

/-- Every label in the cluster has at least four multiples of its scale
as ordered presentations when the residual depth is at least four. -/
theorem weight_floor {t j N : ℕ} (hj : 4≤j) {s : ZMod (2^(2*t+j))}
    (mem : s∈menu t j N) : 2^(t+2)≤weight N s := by
  obtain ⟨d,hd,hs⟩ := mem_biUnion.mp mem
  obtain ⟨x,hx⟩ := (mem_filter.mp hd).2
  have low : 2^2≤roots j d := by
    rw [hx,←pow_two]
    by_cases zero : x.val=0
    · have x0 : x=0 := ZMod.val_injective _ (by simpa using zero)
      rw [x0,zero_pow (by decide : 2≠0),roots,PrimePowerPairWeight.roots_zero]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    · obtain ⟨i,u,uo,eq⟩ := Nat.exists_eq_two_pow_mul_odd zero
      rw [←ZMod.natCast_zmod_val x,eq,PrimeFactors.DyadicPairSumWeight.gap_roots j i u uo]
      split <;> apply Nat.pow_le_pow_right (by decide) <;> omega
  rw [lane_weight hs,pow_add,mul_comm (2^t) _]
  exact Nat.mul_le_mul_right _ low

private theorem root_mass (j : ℕ) : ∑ d∈squares j, roots j d = 2^j := by
  classical
  have maps : Set.MapsTo (fun x : ZMod (2^j) => x^2) (↑(univ : Finset (ZMod (2^j))) : Set _) (squares j) := by
    intro x _
    exact mem_filter.mpr ⟨mem_univ _,⟨x,pow_two x⟩⟩
  simpa only [roots,Nat.card_eq_fintype_card,Fintype.card_subtype] using
    (card_eq_sum_card_fiberwise maps).symm.trans (by simp)

theorem card {t j N : ℕ} (ht : 2≤t) (good : N%8=1) :
    (menu t j N).card=2*DyadicSquareValueCount.count j := by
  rw [menu,card_biUnion (disjoint ht)]
  simp only [lane_card ht good,sum_const,nsmul_eq_mul]
  rw [Nat.mul_comm]
  congr 1
  simp [squares,DyadicSquareValueCount.count,Nat.card_eq_fintype_card,Fintype.card_subtype]

/-- Each root at the remaining j bits contributes exactly two sum labels'
worth of scaled weight when the two opposite lanes are counted together. -/
theorem mass {t j N : ℕ} (ht : 2≤t) (good : N%8=1) :
    covered N (menu t j N)=2^(t+j+1) := by
  rw [covered_eq_sum,menu,sum_biUnion (disjoint ht)]
  calc
    _ = ∑ d∈squares j, 2*(roots j d*2^t) := by
      apply sum_congr rfl
      intro d _
      calc
        _ = ∑ _s ∈ lane t j N d, roots j d*2^t := sum_congr rfl fun _ h => lane_weight h
        _ = _ := by rw [sum_const,nsmul_eq_mul,lane_card ht good]; rfl
    _ = _ := by rw [←mul_sum,←sum_mul,root_mass,pow_succ,pow_add]; ring

/-- The share of all ordered residue pairs at the given fixed product. -/
theorem population {t j N : ℕ} (ht : 2≤t) (good : N%8=1) :
    2^(t-2)*covered N (menu t j N)=Nat.card (Pairs N (2^(2*t+j))) := by
  have odd : Odd N := Nat.odd_iff.mpr (by omega)
  rw [mass ht good,total ((ZMod.isUnit_iff_coprime _ _).mpr (odd.coprime_two_right.pow_right _)),
    Nat.totient_prime_pow Nat.prime_two (by omega),←pow_add]
  simp only [Nat.reduceSub,mul_one]
  congr 1
  omega

/-- At depth 161 the list fits in 2^32 guesses and covers one in 2^62
ordered residue pairs with the specified product. -/
theorem at_161 {N : ℕ} (good : N%8=1) :
    (menu 64 33 N).card=2863311534 ∧ (menu 64 33 N).card<2^32 ∧
    2^62*covered N (menu 64 33 N)=Nat.card (Pairs N (2^161)) := by
  rw [card (by decide) good,DyadicSquareValueCount.closed (by decide)]
  exact ⟨by decide,by decide,population (t:=64) (j:=33) (by decide) good⟩

end PrimeFactors.DyadicClusterMenu
