import PrimeFactors.CircleMarkRationalFrequency

/-! A finite staircase inside a clipped quarter disk. The count of points
divisible in both coordinates tracks its area divided by the divisor squared. -/
namespace PrimeFactors.CircleMarkDiskStaircase

open Finset CircleMarkRationalFrequency

/-- Height of the strip at the right edge of its unit-width base. -/
def height (u : ℕ) : ℕ := min 105 (Nat.sqrt (125^2-(u+1)^2))

noncomputable def strip (m u : ℕ) : Finset (ℕ×ℕ) :=
  Ioc (u*m) ((u+1)*m) ×ˢ Ioc 0 (height u*m)

noncomputable def region (m : ℕ) : Finset (ℕ×ℕ) := (range 105).biUnion (strip m)

private theorem height_cap (u : ℕ) : height u≤105 := min_le_left ..

-- Use small integer square comparisons for the finite computation.
private def tabulated (u : ℕ) : ℕ := if u<67 then 105 else
  ([104,104,103,102,102,101,100,100,99,98,97,96,96,95,94,93,92,91,90,89,
    88,87,86,85,84,83,82,81,80,78,77,76,75,73,72,70,69,67] : List ℕ)[u-67]?.getD 0

private theorem table_bounds : ∀ i : Fin 105,
    tabulated i≤105 ∧ (tabulated i)^2≤125^2-((i:ℕ)+1)^2 ∧
      (tabulated i=105 ∨ 125^2-((i:ℕ)+1)^2<(tabulated i+1)^2) := by
  set_option maxRecDepth 2048 in decide +kernel

theorem height_sum : ∑ u∈range 105, height u=10394 := by
  calc _ = ∑ u∈range 105, tabulated u := by
         apply sum_congr rfl
         intro u um
         obtain ⟨cap,lower,upper⟩ := table_bounds ⟨u,mem_range.mp um⟩
         change tabulated u≤105 at cap
         change (tabulated u)^2≤125^2-(u+1)^2 at lower
         change tabulated u=105 ∨ 125^2-(u+1)^2<(tabulated u+1)^2 at upper
         apply le_antisymm _ (le_min cap (Nat.le_sqrt'.mpr lower))
         rcases upper with eqn | strict
         · rw [eqn]; exact height_cap _
         · exact (min_le_right ..).trans (Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr strict))
       _ = _ := by decide +kernel

theorem inside (m : ℕ) : region m⊆rectangle (105*m) (105*m) := by
  intro z zm
  obtain ⟨u,um,zu⟩ := mem_biUnion.mp zm
  have ucap : u+1≤105 := mem_range.mp um
  obtain ⟨xl,xu⟩ := mem_Ioc.mp (mem_product.mp zu).1
  obtain ⟨yl,yu⟩ := mem_Ioc.mp (mem_product.mp zu).2
  exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,xu.trans (Nat.mul_le_mul_right m ucap)⟩,
    mem_Icc.mpr ⟨yl,yu.trans (Nat.mul_le_mul_right m (height_cap u))⟩⟩

theorem norm_bound {m : ℕ} {z : ℕ×ℕ} (zm : z∈region m) : z.1^2+z.2^2≤(125*m)^2 := by
  obtain ⟨u,um,zu⟩ := mem_biUnion.mp zm
  have ucap : u+1≤125 := (mem_range.mp um : u+1≤105).trans (by decide)
  have vcap : height u≤Nat.sqrt (125^2-(u+1)^2) := min_le_right ..
  have x := (mem_Ioc.mp (mem_product.mp zu).1).2
  have y := (mem_Ioc.mp (mem_product.mp zu).2).2
  have bound : (u+1)^2+(height u)^2≤125^2 := by
    have a := Nat.le_sqrt'.mp vcap
    have b := Nat.pow_le_pow_left ucap 2
    omega
  calc _ ≤ ((u+1)*m)^2+(height u*m)^2 := Nat.add_le_add (Nat.pow_le_pow_left x 2) (Nat.pow_le_pow_left y 2)
       _ ≤ _ := by rw [mul_pow,mul_pow,mul_pow,←Nat.add_mul]; exact Nat.mul_le_mul_right (m^2) bound

private theorem disjoint_strip {u v : ℕ} (m : ℕ) (ne : u≠v) : Disjoint (strip m u) (strip m v) := by
  apply disjoint_left.mpr
  intro z zu zv
  have a := mem_Ioc.mp (mem_product.mp zu).1
  have b := mem_Ioc.mp (mem_product.mp zv).1
  rcases lt_or_gt_of_ne ne with lt | gt
  · exact (not_lt_of_ge (Nat.mul_le_mul_right m (show u+1≤v from lt))) (b.1.trans_le a.2)
  · exact (not_lt_of_ge (Nat.mul_le_mul_right m (show v+1≤u from gt))) (a.1.trans_le b.2)

theorem area (m : ℕ) : (region m).card = 10394*m^2 := by
  rw [region,card_biUnion (fun u _ v _ ne => disjoint_strip m ne)]
  simp only [strip,card_product,Nat.card_Ioc,Nat.sub_zero,Nat.add_mul,one_mul,Nat.add_sub_cancel_left]
  calc _ = ∑ u∈range 105, height u*m^2 := sum_congr rfl (fun _ _ => by ring)
       _ = _ := by rw [←sum_mul,height_sum]

private theorem shifted_count {a b : ℕ} (ab : a≤b) (d : ℕ) :
    ((Ioc a b).filter (d∣·)).card = b/d-a/d := by
  have sets : (Ioc a b).filter (d∣·) =
      (Ioc 0 b).filter (d∣·) \ (Ioc 0 a).filter (d∣·) := by
    ext i
    simp only [mem_filter,mem_Ioc,mem_sdiff]
    omega
  have sub : (Ioc 0 a).filter (d∣·) ⊆ (Ioc 0 b).filter (d∣·) :=
    filter_subset_filter _ (Ioc_subset_Ioc_right ab)
  rw [sets,card_sdiff sub,Nat.Ioc_filter_dvd_card_eq_div,Nat.Ioc_filter_dvd_card_eq_div]

private theorem floor_error (a : ℕ) {d : ℕ} (pos : 0<d) :
    0≤(a:ℚ)/d-((a/d:ℕ):ℚ) ∧ (a:ℚ)/d-((a/d:ℕ):ℚ)<1 := by
  refine ⟨sub_nonneg.mpr Nat.cast_div_le,?_⟩
  have b := (Nat.div_lt_iff_lt_mul pos).mp (Nat.lt_succ_self (a/d))
  have div : (a:ℚ)/d < ((a/d:ℕ):ℚ)+1 := (div_lt_iff₀ (by exact_mod_cast pos)).mpr (by exact_mod_cast b)
  linarith

set_option maxHeartbeats 800000 in
private theorem strip_error (m u : ℕ) {d : ℕ} (pos : 0<d) :
    |(((strip m u).filter (fun z => d∣z.1 ∧ d∣z.2)).card:ℚ)
      - (height u:ℚ)*m^2/(d:ℚ)^2| ≤ 106*m := by
  let a := u*m
  let b := (u+1)*m
  let t := height u*m
  have ab : a≤b := Nat.mul_le_mul_right m (Nat.le_succ _)
  have row := shifted_count ab d
  rw [strip,filter_product,card_product,Nat.Ioc_filter_dvd_card_eq_div,Nat.cast_mul]
  change |(((Ioc a b).filter (d∣·)).card:ℚ)*((t/d:ℕ):ℚ)-_|≤_
  rw [row,Nat.cast_sub (Nat.div_le_div_right ab)]
  let A : ℚ := ((b/d:ℕ):ℚ)-((a/d:ℕ):ℚ)
  let B : ℚ := ((t/d:ℕ):ℚ)
  let X : ℚ := (m:ℚ)/d
  let Y : ℚ := (t:ℚ)/d
  have diff : (b:ℚ)/d-(a:ℚ)/d=X := by dsimp [a,b,X]; push_cast; ring
  have ax : |A-X|≤1 := by
    have ea := floor_error a pos
    have eb := floor_error b pos
    dsimp [A]
    rw [abs_le]; constructor <;> linarith
  have by' : |B-Y|≤1 := by
    have et := floor_error t pos
    dsimp [B,Y]; rw [abs_le]; constructor <;> linarith
  have bp : 0≤B := Nat.cast_nonneg _
  have hc := Nat.mul_le_mul_right m (height_cap u)
  have bc : B≤105*m := by dsimp [B]; exact_mod_cast (Nat.div_le_self t d).trans hc
  have xp : 0≤X := by dsimp [X]; positivity
  have xc : X≤m := (div_le_iff₀ (by exact_mod_cast pos : 0<(d:ℚ))).mpr (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (by exact_mod_cast pos : (1:ℚ)≤d) (Nat.cast_nonneg m))
  have xy : X*Y = (height u:ℚ)*m^2/(d:ℚ)^2 := by dsimp [X,Y,t]; push_cast; ring
  change |A*B-_|≤_
  rw [←xy,show A*B-X*Y=(A-X)*B+X*(B-Y) by ring]
  calc _ ≤ |(A-X)*B|+|X*(B-Y)| := abs_add_le ..
       _ ≤ 1*B+X*1 := by
         rw [abs_mul,abs_mul,abs_of_nonneg bp,abs_of_nonneg xp]
         exact add_le_add (mul_le_mul_of_nonneg_right ax bp) (mul_le_mul_of_nonneg_left by' xp)
       _ ≤ _ := by linarith

/-- Uniform error for the divisibility count, summed over all 105 strips. -/
theorem discrepancy {m d : ℕ} (pos : 0<d) :
    |(((region m).filter (fun z => d∣z.1 ∧ d∣z.2)).card:ℚ)
      - 10394*(m:ℚ)^2/(d:ℚ)^2| ≤ 20000*((m:ℚ)+1) := by
  let f := fun u => (strip m u).filter (fun z => d∣z.1 ∧ d∣z.2)
  have sets : (region m).filter (fun z => d∣z.1 ∧ d∣z.2)=(range 105).biUnion f := by
    ext z
    simp only [region,f,mem_filter,mem_biUnion]
    constructor
    · rintro ⟨⟨u,um,zu⟩,hz⟩; exact ⟨u,um,zu,hz⟩
    · rintro ⟨u,um,zu,hz⟩; exact ⟨⟨u,um,zu⟩,hz⟩
  have counts := card_biUnion (s:=range 105) (t:=f) (fun u _ v _ ne =>
    (disjoint_strip m ne).mono (filter_subset ..) (filter_subset ..))
  have coeff : (∑ u∈range 105, (height u:ℚ))=10394 := by exact_mod_cast height_sum
  have expected : (∑ u∈range 105, (height u:ℚ)*m^2/(d:ℚ)^2)=10394*(m:ℚ)^2/(d:ℚ)^2 := by
    simp only [div_eq_mul_inv,←sum_mul,coeff]
  rw [sets,counts,Nat.cast_sum,←expected,←sum_sub_distrib]
  calc _ ≤ ∑ u∈range 105, |((f u).card:ℚ)-(height u:ℚ)*m^2/(d:ℚ)^2| := abs_sum_le_sum_abs ..
       _ ≤ ∑ _u∈range 105, (106:ℚ)*m := sum_le_sum (fun u _ => strip_error m u pos)
       _ ≤ _ := by simp; linarith

end PrimeFactors.CircleMarkDiskStaircase
