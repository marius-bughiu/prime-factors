import PrimeFactors.FrobeniusFixedCounts
import PrimeFactors.PoweredTraceLimit
import Mathlib.GroupTheory.Index

/-! Exact distribution of local multiplicative orders after a fixed power. -/
namespace PrimeFactors.PoweredOrderCounts
open Finset

/-- Number of original inputs whose E-th power has order r. -/
noncomputable def count (G : Type*) [Group G] [Fintype G] (E r : ℕ) : ℕ :=
  (univ.filter (fun x : G => orderOf (x^E)=r)).card

/-- A surjective group homomorphism pulls a finite subset of its codomain
back to one full kernel-sized fibre for each member. -/
private theorem pullback {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    [DecidableEq H] (f : G →* H) (onto : Function.Surjective f) (S : Finset H) :
    (univ.filter (fun x : G => f x∈S)).card =
    S.card*(univ.filter (fun x : G => f x=1)).card := by
  have fibers (y : H) : (univ.filter (fun x : G => f x=y)).card =
      (univ.filter (fun x : G => f x=1)).card :=
    MonoidHom.card_fiber_eq_of_mem_range f (onto y) (onto 1)
  rw [←sum_card_fiberwise_eq_card_filter]
  simp [fibers]

/-- For a finite cyclic group of size P, g=gcd(P,E) of the original
seeds map to each element of the image of size P/g. In particular E=0
sends every seed to the identity, which has order one. -/
theorem exact_count (G : Type*) [Group G] [Fintype G] [IsCyclic G] (E r : ℕ) :
    count G E r = if r∣Fintype.card G / (Fintype.card G).gcd E then
      (Fintype.card G).gcd E*r.totient else 0 := by
  classical
  letI : CommGroup G := IsCyclic.commGroup
  let f : G →* G := powMonoidHom E
  let F : G →* f.range := f.rangeRestrict
  let g := (Fintype.card G).gcd E
  have onto : Function.Surjective F := f.rangeRestrict_surjective
  have val (x : G) : (F x : G)=x^E := rfl
  have ker : (univ.filter (fun x : G => F x=1)).card = g := by
    have eq : (univ.filter (fun x : G => F x=1)) = (univ.filter (fun x : G => x^E=1)) := by
      ext x
      simp only [mem_filter,mem_univ,true_and]
      exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
    rw [eq]
    exact (FrobeniusFixedCounts.cyclic_count G E).trans (Nat.gcd_comm ..)
  have whole : Fintype.card G=Fintype.card f.range*g := by
    simpa [ker] using pullback F onto univ
  have gp : 0<g := Nat.gcd_pos_of_pos_left E Fintype.card_pos
  have size : Fintype.card f.range=Fintype.card G / g := by
    rw [whole,Nat.mul_div_cancel _ gp]
  let rows : Finset f.range := univ.filter (fun y => orderOf y=r)
  have orders : count G E r=(univ.filter (fun x : G => F x∈rows)).card := by
    unfold count
    congr 1
    ext x
    simp only [mem_filter,mem_univ,true_and,rows]
    rw [←Subgroup.orderOf_coe,val]
  rw [orders,pullback F onto rows,ker]
  change rows.card*g=if r∣Fintype.card G/g then g*r.totient else 0
  rw [←size]
  split_ifs with divides
  · have card : rows.card=r.totient := IsCyclic.card_orderOf_eq_totient divides
    rw [card,Nat.mul_comm]
  · have empty : rows=∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro y hy
      have o : orderOf y=r := (mem_filter.mp hy).2
      exact divides (o ▸ orderOf_dvd_card (x:=y))
    simp [empty]

/-- Count independently chosen inputs with a prescribed pair of output
orders, allowing a different power on each group. -/
theorem pair_count (G H : Type*) [Group G] [Group H] [Fintype G] [Fintype H]
    (E F r s : ℕ) :
    (univ.filter (fun z : G×H => orderOf (z.1^E)=r ∧ orderOf (z.2^F)=s)).card =
      count G E r * count H F s := by
  have same : (univ.filter (fun z : G×H => orderOf (z.1^E)=r ∧ orderOf (z.2^F)=s)) =
      (univ.filter (fun x : G => orderOf (x^E)=r)) ×ˢ (univ.filter (fun y : H => orderOf (y^F)=s)) := by
    ext z
    simp
  rw [same,card_product]
  rfl

/-- Summing the product of local counts over any allowed finite relation
on orders introduces no overlap, even when several pairs qualify. -/
theorem menu (G H : Type*) [Group G] [Group H] [Fintype G] [Fintype H]
    (E F : ℕ) (S : Finset (ℕ×ℕ)) :
    (univ.filter (fun z : G×H => (orderOf (z.1^E),orderOf (z.2^F))∈S)).card =
      ∑ w ∈ S, count G E w.1 * count H F w.2 := by
  rw [←sum_card_fiberwise_eq_card_filter]
  apply sum_congr rfl
  rintro ⟨r,s⟩ _
  simpa only [Prod.mk.injEq] using pair_count G H E F r s

/-- Elements of order r in a cyclic group of size size. -/
def imageMultiplicity (size r : ℕ) : ℕ := if r∣size then r.totient else 0

/-- Every allowed pair of powered orders has the same number of preimages per
image point. This factors the two kernel sizes out of any finite menu. -/
theorem menu_scaled (G H : Type*) [Group G] [Group H] [Fintype G] [Fintype H]
    [IsCyclic G] [IsCyclic H] (E F : ℕ) (S : Finset (ℕ×ℕ)) :
    (univ.filter (fun z : G×H => (orderOf (z.1^E),orderOf (z.2^F))∈S)).card =
      (Fintype.card G).gcd E * (Fintype.card H).gcd F *
        ∑ w ∈ S, imageMultiplicity (Fintype.card G / (Fintype.card G).gcd E) w.1 *
          imageMultiplicity (Fintype.card H / (Fintype.card H).gcd F) w.2 := by
  rw [menu,mul_sum]
  apply sum_congr rfl
  intro w _
  simp only [exact_count,imageMultiplicity]
  split_ifs <;> ring

/-- Exact number of original pairs hitting the two fresh-control order
classes (7,8) and (14,8) under one common exponent E. -/
theorem trace_count (G H : Type*) [Group G] [Group H] [Fintype G] [Fintype H]
    [IsCyclic G] [IsCyclic H] (E : ℕ) :
    (univ.filter (fun z : G×H =>
      (orderOf (z.1^E)=7 ∨ orderOf (z.1^E)=14) ∧ orderOf (z.2^E)=8)).card =
      (Fintype.card G).gcd E * (Fintype.card H).gcd E *
        PoweredTraceLimit.count (Fintype.card G / (Fintype.card G).gcd E)
          (Fintype.card H / (Fintype.card H).gcd E) := by
  let S : Finset (ℕ×ℕ) := {(7,8),(14,8)}
  have same : (univ.filter (fun z : G×H =>
      (orderOf (z.1^E)=7 ∨ orderOf (z.1^E)=14) ∧ orderOf (z.2^E)=8)) =
      (univ.filter (fun z : G×H => (orderOf (z.1^E),orderOf (z.2^E))∈S)) := by
    ext z
    simp only [mem_filter,mem_univ,true_and,S,mem_insert,mem_singleton,Prod.mk.injEq]
    tauto
  have image (A B : ℕ) : (∑ w ∈ S, imageMultiplicity A w.1 * imageMultiplicity B w.2) =
      PoweredTraceLimit.count A B := by
    have apart : (7,8) ∉ ({(14,8)} : Finset (ℕ×ℕ)) := by decide
    simp only [S,sum_insert apart,sum_singleton,imageMultiplicity,PoweredTraceLimit.count,
      show (7:ℕ).totient=6 by decide,show (14:ℕ).totient=6 by decide,show (8:ℕ).totient=4 by decide]
  rw [same,menu_scaled,image]

/-- A nonempty group's powered image has positive size for every exponent. -/
theorem image_pos (P E : ℕ) (pos : 0<P) : 0<P/P.gcd E :=
  Nat.div_pos (Nat.gcd_le_left E pos) (Nat.gcd_pos_of_pos_left E pos)

/-- Cancellation of the two positive kernel sizes transfers a raw seed
rate to the identical image rate, with any integer scale (including 2^503). -/
theorem trace_rate (G H : Type*) [Group G] [Group H] [Fintype G] [Fintype H]
    [IsCyclic G] [IsCyclic H] (E scale : ℕ)
    (raw : Fintype.card G * Fintype.card H ≤
      (univ.filter (fun z : G×H =>
        (orderOf (z.1^E)=7 ∨ orderOf (z.1^E)=14) ∧ orderOf (z.2^E)=8)).card * scale) :
    let X := Fintype.card G / (Fintype.card G).gcd E
    let Y := Fintype.card H / (Fintype.card H).gcd E
    X*Y ≤ PoweredTraceLimit.count X Y * scale := by
  intro X Y
  let P := Fintype.card G
  let Q := Fintype.card H
  let d := P.gcd E
  let e := Q.gcd E
  have left : X*d=P := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have right : Y*e=Q := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have total : (d*e)*(X*Y)=P*Q := calc
    _ = (X*d)*(Y*e) := by ring
    _ = _ := by rw [left,right]
  have pos : 0<d*e := Nat.mul_pos (Nat.gcd_pos_of_pos_left E Fintype.card_pos)
    (Nat.gcd_pos_of_pos_left E Fintype.card_pos)
  rw [trace_count] at raw
  change P*Q ≤ d*e*PoweredTraceLimit.count X Y*scale at raw
  apply Nat.le_of_mul_le_mul_left (c:=d*e) _ pos
  rwa [total,←Nat.mul_assoc]

/-- The two order classes contain at most 48 points in any powered image. -/
theorem trace_cap (X Y : ℕ) : PoweredTraceLimit.count X Y≤48 := by
  unfold PoweredTraceLimit.count
  split_ifs <;> decide

end PrimeFactors.PoweredOrderCounts
