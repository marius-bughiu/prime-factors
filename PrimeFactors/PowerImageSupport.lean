import PrimeFactors.FrobeniusFixedCounts
import Mathlib.GroupTheory.Index

/-! Counts for arbitrary accepted output pairs after exponentiation. -/
namespace PrimeFactors.PowerImageSupport
open Finset
open scoped Classical

variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]

/-- Original pairs whose powered values are in the given finite set. -/
noncomputable def successes (E : ℕ) (S : Finset (G×H)) : ℕ :=
  (univ.filter (fun z : G×H => (z.1^E,z.2^E)∈S)).card

/-- The acceptable output pairs attained by the power map. -/
noncomputable def reachable (E : ℕ) (S : Finset (G×H)) : Finset (G×H) :=
  S.filter (fun y => ∃ z : G×H, (z.1^E,z.2^E)=y)

theorem reachable_card_le (E : ℕ) (S : Finset (G×H)) : (reachable E S).card ≤ S.card :=
  card_le_card (filter_subset _ S)

variable [IsCyclic G] [IsCyclic H]

/-- Each attainable output pair receives exactly the product of the local
kernel sizes. The acceptable outputs may be selected by any criterion. -/
theorem exact_count (E : ℕ) (S : Finset (G×H)) :
    successes E S = (Fintype.card G).gcd E * (Fintype.card H).gcd E * (reachable E S).card := by
  classical
  letI : CommGroup G := IsCyclic.commGroup
  letI : CommGroup H := IsCyclic.commGroup
  let f : G×H →* G×H := powMonoidHom E
  have val (z : G×H) : f z=(z.1^E,z.2^E) := rfl
  have ker : (univ.filter (fun z : G×H => f z=1)).card =
      (Fintype.card G).gcd E * (Fintype.card H).gcd E := by
    have eq : (univ.filter (fun z : G×H => f z=1)) =
        (univ.filter (fun x : G => x^E=1)) ×ˢ (univ.filter (fun y : H => y^E=1)) := by
      ext z
      simp [val,Prod.ext_iff]
    rw [eq,card_product]
    exact congrArg₂ Nat.mul
      ((FrobeniusFixedCounts.cyclic_count G E).trans (Nat.gcd_comm ..))
      ((FrobeniusFixedCounts.cyclic_count H E).trans (Nat.gcd_comm ..))
  have restrict : (univ.filter (fun z : G×H => (z.1^E,z.2^E)∈S)) =
      (univ.filter (fun z : G×H => f z∈reachable E S)) := by
    ext z
    simp only [mem_filter,mem_univ,true_and,reachable,val]
    exact ⟨fun h => ⟨h,⟨z,rfl⟩⟩,fun h => h.1⟩
  have fiber (y : G×H) (hy : y∈reachable E S) :
      (univ.filter (fun z : G×H => f z=y)).card =
      (Fintype.card G).gcd E * (Fintype.card H).gcd E :=
    (MonoidHom.card_fiber_eq_of_mem_range f (mem_filter.mp hy).2 ⟨1,f.map_one⟩).trans ker
  unfold successes
  rw [restrict,←sum_card_fiberwise_eq_card_filter,sum_congr rfl fiber]
  simp [Nat.mul_comm]

/-- A uniform success fraction at least 1/scale bounds the size of the
entire output image by the number of reachable acceptable pairs times scale. -/
theorem reachable_rate (E scale : ℕ) (S : Finset (G×H))
    (raw : Fintype.card G * Fintype.card H ≤ successes E S * scale) :
    (Fintype.card G / (Fintype.card G).gcd E) * (Fintype.card H / (Fintype.card H).gcd E) ≤
      (reachable E S).card * scale := by
  let P := Fintype.card G
  let Q := Fintype.card H
  let d := P.gcd E
  let e := Q.gcd E
  let X := P/d
  let Y := Q/e
  have left : X*d=P := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have right : Y*e=Q := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have total : (d*e)*(X*Y)=P*Q := calc
    _ = (X*d)*(Y*e) := by ring
    _ = _ := by rw [left,right]
  have pos : 0<d*e := Nat.mul_pos (Nat.gcd_pos_of_pos_left E Fintype.card_pos)
    (Nat.gcd_pos_of_pos_left E Fintype.card_pos)
  change X*Y ≤ (reachable E S).card*scale
  apply Nat.le_of_mul_le_mul_left (c:=d*e) _ pos
  rw [total,←Nat.mul_assoc]
  rwa [exact_count] at raw

/-- The plain cardinality of S is a valid bound even if membership in
the image has not been determined for any specified output. -/
theorem rate (E scale : ℕ) (S : Finset (G×H))
    (raw : Fintype.card G * Fintype.card H ≤ successes E S * scale) :
    (Fintype.card G / (Fintype.card G).gcd E) * (Fintype.card H / (Fintype.card H).gcd E) ≤
      S.card * scale :=
  (reachable_rate E scale S raw).trans
    (Nat.mul_le_mul_right scale (reachable_card_le E S))

end PrimeFactors.PowerImageSupport
