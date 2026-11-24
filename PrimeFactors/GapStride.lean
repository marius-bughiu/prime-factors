import PrimeFactors.Fermat
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.Basic

namespace PrimeFactors

/-- Offsets from `start` at which the square equals the target modulo the product
of the given radices. Each stage extends only roots found at the preceding stage. -/
noncomputable def squareOffsets (target start : ℕ) : List ℕ → List ℕ
  | [] => [0]
  | d :: ds =>
    let m := ds.prod
    (squareOffsets target start ds).flatMap fun u =>
      ((List.range d).map fun j => u + m*j).filter fun z =>
        (start + z)^2 % (d*m) == target % (d*m)

/-- Mixed-radix lifting enumerates exactly the roots, including singular roots. -/
theorem mem_squareOffsets {target start z : ℕ} {ds : List ℕ} (pos : 0 < ds.prod) :
    z ∈ squareOffsets target start ds ↔ z < ds.prod ∧ (start+z)^2 ≡ target [MOD ds.prod] := by
  induction ds generalizing z with
  | nil => simp [squareOffsets, Nat.ModEq, Nat.mod_one]
  | cons d ds ih =>
    simp only [List.prod_cons] at pos ⊢
    have mp : 0 < ds.prod := Nat.pos_of_mul_pos_left pos
    simp only [squareOffsets, List.mem_flatMap, List.mem_filter, List.mem_map,
      List.mem_range, beq_iff_eq]
    constructor
    · rintro ⟨u, hu, ⟨j, hj, rfl⟩, hz⟩
      have ru := (ih mp).mp hu
      refine ⟨?_, hz⟩
      calc
        u + ds.prod*j < ds.prod + ds.prod*j := Nat.add_lt_add_right ru.1 _
        _ = (j+1)*ds.prod := by ring
        _ ≤ d*ds.prod := Nat.mul_le_mul_right _ hj
    · rintro ⟨hz, correct⟩
      refine ⟨z % ds.prod, (ih mp).mpr ⟨Nat.mod_lt _ mp, ?_⟩, ?_, correct⟩
      · exact (((Nat.mod_modEq z ds.prod).add_left start).pow 2).trans
          (correct.of_dvd (dvd_mul_left _ _))
      · exact ⟨z / ds.prod, (Nat.div_lt_iff_lt_mul mp).mpr hz, Nat.mod_add_div _ _⟩

/-- If the half-gap is m*c and c² is known modulo e, a root class of stride
m²*e contains the midpoint. The bound on its index depends only on the cofactor c. -/
theorem gap_stride_witness {N H m c e s : ℕ} (hm : 0 < m) (he : 0 < e)
    (identity : H^2 = N + (m*c)^2) (code : c^2 ≡ s [MOD e]) :
    let r := ceilSqrt N
    let M := m^2*e
    ∃ z j : ℕ, z < M ∧ (r+z)^2 ≡ N + m^2*s [MOD M] ∧
      H = r + z + M*j ∧ 2*r*e*j ≤ c^2 := by
  dsimp only
  let r := ceilSqrt N
  let M := m^2*e
  have mp : 0 < M := Nat.mul_pos (pow_pos hm _) he
  have hr : r ≤ H := ceilSqrt_le_iff.mpr (by omega)
  have rn : N ≤ r^2 := ceilSqrt_le_iff.mp (le_refl r)
  let u := H-r
  have hu : r+u=H := by dsimp [u]; omega
  let z := u%M
  let j := u/M
  have decomp : z + M*j = u := Nat.mod_add_div _ _
  have zc : r+z ≡ H [MOD M] := hu ▸ (Nat.mod_modEq u M).add_left r
  have hc : H^2 ≡ N+m^2*s [MOD M] := by
    rw [identity, mul_pow]
    exact (code.mul_left' (m^2)).add_left N
  refine ⟨z,j,Nat.mod_lt _ mp,(zc.pow 2).trans hc,?_,?_⟩
  · change H = r+z+M*j
    omega
  have inner : 2*r*u ≤ (m*c)^2 := by
    nlinarith only [identity, rn, congrArg (fun v : ℕ => v^2) hu, Nat.zero_le (u^2)]
  have mj : M*j ≤ u := by omega
  apply Nat.le_of_mul_le_mul_left (c := m^2) _ (pow_pos hm _)
  calc
    m^2 * (2*r*e*j) = 2*r*(M*j) := by dsimp [M]; ring
    _ ≤ 2*r*u := Nat.mul_le_mul_left _ mj
    _ ≤ (m*c)^2 := inner
    _ = m^2*c^2 := by ring

/-- The square of every unit modulo 24 is one. Only the 24 residue classes enter. -/
theorem square_mod_twentyfour {c : ℕ} (unit : c.Coprime 6) : c^2 ≡ 1 [MOD 24] := by
  have pos : c%24 < 24 := Nat.mod_lt _ (by decide)
  have rem : (c%24).Coprime 6 := by
    change Nat.gcd (c%24) 6 = 1
    rw [Nat.gcd_comm (c%24), Nat.gcd_rec 6, Nat.mod_mod_of_dvd c (by decide : 6 ∣ 24),
      ← Nat.gcd_rec 6, Nat.gcd_comm]
    exact unit
  have valid : ∀ t : Fin 24, t.val.Coprime 6 → t.val^2 % 24 = 1 := by decide
  exact ((Nat.mod_modEq c 24).pow 2).symm.trans (valid ⟨_,pos⟩ rem)

/-- For positive factors p and p+2mc, square-root lifting plus a bounded scan
reaches the exact midpoint whenever the displayed cofactor budget holds. -/
theorem smooth_gap_search {p m c e s budget : ℕ} {ds : List ℕ}
    (hm : 0 < m) (he : 0 < e) (code : c^2 ≡ s [MOD e]) (radices : ds.prod = m^2*e)
    (small : c^2 < 2*ceilSqrt (p*(p+2*(m*c)))*e*budget) :
    let N := p*(p+2*(m*c))
    let r := ceilSqrt N
    ∃ z ∈ squareOffsets (N+m^2*s) r ds, ∃ j < budget,
      r+z+ds.prod*j = p+m*c := by
  let N := p*(p+2*(m*c))
  have id : (p+m*c)^2=N+(m*c)^2 := by dsimp [N]; ring
  obtain ⟨z,j,hz,root,repr,bd⟩ := gap_stride_witness hm he id code
  have mp : 0 < ds.prod := radices ▸ Nat.mul_pos (pow_pos hm _) he
  refine ⟨z,(mem_squareOffsets mp).mpr (radices ▸ ⟨hz,root⟩),j,?_,?_⟩
  · by_contra! h
    have := Nat.mul_le_mul_left (2*ceilSqrt N*e) h
    change c^2 < 2*ceilSqrt N*e*budget at small
    omega
  · rw [radices]; exact repr.symm

/-- An exhausted root-class search bounds the remaining half-gap cofactor of every
factor pair it covers. The statement uses the publicly tested midpoints. -/
theorem gap_stride_exclusion {N p m c e s budget : ℕ} {ds : List ℕ}
    (hm : 0 < m) (he : 0 < e) (code : c^2 ≡ s [MOD e]) (radices : ds.prod = m^2*e)
    (miss : ∀ z ∈ squareOffsets (N+m^2*s) (ceilSqrt N) ds, ∀ j < budget, ∀ d : ℕ,
      (ceilSqrt N+z+ds.prod*j)^2 ≠ N+d^2) (pair : N=p*(p+2*(m*c))) :
    2*ceilSqrt N*e*budget ≤ c^2 := by
  subst N
  by_contra! small
  obtain ⟨z, root, j, hj, eq⟩ := smooth_gap_search hm he code radices small
  apply miss z root j hj (m*c)
  rw [eq]; ring

private theorem gap_square_congruence {N H D m : ℕ} (identity : H^2=N+D^2) :
    H^2 ≡ N [MOD m^2] ↔ m ∣ D := by
  rw [identity, Nat.ModEq.comm, Nat.modEq_iff_dvd' (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)]

/-- The first B positions in all root classes cover the exact midpoint iff its
half-gap has the chosen divisor and the midpoint lies in the allocated interval. -/
theorem budget_gap_root_iff {N H D m B : ℕ} {ds : List ℕ} (hm : 0 < m)
    (identity : H^2=N+D^2) (radices : ds.prod=m^2) :
    (∃ z ∈ squareOffsets N (ceilSqrt N) ds, ∃ j < B, H=ceilSqrt N+z+m^2*j) ↔
      m ∣ D ∧ H < ceilSqrt N + m^2*B := by
  let r := ceilSqrt N
  let M := m^2
  have mp : 0 < M := pow_pos hm _
  have pos : 0 < ds.prod := radices ▸ mp
  have le : r ≤ H := ceilSqrt_le_iff.mpr (by omega)
  constructor
  · rintro ⟨z,root,j,hj,eq⟩
    have data := (mem_squareOffsets pos).mp root
    rw [radices] at data
    change z < M ∧ (r+z)^2 ≡ N [MOD M] at data
    change H=r+z+M*j at eq
    have congr : H ≡ r+z [MOD M] := by rw [eq]; simp [Nat.ModEq]
    have bound := Nat.mul_le_mul_left M (show j+1 ≤ B from hj)
    rw [Nat.mul_add, Nat.mul_one] at bound
    exact ⟨(gap_square_congruence identity).mp ((congr.pow 2).trans data.2), by change H < r+M*B; omega⟩
  · rintro ⟨dvd, bound⟩
    let u := H-r
    have hu : r+u=H := by dsimp [u]; omega
    have repr := Nat.mod_add_div u M
    have cong : r+u%M ≡ H [MOD M] := hu ▸ (Nat.mod_modEq u M).add_left r
    have root := (cong.pow 2).trans ((gap_square_congruence identity).mpr dvd)
    have member : u%M ∈ squareOffsets N r ds :=
      (mem_squareOffsets pos).mpr (radices ▸ ⟨Nat.mod_lt _ mp,root⟩)
    refine ⟨u%M, member, u/M, (Nat.div_lt_iff_lt_mul mp).mpr ?_, ?_⟩
    · change H < r+M*B at bound
      rw [Nat.mul_comm B]; omega
    · change H=r+u%M+M*(u/M); omega

/-- Exact coverage of the first midpoint of each root class. This criterion is
used to count successful prime pairs without making assumptions on the roots. -/
theorem first_gap_root_iff {N H D m : ℕ} {ds : List ℕ} (hm : 0 < m)
    (identity : H^2=N+D^2) (radices : ds.prod=m^2) :
    H-ceilSqrt N ∈ squareOffsets N (ceilSqrt N) ds ↔ m ∣ D ∧ H < ceilSqrt N + m^2 := by
  have le : ceilSqrt N ≤ H := ceilSqrt_le_iff.mpr (by omega)
  have pos : 0 < ds.prod := radices ▸ pow_pos hm _
  rw [mem_squareOffsets pos, radices, Nat.add_sub_of_le le, gap_square_congruence identity]
  omega

/-- Any hit in the first B entries of a genuine class forces a small residual
gap. When the midpoint is at most 2X, the implied constant is four. -/
theorem gap_stride_necessary {N H m c B X : ℕ} (positive : 0 < N)
    (identity : H^2 = N+(m*c)^2) (upper : H ≤ 2*X)
    (hit : H < ceilSqrt N + m^2*B) : c^2 < 4*X*B := by
  let r := ceilSqrt N
  have hr : r ≤ H := ceilSqrt_le_iff.mpr (by omega)
  have rp : 0 < r := by
    by_contra! h
    have zero : ceilSqrt N ≤ 0 := h
    have := ceilSqrt_le_iff.mp zero
    omega
  have prev : (r-1)^2 < N := by
    by_contra! h
    have le : r ≤ r-1 := ceilSqrt_le_iff.mpr h
    omega
  have before : r-1+1=r := by omega
  have round : r^2 < N+2*r := by
    nlinarith only [prev, congrArg (fun t : ℕ => t^2) before, before]
  let u := H-r
  have hu : r+u=H := by dsimp [u]; omega
  have exactSq : H^2=r^2+u*(H+r) := by rw [← hu]; ring
  have bounded := Nat.mul_le_mul_left u (show H+r ≤ 4*X by omega)
  have gap : (m*c)^2 < 4*X*(u+1) := by
    nlinarith only [identity, exactSq, bounded, round, show 2*r ≤ 4*X by omega]
  change H < r+m^2*B at hit
  have next : u+1 ≤ m^2*B := by omega
  have ans : m^2*c^2 < m^2*(4*X*B) := calc
    _ = (m*c)^2 := by ring
    _ < _ := gap
    _ ≤ 4*X*(m^2*B) := Nat.mul_le_mul_left _ next
    _ = _ := by ring
  exact Nat.lt_of_mul_lt_mul_left ans

/-- A small product-only run lifts two residues modulo 625. One yields the
midpoint 351 and the half-gap 250. -/
theorem gap_stride_60701 :
    (squareOffsets 60701 247 [5,5,5,5]).length = 2 ∧
      104 ∈ squareOffsets 60701 247 [5,5,5,5] ∧
      (247+104)^2 = 60701+250^2 ∧ 60701 = (351-250)*(351+250) := by decide +kernel

end PrimeFactors
