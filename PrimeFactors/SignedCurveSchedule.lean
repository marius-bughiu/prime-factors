import PrimeFactors.ThreeNormCurves

/-! A choice of three publicly eligible signed targets can be priced before
search. Characterize exactly which selections cover an unknown sign row in
the three-generator case, and bound the cost of a cyclic three-curve search. -/
namespace PrimeFactors.SignedCurveSchedule

open RootableSignSpan

/-- If the public Jacobi bit vanishes at a and b, at least one of a, b and
their binary sum has a square root modulo the actual product. -/
theorem eligible_line {s p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (g : Fin s → ℤ) (gp : ∀ i, (g i : ZMod p) ≠ 0) (gq : ∀ i, (g i : ZMod q) ≠ 0)
    (a b : Mask s) (ha : publicRow (p*q) g a = 0) (hb : publicRow (p*q) g b = 0) :
    IsSquare (word g a : ZMod (p*q)) ∨ IsSquare (word g b : ZMod (p*q)) ∨
      IsSquare (word g (a+b) : ZMod (p*q)) := by
  rw [public_eq_add g gp gq, LinearMap.add_apply] at ha hb
  simp only [rootable_iff cop g gp gq, Submodule.mem_inf, LinearMap.mem_ker, map_add]
  exact (by decide : ∀ x y z w : Bit, x+y=0 → z+w=0 →
    (x=0 ∧ y=0) ∨ (z=0 ∧ w=0) ∨ (x+z=0 ∧ y+w=0)) _ _ _ _ ha hb

/-- Mask i+1 is the signed product selected by its three low bits, in the
order −1, 2, −2, 3, −3, 6, −6. Bit i in a selection enables that mask. -/
noncomputable def selected (s : Fin 128) (m : ℕ) : Bool := s.val.testBit (m-1)

/-- Dot product with the hidden sign row, zero precisely for a positive target. -/
noncomputable def positive (row mask : ℕ) : Bool :=
  let a := row &&& mask
  !((a.testBit 0 ^^ a.testBit 1) ^^ a.testBit 2)

/-- Check all eight possible local sign rows on the publicly positive masks. -/
noncomputable def covers (s : Fin 128) : Bool :=
  (List.range 8).all fun row =>
    (List.range 7).any fun i => selected s (i+1) && positive row (i+1)

/-- Each triple has xor zero; the third mask is the sum of the first two
as binary vectors. Every line in the three-generator mask space appears. -/
def lines : List (ℕ × ℕ × ℕ) :=
  [(1,2,3),(1,4,5),(1,6,7),(2,4,6),(2,5,7),(3,4,7),(3,5,6)]

noncomputable def containsLine (s : Fin 128) : Bool :=
  lines.any fun (a,b,c) => selected s a && selected s b && selected s c

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- Covering every possible sign row is equivalent to including an entire
line. In particular adding a fourth or later curve cannot lower the minimum
total price among covering selections with nonnegative additive prices. -/
theorem complete_cover : ∀ s : Fin 128, covers s = containsLine s := by decide +kernel

noncomputable def points (l : ℕ × ℕ × ℕ) : Finset ℕ := {l.1, l.2.1, l.2.2}

noncomputable def selectedMasks (s : Fin 128) : Finset ℕ :=
  (Finset.Icc 1 7).filter fun i => selected s i

/-- For any nonnegative additive price (blocks, row counts, or another
fixed search cost) a guaranteeing selection contains a line costing no more.
Each such line uses only targets already available in the selection. -/
theorem contained_cost (cost : ℕ → ℕ) (s : Fin 128) (h : covers s = true) :
    ∃ l ∈ lines, points l ⊆ selectedMasks s ∧
      ∑ i ∈ points l, cost i ≤ ∑ i ∈ selectedMasks s, cost i := by
  rw [complete_cover] at h
  obtain ⟨⟨a,b,c⟩,mem,h⟩ := List.any_eq_true.mp h
  have inside : ∀ l∈lines, points l ⊆ Finset.Icc 1 7 := by decide +kernel
  have sub : points (a,b,c) ⊆ selectedMasks s := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨inside _ mem hi,?_⟩
    simp only [Bool.and_eq_true] at h
    simp only [points,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl <;> tauto
  exact ⟨(a,b,c),mem,sub,Finset.sum_le_sum_of_subset sub⟩

/-- Every rootable signed target has two points on its single public norm
equation whose determinant gives a proper divisor. This conclusion is
independent of how a scheduler chooses its eligible line or scans its rows. -/
theorem split_on_curve {p q : ℕ} (pp : p.Prime) (pq : q.Prime) (ne : p≠q)
    (lp : 3<p) (lq : 3<q) {D : ℤ} (valid : D ∈ ThreeTargetRepresentations.values)
    (sq : IsSquare (D : ZMod (p*q))) :
    ∃ r t : ZMod (p*q), ∃ u : ThreeNormCurves.Point (p*q) D r,
      ∃ v : ThreeNormCurves.Point (p*q) D t,
      let g := ((u.x : ZMod (p*q))*v.y - (v.x : ZMod (p*q))*u.y).val.gcd (p*q)
      1 < g ∧ g < p*q ∧ g ∣ p*q := by
  letI : Fact p.Prime := ⟨pp⟩
  letI : Fact q.Prime := ⟨pq⟩
  have np := Nat.mul_pos pp.pos pq.pos
  letI : NeZero (p*q) := ⟨np.ne'⟩
  have cop := (Nat.coprime_primes pp pq).mpr ne
  have odd := (pp.odd_of_ne_two (by omega)).mul (pq.odd_of_ne_two (by omega))
  have no3 : ¬3∣p*q := by
    intro dv
    rcases Nat.prime_three.dvd_mul.mp dv with h|h
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp h; omega
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pq).mp h; omega
  obtain ⟨r,sr⟩ := sq
  have rr : r^2=D := by simpa [pow_two] using sr.symm
  obtain ⟨t,tr,diff,opposite⟩ := ThreeTargetRepresentations.second_root cop lp lq valid r rr
  obtain ⟨pos,small,ns⟩ := ThreeTargetRepresentations.value_bounds valid
  obtain ⟨ur⟩ := SmallDiscriminantLattice.exists_representation np odd pos small ns r rr
  obtain ⟨ut⟩ := SmallDiscriminantLattice.exists_representation np odd pos small ns t tr
  obtain ⟨u⟩ := ThreeNormCurves.normalize np odd no3 valid rr ur
  obtain ⟨v⟩ := ThreeNormCurves.normalize np odd no3 valid tr ut
  exact ⟨r,t,u,v,ThreeNormCurves.factor u v rr tr diff opposite⟩

noncomputable def mask (i : ℕ) : Mask 3 := fun j => if i.testBit j.val then 1 else 0

noncomputable def discriminant (i : ℕ) : ℤ := word ThreeRootTargets.signed (mask i)

theorem target_table : (List.range' 1 7).map discriminant = ThreeTargetRepresentations.values :=
  by decide +kernel

/-- Every listed line contained in the public Jacobi kernel splits the
product on at least one of its three reduced norm curves. The two first
public zero-bit checks imply the third by linearity. -/
theorem listed_split {p q : ℕ} (pp : p.Prime) (pq : q.Prime) (ne : p≠q)
    (lp : 3<p) (lq : 3<q) (l : ℕ × ℕ × ℕ) (mem : l∈lines)
    (ha : publicRow (p*q) ThreeRootTargets.signed (mask l.1) = 0)
    (hb : publicRow (p*q) ThreeRootTargets.signed (mask l.2.1) = 0) :
    ∃ i ∈ points l, ∃ r t : ZMod (p*q),
      ∃ u : ThreeNormCurves.Point (p*q) (discriminant i) r,
      ∃ v : ThreeNormCurves.Point (p*q) (discriminant i) t,
      let g := ((u.x : ZMod (p*q))*v.y - (v.x : ZMod (p*q))*u.y).val.gcd (p*q)
      1 < g ∧ g < p*q ∧ g ∣ p*q := by
  letI : Fact p.Prime := ⟨pp⟩
  letI : Fact q.Prime := ⟨pq⟩
  have gen {k : ℕ} [Fact k.Prime] (large : 3<k) (i : Fin 3) :
      (ThreeRootTargets.signed i : ZMod k) ≠ 0 := by
    have two : (2 : ZMod k) ≠ 0 := by exact_mod_cast ZMod.prime_ne_zero k 2 (by omega)
    have three : (3 : ZMod k) ≠ 0 := by exact_mod_cast ZMod.prime_ne_zero k 3 (by omega)
    fin_cases i <;> simp [ThreeRootTargets.signed,two,three]
  have add : ∀ l∈lines, mask l.1 + mask l.2.1 = mask l.2.2 := by decide +kernel
  have valid : ∀ l∈lines, ∀ i∈points l, discriminant i ∈ ThreeTargetRepresentations.values :=
    by decide +kernel
  have h := eligible_line ((Nat.coprime_primes pp pq).mpr ne) ThreeRootTargets.signed
    (gen lp) (gen lq) _ _ ha hb
  rw [add _ mem] at h
  obtain ⟨i,hi,sq⟩ : ∃ i∈points l, IsSquare (discriminant i : ZMod (p*q)) := by
    rcases h with h|h|h
    · exact ⟨l.1,by simp [points],h⟩
    · exact ⟨l.2.1,by simp [points],h⟩
    · exact ⟨l.2.2,by simp [points],h⟩
  exact ⟨i,hi,split_on_curve pp pq ne lp lq (valid _ mem i hi) sq⟩

/-- A race rotates through the active curves, executing at most one block
from each per round. At a success in round t each curve has received at
most t blocks (or its smaller exhaustion budget). -/
theorem race_budget (a b c t : ℕ) :
    min a t + min b t + min c t ≤ 3*t := by
  have := min_le_right a t
  have := min_le_right b t
  have := min_le_right c t
  omega

end PrimeFactors.SignedCurveSchedule
