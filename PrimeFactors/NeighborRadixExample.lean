import PrimeFactors.LowBitsCarryMenu

/-! A divisor of the product's neighbor selects a useful carry radix that
every comparable dyadic radix misses, even with an arbitrary high carry. -/

namespace PrimeFactors.NeighborRadixExample
open PredictedTraceCarries LowBitsCarryMenu

/-- Check candidates in increasing order, starting at lo and taking length
consecutive integers. Only N is used in the divisibility test. -/
noncomputable def firstNeighborPrime (n lo length : ℕ) : Option ℕ :=
  ((List.range length).map (lo+·)).find? fun d => decide d.Prime && (n-1)%d==0

theorem neighbor_split :
    firstNeighborPrime 135137 32 481=some 41 ∧
    coefficient 135137 41 0=80 ∧ label 135137 41 0 (-2)=6578 ∧
    probe 135137 41 0 (-2)=some 337 ∧
    337*401=135137 ∧ Nat.Prime 337 ∧ Nat.Prime 401 := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,?_,
    by decide +kernel,by decide +kernel,by decide +kernel⟩
  apply probe_of_square (c:=80) (t:=6578) (r:=162) <;> decide +kernel

/-- Every signed displacement of the first prime supplies a signed divisor
in its residue class. This test does not require a high-carry budget. -/
private theorem first_residue {d p q : ℕ} {w : ℤ} (ne : w≠0) (hit : Lift d p q w) :
    ∃ t∈w.natAbs.divisors, (t:ℤ)%d=(p:ℤ)%d ∨ (-(t:ℤ))%d=(p:ℤ)%d := by
  obtain ⟨a,b,eq⟩ := hit
  let u := (p:ℤ)-a*d
  have dv : u∣w := ⟨(q:ℤ)-b*d,eq⟩
  have same : u ≡ (p:ℤ) [ZMOD (d:ℤ)] := Int.modEq_iff_dvd.mpr ⟨a,by dsimp [u]; ring⟩
  refine ⟨u.natAbs,Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr dv,Int.natAbs_ne_zero.mpr ne⟩,?_⟩
  rcases Int.natAbs_eq u with pos|neg
  · left; rw [←pos];exact same
  · right; rw [←neg];exact same

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem table :
    ∀ e∈Finset.Icc 5 9, ∀ k∈Finset.Icc (-4:ℤ) 4,
      let d := 2^e
      let w := output 135137 d k
      w≠0 ∧ ¬∃ t∈w.natAbs.divisors,
        (t:ℤ)%d=(337:ℤ)%d ∨ (-(t:ℤ))%d=(337:ℤ)%d := by decide +kernel

/-- All five dyadic radices in [32,512] miss for every high carry, including
accidental successful probes, when the low correction has magnitude at most four. -/
theorem dyadic_miss (e : ℕ) (lo : 5≤e) (hi : e≤9) (h k : ℤ) (cap : |k|≤4) :
    probe 135137 (2^e) h k=none := by
  cases hit : probe 135137 (2^e) h k with
  | none => rfl
  | some f =>
    obtain ⟨nz,excluded⟩ := table e (Finset.mem_Icc.mpr ⟨lo,hi⟩) k (Finset.mem_Icc.mpr (abs_le.mp cap))
    exact False.elim (excluded (first_residue nz (lift_of_probe (p:=337) (q:=401)
      (by decide +kernel) (by decide +kernel) (by decide) hit)))

end PrimeFactors.NeighborRadixExample
