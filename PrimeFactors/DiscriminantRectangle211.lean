import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Prime
set_option maxRecDepth 4096
/-! Exact single-prime window restrictions. The integer mask contains two copies
of the nonsquare residues modulo 211. Every bit used in the proof is checked
against a square root calculation in the field. -/
namespace PrimeFactors.DiscriminantRectangle211

private def nonsquares : ℕ := 6628610593850189922452210652971592050206168034004709187632010941997954730651794159533429138139654970292346227558869937273869708

private theorem classify : ∀ x : Fin 422, nonsquares.testBit x.val = true ↔
    (((x.val:ZMod 211)^53)^2 ≠ (x.val:ZMod 211)) := by decide +kernel

private theorem squares : ∀ r : Fin 211, ((r*r)^53)^2=r*r := by decide +kernel

private theorem bit_iff {v : ℕ} (bound : v<422) :
    nonsquares.testBit v = true ↔ ¬ IsSquare (v : ZMod 211) := by
  rw [classify ⟨v,bound⟩]
  constructor
  · rintro h ⟨r,hr⟩
    rw [hr] at h
    exact h (squares r)
  · rintro h yes
    exact h ⟨(v:ZMod 211)^53, by rw [← sq,yes]⟩

/-- The bit at the negative of a product class records failure at every supplied trace. -/
def mask (s : ZMod 211) (sites : List ℕ) : ℕ :=
  sites.foldr (fun i tail => (nonsquares >>> (((s+(i:ZMod 211))^2).val)) &&& tail) (2^211-1)

theorem mask_iff (s c : ZMod 211) (sites : List ℕ) :
    (mask s sites).testBit (-c).val = true ↔ ∀ j ∈ sites, ¬IsSquare ((s+(j:ZMod 211))^2-c) := by
  induction sites with
  | nil =>
    change (2^211-1:ℕ).testBit (-c).val = true ↔ _
    rw [Nat.testBit_two_pow_sub_one]
    simp [ZMod.val_lt]
  | cons i sites ih =>
    let u : ZMod 211 := (s+(i:ZMod 211))^2
    have b : u.val+(-c).val<422 := by
      have := ZMod.val_lt u
      have := ZMod.val_lt (-c)
      omega
    change ((nonsquares >>> u.val) &&& mask s sites).testBit (-c).val = true ↔ _
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Bool.and_eq_true, bit_iff b, ih]
    simp [Nat.cast_add,ZMod.natCast_zmod_val,u,sub_eq_add_neg]

private theorem complete : ∀ s : Fin 211, mask s (List.range 19) = 0 := by decide +kernel

theorem every_nineteen (s c : ZMod 211) :
    ∃ i : ℕ, i < 19 ∧ IsSquare ((s+(i:ZMod 211))^2-c) := by
  by_contra! h
  have all := (mask_iff s c (List.range 19)).mpr (by simpa using h)
  rw [complete s] at all
  simp at all

theorem eighteen : ∀ j : ℕ, j < 18 → ¬IsSquare (((97:ZMod 211)+(j:ZMod 211))^2-178) := by
  have hit : (mask (97:ZMod 211) (List.range 18)).testBit (-(178:ZMod 211)).val = true := by decide +kernel
  simpa using (mask_iff _ _ _).mp hit

private def positions (m : ℕ) : List ℕ :=
  if m=0 then [] else (List.range 211).filter m.testBit

private theorem mem_positions (m : ℕ) {i : ℕ} (bound : i<211) :
    i ∈ positions m ↔ m.testBit i = true := by
  by_cases eq : m=0
  · simp [positions,eq]
  · simp [positions,eq,bound]

/-- An executable complete list of the product classes excluded at all the given sites. -/
def excluded (s : ZMod 211) (sites : List ℕ) : List (ZMod 211) :=
  (positions (mask s sites)).map (fun j : ℕ => -(j : ZMod 211))

theorem mem_excluded (s c : ZMod 211) (sites : List ℕ) :
    c ∈ excluded s sites ↔ ∀ j ∈ sites, ¬ IsSquare ((s+(j:ZMod 211))^2-c) := by
  rw [← mask_iff, ← mem_positions _ (ZMod.val_lt (-c))]
  unfold excluded
  constructor
  · intro h
    obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    have lt : j < 211 := by
      by_cases hz : mask s sites=0
      · simp [positions,hz] at hj
      · have ht : j<211 ∧ (mask s sites).testBit j = true := by simpa [positions,hz] using hj
        exact ht.1
    have ec : (-c).val = j := by
      rw [← e,neg_neg,ZMod.val_natCast_of_lt lt]
    rwa [ec]
  · intro h
    exact List.mem_map.mpr ⟨(-c).val,h,by simp⟩

/-- The ordered list of squares of ten consecutive traces. -/
def squaredSites (s : ZMod 211) : List (ZMod 211) :=
  (List.range 10).map (fun j => (s+(j:ZMod 211))^2)

private theorem countTen : ∀ s : Fin 211, (positions (mask s (List.range 10))).length ≤
    if (squaredSites s).Nodup then 2 else 7 := by decide +kernel

/-- At most seven classes miss ten consecutive traces, and at most two if the
ten squares are distinct. Both limits are attained. -/
theorem ten (s : ZMod 211) : (excluded s (List.range 10)).length ≤ 7 ∧
    (((List.range 10).map (fun j => (s+(j:ZMod 211))^2)).Nodup →
      (excluded s (List.range 10)).length ≤ 2) := by
  have counted := countTen s
  simp only [excluded,List.length_map]
  change _ ≤ 7 ∧ ((squaredSites s).Nodup → _ ≤ _)
  by_cases distinct : (squaredSites s).Nodup
  · rw [if_pos distinct] at counted
    exact ⟨counted.trans (by decide), fun _ => counted⟩
  · rw [if_neg distinct] at counted
    exact ⟨counted, fun h => (distinct h).elim⟩

theorem sharp_ten : (excluded 101 (List.range 10)).length=7 ∧
    (squaredSites 170).Nodup ∧ (excluded 170 (List.range 10)).length=2 := by decide +kernel

local instance : Fact (Nat.Prime 211) := ⟨by norm_num⟩

/-- A nonzero stride can be normalized; the zeroth label and the multiplier
need not be the same for different directions. -/
theorem any_stride (start C k : ZMod 211) (unit : k ≠ 0) :
    ∃ i : ℕ, i < 19 ∧ IsSquare ((start+k*(i:ZMod 211))^2-C) := by
  obtain ⟨i,hi,r,hr⟩ := every_nineteen (start/k) (C/k^2)
  refine ⟨i,hi,k*r,?_⟩
  calc
    _ = k^2*((start/k+(i:ZMod 211))^2-C/k^2) := by field_simp; ring
    _ = _ := by rw [hr]; ring

/-- Exactly these two classes miss the ten traces at normalized start 170. -/
theorem two_products : excluded 170 (List.range 10) = [147,12] := by decide +kernel

end PrimeFactors.DiscriminantRectangle211
