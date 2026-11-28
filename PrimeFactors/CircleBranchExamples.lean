import PrimeFactors.CircleBranchReadout

/-! One modulus and two publicly checked targets expose different primes. -/
namespace PrimeFactors.CircleBranchExamples

open CircleBranchCount CircleBranchReadout CircleCoordinateFibers SphereCircleIdentity
open ThreeSquareRadiusCounts

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : Fact (Nat.Prime 29) := ⟨by decide⟩
local instance : Fact (Nat.Prime 41) := ⟨by decide⟩
local instance : Fact (Nat.Prime 31) := ⟨by decide⟩
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

private theorem targets (a : ℤ) (ja : jacobiSym a 77= -1) :
    let T := (level (ZMod 77) (a : ZMod 77) 2).card
    let Z := (marked 77 a).card
    (legendreSym 7 a=1 → T=12 ∧ Z=22) ∧
    (legendreSym 7 a= -1 → T=8 ∧ Z=14) := by
  have rt := readout (p:=7) (q:=11) (by decide) (by decide) (by decide) ja
  have ct := half_count (p:=7) (q:=11) (by decide) (by decide) (by decide) ja
  dsimp only at *
  norm_num [sign] at rt
  change (legendreSym 7 a=1 → _ ∧ _) ∧ (legendreSym 7 a= -1 → _ ∧ _)
  constructor <;> intro s <;> rcases rt with h|h <;> rcases ct with g|g
  all_goals first | omega | exact ⟨by exact_mod_cast h.2.2,g.1⟩

theorem seventy_seven :
    (level (ZMod 77) 2 2).card=12 ∧ (marked 77 2).card=22 ∧
    (level (ZMod 77) 3 2).card=8 ∧ (marked 77 3).card=14 := by
  obtain ⟨a,b⟩ := (targets 2 (by norm_num)).1 (by norm_num)
  obtain ⟨c,d⟩ := (targets 3 (by norm_num)).2 (by norm_num)
  exact ⟨a,b,c,d⟩

private theorem size {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (h : p≠q) (o : p≠2) (v : q≠2) :
    ((circle (ZMod (p*q)) 1).card:ℤ)=((p:ℤ)-sign p)*((q:ℤ)-sign q) := by
  exact semiprime h o v isUnit_one

theorem sizes : (circle (ZMod 1189) 1).card=1120 ∧ (circle (ZMod 1147) 1).card=1152 := by
  have a := size (p:=29) (q:=41) (by decide) (by decide) (by decide)
  have b := size (p:=31) (q:=37) (by decide) (by decide) (by decide)
  norm_num [sign] at a b
  exact ⟨by exact_mod_cast a,by exact_mod_cast b⟩

end PrimeFactors.CircleBranchExamples
