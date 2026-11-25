import PrimeFactors.ThreeUnitFactorialWindows

/-! A complete disjoint odd grid for one-sided, product-dependent divisor windows.
The final window may extend beyond the feasible range. -/

namespace PrimeFactors.UnitWindowCover

open Polynomial CoupledDivisorWindow

/-- First and past-last odd candidate indices, with d=2j+1. -/
def start (n : ℕ) := lower n/2
def stop (n : ℕ) := (n.sqrt+1)/2
def positions (n : ℕ) := stop n-start n
def locations (n H : ℕ) := (positions n + H)/(H+1)
def first (n H i : ℕ) := 2*(start n+i*(H+1))+1

/-- The input itself bounds the length of its smaller-divisor interval. -/
theorem positions_bound {n : ℕ} (big : 2^2047≤n) :
    14*positions n ≤ 3*2^1023+14 := by
  let X : ℕ := 2^1023
  have square : n.sqrt^2≤2*X*lower n := by
    have eqn : 2*X=2^1024 := by decide +kernel
    rw [eqn]
    exact (Nat.sqrt_le' n).trans (product_le n)
  have am : 98 * X * lower n ≤ (5*lower n+5*X)^2 := by
    have e : (98:ℤ)*(X:ℤ)*(lower n:ℤ) ≤ (5*(lower n:ℤ)+5*(X:ℤ))^2 := by
      nlinarith only [sq_nonneg ((lower n:ℤ)-(X:ℤ)),mul_nonneg (Int.natCast_nonneg X) (Int.natCast_nonneg (lower n))]
    exact_mod_cast e
  have tangent : 7*n.sqrt≤5*lower n+5*X := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    calc
      (7*n.sqrt)^2 = 49*n.sqrt^2 := by ring
      _ ≤ 49*(2*X*lower n) := Nat.mul_le_mul_left _ square
      _ = 98*X*lower n := by ring
      _ ≤ _ := am
  have floor : X≤lower n := lower_size big
  change 14*((n.sqrt+1)/2-lower n/2) ≤ 3*X+14
  omega

/-- The uniform bound for a window size can be checked without computing any factor. -/
theorem count_lt {n H A : ℕ} (big : 2^2047≤n)
    (budget : 3*2^1023+14+14*H<14*(A*(H+1))) : locations n H<A := by
  unfold locations
  apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr
  have h := positions_bound big
  nlinarith only [h,budget]

/-- Quantifying over the whole list guarantees a root somewhere, without
presupposing which index has the factor. Each ordinary polynomial uses public data. -/
noncomputable def At (n H k c : ℕ) : Prop :=
  ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤k ∧ ∀ x d : ℕ, d∣n → d=c+2*x →
    lower n≤d → x≤H → F.eval (x:ℤ)=0

theorem cover {n H k : ℕ} (atEach : ∀ c, Odd c → At n H k c) :
    ∃ F : Fin (locations n H) → ℤ[X], (∀ i, F i≠0 ∧ (F i).roots.toFinset.card≤k) ∧
      ∀ d q : ℕ, n=d*q → Odd d → d≤q → q≤2^1024 → ∃ i x,
        d=first n H i.val+2*x ∧ x≤H ∧ (F i).eval (x:ℤ)=0 := by
  have rows (i : Fin (locations n H)) := atEach (first n H i.val) ⟨_,rfl⟩
  choose F nz rank works using rows
  refine ⟨F,fun i => ⟨nz i,rank i⟩,?_⟩
  intro d q pair odd ord cap
  obtain ⟨j,hj⟩ := odd
  have floor := lower_le_factor pair cap
  have ceiling := Nat.le_sqrt.mpr (show d*d≤n by rw [pair]; exact Nat.mul_le_mul_left d ord)
  have lo : start n≤j := by unfold start; omega
  have hi : j<stop n := by unfold stop; omega
  let a := j-start n
  have ha : a<positions n := by dsimp [positions,a]; omega
  let i := a/(H+1)
  let x := a%(H+1)
  have bound : i<locations n H := by
    have lowerI : (i+1)*(H+1)≤positions n+H := by
      rw [Nat.add_mul,one_mul]
      have used : i*(H+1)≤a := Nat.div_mul_le_self ..
      omega
    exact Nat.lt_of_succ_le ((Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr lowerI)
  have hx : x≤H := Nat.le_of_lt_succ (Nat.mod_lt a (Nat.succ_pos H))
  have pos : d=first n H i+2*x := by
    have z := Nat.mod_add_div a (H+1)
    rw [Nat.mul_comm (H+1)] at z
    change x + i*(H+1)=a at z
    unfold first
    dsimp only [a] at z
    omega
  exact ⟨⟨i,bound⟩,x,pos,hx,works ⟨i,bound⟩ x d (pair ▸ dvd_mul_right ..) pos floor hx⟩

set_option exponentiation.threshold 4096

/-- Certified coverage and number of locations for the 145-row family. -/
theorem degree144 {n : ℕ} (big : 2^2047≤n) (odd : Odd n)
    (cop : n.Coprime (ThreeUnitFactorialWindows.denominator 144)) :
    locations n (2^515)<2^506 ∧ ∃ F : Fin (locations n (2^515)) → ℤ[X],
      (∀ i, F i≠0 ∧ (F i).roots.toFinset.card≤144) ∧ ∀ d q : ℕ, n=d*q →
      Odd d → d≤q → q≤2^1024 → ∃ i x, d=first n (2^515) i.val+2*x ∧
      x≤2^515 ∧ (F i).eval (x:ℤ)=0 := by
  refine ⟨count_lt big (by decide +kernel),cover ?_⟩
  intro c hc
  let t := ((n:ℤ)-c)/2
  have anc : (n:ℤ)∣(c:ℤ)+2*t := by
    obtain ⟨b,hb⟩ := odd
    obtain ⟨a,ha⟩ := hc
    exact ⟨1,by dsimp only [t];omega⟩
  obtain ⟨F,nz,card,hit⟩ := ThreeUnitFactorialWindows.uniform_window big cop
    (Nat.coprime_two_left.mpr odd).isCoprime anc
  refine ⟨F,nz,card,?_⟩
  intro x d div pos floor near
  exact hit x d (by exact_mod_cast div) (by exact_mod_cast pos) (by exact_mod_cast floor) near

end PrimeFactors.UnitWindowCover
