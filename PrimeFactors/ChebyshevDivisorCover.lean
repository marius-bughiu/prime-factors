import PrimeFactors.ChebyshevDivisorWindow
import PrimeFactors.FeasibleDivisorCover

namespace PrimeFactors.ChebyshevDivisorCover

open Polynomial FeasibleDivisorCover

set_option exponentiation.threshold 4096

/-- One larger window covers an adjacent pair of addresses from the two-tier grid. -/
def locations (n : ℕ) (b : Bool) := (count n b+1)/2

def midpoint (n : ℕ) (b : Bool) (i : ℕ) := center n b (2*i)+2*radius b

private lemma pair_address (l w i : ℕ) (x : ℤ) (near : |x|≤(w:ℤ)) :
    ∃ y : ℤ, ((2*(l+i*(2*w)+w)+1:ℕ):ℤ)+2*x =
      ((2*(l+2*(i/2)*(2*w)+w)+1+2*w:ℕ):ℤ)+2*y ∧ |y| ≤ 2*(w:ℤ) := by
  obtain ⟨lo,hi⟩ := abs_le.mp near
  have rem := Nat.mod_lt i (by decide : 0<2)
  have split := Nat.div_add_mod i 2
  rcases (show i=2*(i/2) ∨ i=2*(i/2)+1 by omega) with h|h
  · refine ⟨x-w,?_,abs_le.mpr (by omega)⟩
    conv_lhs => rw [h]
    push_cast
    ring
  · refine ⟨x+w,?_,abs_le.mpr (by omega)⟩
    conv_lhs => rw [h]
    push_cast
    ring

private theorem at_location {n : ℕ} (big : 2^2047≤n) (parity : Odd n) (b : Bool) (i : ℕ) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤dimension-1 ∧ ∀ x d : ℤ,
      d∣(n:ℤ) → d=(midpoint n b i:ℤ)+2*x → (divisorFloor n b:ℤ)≤d →
      |x|≤2*(radius b:ℤ) → F.eval x=0 := by
  let c := midpoint n b i
  let t := ((n:ℤ)-c)/2
  have anchor : (n:ℤ) ∣ (c:ℤ)+2*t := by
    obtain ⟨s,hs⟩ := parity
    refine ⟨1,?_⟩
    dsimp only [c,t,midpoint,center]
    push_cast
    omega
  have fd : 0 < lower n := Nat.succ_pos _
  have dp : 0<divisorFloor n b := by
    cases b
    · exact fd
    · exact fd.trans_le (le_max_left ..)
  have factorRoom := (weighted_rooms big b).1
  obtain ⟨F,nz,rank,hit⟩ := ChebyshevDivisorWindow.relation_at_dimension
    (r:=dimension) (m:=multiplicity) (n:=n) (U:=radius b) (D:=divisorFloor n b) (by decide)
    (lt_of_lt_of_le (by positivity) big)
    (show 0<radius b by cases b <;> decide +kernel) dp factorRoom t
  refine ⟨F,nz,rank,?_⟩
  intro x d hd pos floor near
  have unit : IsCoprime (2:ℤ) (n:ℤ) := by exact_mod_cast (Nat.coprime_two_left.mpr parity).isCoprime
  exact hit x d hd (QuarticDivisorWindow.progression_offset unit anchor hd pos) floor near

/-- Both tiers combined have fewer than 2^508 public locations. -/
theorem feasible_cover {n : ℕ} (big : 2^2047≤n) (parity : Odd n) :
    locations n false+locations n true < 2^508 ∧
    ∃ F : (b : Bool) → Fin (locations n b) → ℤ[X],
      (∀ b i, F b i ≠ 0 ∧ (F b i).roots.toFinset.card<dimension) ∧
      ∀ d q : ℕ, n=d*q → Odd d → d≤q → q<Q →
        ∃ b, ∃ i : Fin (locations n b), ∃ x : ℤ, (d:ℤ)=midpoint n b i.val+2*x ∧
          |x|≤2*(radius b:ℤ) ∧ x∈(F b i).roots.toFinset := by
  classical
  choose F nz rank roots using at_location big parity
  constructor
  · have budget := center_budget big
    dsimp only [locations]
    omega
  · refine ⟨fun b i => F b i.val,fun b i => ⟨nz _ _,Nat.lt_of_le_of_lt (rank _ _) (by decide)⟩,?_⟩
    intro d q pair odd ord cap
    obtain ⟨b,i,x,floor,pos,near⟩ := address pair odd ord cap
    let j : Fin (locations n b) := ⟨i.val/2,by have := i.isLt; dsimp [locations]; omega⟩
    obtain ⟨y,eq,size⟩ := pair_address (start n b) (radius b) i.val x near
    have atMid : (d:ℤ)=midpoint n b j.val+2*y := pos.trans eq
    have hd : d∣n := ⟨q,pair⟩
    exact ⟨b,j,y,atMid,size,Multiset.mem_toFinset.mpr ((mem_roots (nz b j.val)).mpr
      (roots b j.val y d (by exact_mod_cast hd) atMid (by exact_mod_cast floor) size))⟩

private theorem control_bound (n k : ℕ) (bound : 2^(k+1)<count n false+count n true) :
    2^k < locations n false+locations n true := by
  dsimp only [locations]
  rw [pow_succ] at bound
  omega

/-- The two example products still require exponentially many calls with this schedule. -/
theorem control_floor :
    2^506<locations ChebyshevQuarticScale.fresh false+locations ChebyshevQuarticScale.fresh true ∧
    2^507<locations ChebyshevQuarticScale.crossed false+locations ChebyshevQuarticScale.crossed true := by
  exact ⟨control_bound ChebyshevQuarticScale.fresh 506 control_counts.1.1,
    control_bound ChebyshevQuarticScale.crossed 507 control_counts.2.1⟩

end PrimeFactors.ChebyshevDivisorCover
