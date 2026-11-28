import PrimeFactors.CeilingShiftPopulation
import PrimeFactors.UniformDivisorCount
import PrimeFactors.GaussianGateAggregateCost

/-! Which positions before the true Fermat midpoint can admit a negative
integer shift? The distance to that midpoint divides the squared half-gap. -/
namespace PrimeFactors.CeilingShiftDistances

open Finset CeilingShiftPopulation MixedPrefixSample SeparatedMonotonePopulation
open private PrimeFactors.GaussianGateAggregateCost.info from PrimeFactors.GaussianGateAggregateCost
open scoped Classical
set_option exponentiation.threshold 4096
attribute [local irreducible] eligible primes far

/-- At a center `m` at distance `b` below the midpoint `p+d`, the
shift equation is exactly a divisor-pair equation for the squared half-gap. -/
theorem shift_equation {p d m b a : ℕ} (center : m+b=p+d) :
    (p+a)*(p+2*d+a)=(m+a)^2 ↔ d^2=b*(2*m+b+2*a) := by
  have squares : (m+b)^2=p*(p+2*d)+d^2 := by rw [center]; ring
  have scaled := congrArg (fun n : ℕ => a*n) center
  dsimp at scaled
  constructor <;> intro h <;> nlinarith only [squares,scaled,h]

theorem at_distance {p d m b : ℕ} (center : m+b=p+d)
    (above : p*(p+2*d)<m^2) :
    (∃ a, Hit p (p+2*d) m a) ↔ ∃ c, b*c=d^2 ∧ Even (b+c) := by
  constructor
  · rintro ⟨a,_,ha⟩
    exact ⟨2*m+b+2*a,((shift_equation center).mp ha).symm,m+b+a,by ring⟩
  · rintro ⟨c,mul,k,even⟩
    have sq : (m+b)^2=p*(p+2*d)+d^2 := by rw [center]; ring
    have lt : b*(2*m+b)<b*c := by nlinarith only [above,sq,mul]
    have order := Nat.lt_of_mul_lt_mul_left lt
    let a := k-(m+b)
    have value : c=2*m+b+2*a := by dsimp [a]; omega
    exact ⟨a,by dsimp [a]; omega,(shift_equation center).mpr (mul.symm.trans (by rw [value]))⟩

noncomputable def interval (p q : ℕ) := Ico (ceilSqrt (p*q)) ((p+q)/2)
noncomputable def centers (p q : ℕ) := (interval p q).filter (fun m => ∃ a, Hit p q m a)

/-- Every earlier center has a different positive distance, so it has to
use a different divisor. The shift itself is granted for free here. -/
theorem count {p d : ℕ} (dp : 0<d) :
    (centers p (p+2*d)).card ≤ (d^2).divisors.card := by
  let dist (m : ℕ) := p+d-m
  have inside {m : ℕ} (hm : m∈centers p (p+2*d)) : m<p+d := by
    have h := (mem_Ico.mp (mem_filter.mp hm).1).2
    omega
  apply card_le_card_of_injOn (s:=centers p (p+2*d)) (t:=(d^2).divisors) dist
  · intro m hm
    have lt := inside hm
    obtain ⟨a,_,eqn⟩ := (mem_filter.mp hm).2
    have mid : m+dist m=p+d := by dsimp [dist]; omega
    exact Nat.mem_divisors.mpr ⟨⟨_,(shift_equation mid).mp eqn⟩,(pow_pos dp 2).ne'⟩
  · intro m hm n hn same
    have ml := inside hm
    have nl := inside hn
    change p+d-m=p+d-n at same
    omega

def halfGap (z : ℕ×ℕ) := (z.2-z.1)/2

theorem gap_data {p q : ℕ} (h : (p,q)∈eligible) :
    q=p+2*halfGap (p,q) ∧ 0<halfGap (p,q) ∧ halfGap (p,q)<2^1022 := by
  obtain ⟨lo,lt,hi,⟨i,pi⟩,⟨j,qj⟩⟩ := PrimeFactors.GaussianGateAggregateCost.info h
  dsimp [halfGap]
  omega

theorem count_pair {p q : ℕ} (h : (p,q)∈eligible) :
    (centers p q).card ≤ ((halfGap (p,q))^2).divisors.card := by
  obtain ⟨eqn,dp,_⟩ := gap_data h
  exact (congrArg (fun n => (centers p n).card) eqn).le.trans (count dp)

set_option exponentiation.threshold 100000 in
theorem uniform {p q : ℕ} (h : (p,q)∈eligible) :
    (centers p q).card < 2^239 := by
  obtain ⟨_,dp,limit⟩ := gap_data h
  have high : (halfGap (p,q))^2 < 2^2044 := calc
    _ < (2^1022)^2 := Nat.pow_lt_pow_left limit (by decide)
    _ = _ := by rw [←pow_mul]
  apply (count_pair h).trans_lt
  apply (Nat.pow_lt_pow_iff_left (by decide : 336≠0)).mp
  rw [←pow_mul]
  exact (UniformDivisorCount.below_power_two (pow_pos dp _) high).trans_le
    (Nat.pow_le_pow_right (by decide) (by decide : 14882+32*2044≤239*336))

/-- The large-gap majority has this many consecutive positions strictly
before the true midpoint. The last (successful) Fermat test is excluded. -/
theorem interval_lower {p q : ℕ} (h : (p,q)∈far) : 2^985 ≤ (interval p q).card := by
  obtain ⟨member,gap⟩ := mem_far.mp h
  obtain ⟨eqn,_,_⟩ := gap_data member
  obtain ⟨lo,ord,hi,_,_⟩ := PrimeFactors.GaussianGateAggregateCost.info member
  let d := halfGap (p,q)
  let M := p+d
  change q=p+2*d at eqn
  change 2^1006≤q-p at gap
  have lower : 2^1005≤d := by omega
  have mid : 2*M=p+q := by dsimp [M]; omega
  have room : 2^985≤M := by omega
  let m := M-2^985
  have back : m+2^985=M := Nat.sub_add_cancel room
  have relation : M^2=p*q+d^2 := by dsimp [M]; rw [eqn]; ring
  have loss : 2*M*2^985≤d^2 := calc
    _ ≤ 2*(2^1024)*2^985 := by apply Nat.mul_le_mul_right; omega
    _ = (2^1005)^2 := by decide +kernel
    _ ≤ d^2 := Nat.pow_le_pow_left lower _
  have subtract : m^2+2*M*2^985=M^2+(2^985)^2 := by rw [←back]; ring
  have first := ceilSqrt_le_iff.mpr (by omega : p*q≤m^2)
  rw [interval,Nat.card_Ico]
  omega

end PrimeFactors.CeilingShiftDistances
