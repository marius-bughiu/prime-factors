import PrimeFactors.CircleMarkEarlyReadout
import PrimeFactors.CircleMarkStoppingMoments

/-! The product supplies a spacing between candidate prime sums. Round either
a mean-rank reading or an early-hit probability on this public progression. -/
namespace PrimeFactors.CircleMarkStoppingDecoder

open CircleMarkEarlyReadout CircleMarkStoppingMoments

/-- The prime sum agrees with N+1 modulo this public modulus. -/
def stride (n : ℕ) : ℕ := if n%4=3 then 8 else 4

private theorem stride_pos (n : ℕ) : 0<stride n := by unfold stride; split <;> decide

theorem sum_lane {p q : ℕ} (po : Odd p) (qo : Odd q) :
    ∃ t : ℕ, p*q+1=(p+q)+stride (p*q)*t := by
  obtain ⟨a,rfl⟩ := po
  obtain ⟨b,rfl⟩ := qo
  have expanded : (2*a+1)*(2*b+1)=4*(a*b)+2*a+2*b+1 := by ring
  unfold stride
  split
  next mixed =>
    have parity : a%2=0 ∨ b%2=0 := by omega
    have even : (a*b)%2=0 := by
      rw [Nat.mul_mod]
      rcases parity with h|h <;> simp [h]
    exact ⟨a*b/2,by omega⟩
  next => exact ⟨a*b,by omega⟩

/-- The closest integer in the residue class of N+1. At a tie it rounds up. -/
noncomputable def roundedSum (n : ℕ) (x : ℚ) : ℤ :=
  (n:ℤ)+1+(stride n:ℤ)*⌊(x-((n:ℚ)+1))/(stride n:ℚ)+1/2⌋

theorem rounded_correct {p q : ℕ} (po : Odd p) (qo : Odd q) {x : ℚ}
    (accurate : |x-((p:ℚ)+q)| < (stride (p*q):ℚ)/2) :
    roundedSum (p*q) x=(p:ℤ)+q := by
  obtain ⟨t,eqn⟩ := sum_lane po qo
  let n := p*q
  let w := stride n
  have wp : (0:ℚ)<w := by exact_mod_cast stride_pos n
  have rep : (n:ℚ)+1 = ((p:ℚ)+q)+(w:ℚ)*t := by exact_mod_cast eqn
  obtain ⟨lower,upper⟩ := abs_lt.mp accurate
  change -((w:ℚ)/2) < x-((p:ℚ)+q) at lower
  have lo : -(t:ℚ)-1/2 < (x-((n:ℚ)+1))/w := by
    apply (lt_div_iff₀ wp).mpr
    linarith only [lower,rep]
  have hi : (x-((n:ℚ)+1))/w < -(t:ℚ)+1/2 := by
    apply (div_lt_iff₀ wp).mpr
    change x-((p:ℚ)+q)<(w:ℚ)/2 at upper
    linarith only [upper,rep]
  have rounded : ⌊(x-((n:ℚ)+1))/w+1/2⌋ = -(t:ℤ) := by
    apply Int.floor_eq_iff.mpr
    push_cast
    exact ⟨by linarith,by linarith⟩
  change (n:ℤ)+1+(w:ℤ)*⌊(x-((n:ℚ)+1))/w+1/2⌋ = (p:ℤ)+q
  rw [rounded]
  have h : (n:ℤ)+1=((p:ℤ)+q)+(w:ℤ)*t := by exact_mod_cast eqn
  linarith

/-- Error strictly less than 1/4 in the mean always suffices. For N ≡ 3 mod 4
the tolerance is 1/2. The actual mean and modulus depend only on N. -/
theorem mean_reading {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {m : ℚ}
    (accurate : |m-rawMoment (p*q) 1| < (stride (p*q):ℚ)/16) :
    roundedSum (p*q) (8*m-2)=(p:ℤ)+q := by
  apply rounded_correct (hp.out.odd_of_ne_two op) (hq.out.odd_of_ne_two oq)
  rw [first_moment diff op oq] at accurate
  rw [abs_lt] at accurate ⊢
  constructor <;> linarith only [accurate.1,accurate.2]

/-- Error sufficient to round an externally obtained normalized early-hit rate.
The input product and the supplied reading are the only inputs to the decoder. -/
theorem early_reading {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a : ℚ} (ha : 0≤a)
    (accurate : (((p*q:ℕ):ℚ)-1)*|a-early (p*q)| < (stride (p*q):ℚ)/2) :
    roundedSum (p*q) (inferredSum (p*q) a)=(p:ℤ)+q := by
  have P : (1:ℚ)<p := by exact_mod_cast hp.out.one_lt
  have Q : (1:ℚ)<q := by exact_mod_cast hq.out.one_lt
  have d : 0≤early (p*q) := by
    rw [early_eq diff op oq]
    exact (add_pos (one_div_pos.mpr (sub_pos.mpr P)) (one_div_pos.mpr (sub_pos.mpr Q))).le
  have out := stability (Nat.mul_pos hp.out.pos hq.out.pos) ha d
  rw [inferred_correct diff op oq] at out
  exact rounded_correct (hp.out.odd_of_ne_two op) (hq.out.odd_of_ne_two oq) (out.trans_lt accurate)

/-- The wider rounding tolerance is strict. At this midpoint the rule rounds
to the next public candidate sum, four above the correct one. -/
theorem midpoint_example : roundedSum 2501 (8*(13+1/4)-2)=106 ∧
    roundedSum 187 (8*(15/4+1/2)-2)=36 := by norm_num [roundedSum,stride]

end PrimeFactors.CircleMarkStoppingDecoder
