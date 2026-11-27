import PrimeFactors.UpperConvergentDeficit
import PrimeFactors.Certificate

/-! Read a block of intermediate fractions at once. Only the product, the trial exponent,
the common prime width and the current Euclidean rows enter the interval endpoints. -/
namespace PrimeFactors.IntermediateTotientRows

open UpperConvergentDeficit

/-- First and last positive indices compatible with a deficit in [L,2L). -/
def first (u v L a₀ a₁ : ℕ) := 1+(u-2*L*a₀)/(v+2*L*a₁)
def last (u v L a₀ a₁ : ℕ) := min (u/v) ((u-L*a₀)/(v+L*a₁))

/-- This equivalence includes the first upper block, where a₁=0, and empty intervals. -/
theorem interval {u v L a₀ a₁ t : ℕ} (vp : 0<v) :
    first u v L a₀ a₁ ≤ t ∧ t ≤ last u v L a₀ a₁ ↔
      1≤t ∧ t≤u/v ∧ L*(a₀+t*a₁)+t*v≤u ∧ u<2*L*(a₀+t*a₁)+t*v := by
  have p₁ : 0<v+L*a₁ := by omega
  have p₂ : 0<v+2*L*a₁ := by omega
  rw [first,last,le_min_iff]
  have lower {t : ℕ} (tp : 0<t) :
      (u-2*L*a₀)/(v+2*L*a₁)<t ↔ u<2*L*a₀+t*(v+2*L*a₁) := by
    rw [Nat.div_lt_iff_lt_mul p₂]
    have : 0<t*(v+2*L*a₁) := Nat.mul_pos tp p₂
    omega
  have upper {t : ℕ} (tp : 0<t) :
      t≤(u-L*a₀)/(v+L*a₁) ↔ L*a₀+t*(v+L*a₁)≤u := by
    rw [Nat.le_div_iff_mul_le p₁]
    have : 0<t*(v+L*a₁) := Nat.mul_pos tp p₁
    omega
  constructor
  · rintro ⟨lo,q,hi⟩
    have tp : 0<t := (by positivity : 0<1+(u-2*L*a₀)/(v+2*L*a₁)).trans_le lo
    have a := (lower tp).mp (by omega)
    have b := (upper tp).mp hi
    exact ⟨tp,q,by nlinarith only [b],by nlinarith only [a]⟩
  · rintro ⟨tp,q,lo,hi⟩
    have a := (lower tp).mpr (by nlinarith only [hi])
    have b := (upper tp).mpr (by nlinarith only [lo])
    exact ⟨by omega,q,b⟩

/-- On an upper block the interval selects exactly every positive intermediate test in the
advertised width band. The other endpoint of the block is a lower convergent. -/
theorem width_iff {N E u v L t : ℕ} {x y : Row} (vp : 0<v)
    (high : N*x.a=E*x.b+u) (low : E*y.b=N*y.a+v) :
    first u v L x.a y.a ≤ t ∧ t ≤ last u v L x.a y.a ↔
      1≤t ∧ t≤u/v ∧ E*(step x y t).b+L*(step x y t).a≤N*(step x y t).a ∧
        N*(step x y t).a < E*(step x y t).b+2*L*(step x y t).a := by
  rw [interval vp]
  simp only [step]
  have eq : N*(x.a+t*y.a)+t*v=E*(x.b+t*y.b)+u := by
    nlinarith only [high,congrArg (fun z => t*z) low]
  omega

/-- A lower block, up to its actual quotient, has no positive-width candidates.
The strict positivity of the row numerator excludes the zeroth convergent 0/1. -/
theorem lower_skips {N E u v L t : ℕ} {x y : Row} (vp : 0<v) (lp : 0<L)
    (tp : t≤u/v) (ap : 0<(step x y t).a)
    (low : E*x.b=N*x.a+u) (high : N*y.a=E*y.b+v) :
    N*(step x y t).a < E*(step x y t).b+L*(step x y t).a := by
  have tv := (Nat.le_div_iff_mul_le vp).mp tp
  have base : N*(step x y t).a ≤ E*(step x y t).b := by
    dsimp only [step]
    nlinarith only [low,congrArg (fun z => t*z) high,tv]
  have add := Nat.mul_pos lp ap
  omega

private theorem reduced {x y : Row} (near : x.a*y.b=x.b*y.a+1) (t : ℕ) :
    (step x y t).a.Coprime (step x y t).b := by
  have det : (step x y t).a*y.b=(step x y t).b*y.a+1 := by
    dsimp only [step]
    nlinarith only [near]
  apply Nat.coprime_of_mul_modEq_one y.b
  change ((step x y t).a*y.b)%(step x y t).b=1%(step x y t).b
  rw [det]
  simp [Nat.add_mod]

/-- The totient candidate E*b/a is integral exactly when the row numerator divides E. -/
theorem integral_iff {x y : Row} (near : x.a*y.b=x.b*y.a+1) (E t : ℕ) :
    (step x y t).a ∣ E*(step x y t).b ↔ (step x y t).a∣E :=
  ⟨(reduced near t).dvd_of_dvd_mul_right,fun h => dvd_mul_of_dvd_left h _⟩

/-- The forward complementary-divisor identity also holds in the initial block. -/
theorem complementary_divisor {x y : Row} {N E v D t : ℕ}
    (near : x.a*y.b=x.b*y.a+1) (low : E*y.b=N*y.a+v)
    (eq : E*(step x y t).b+D*(step x y t).a=N*(step x y t).a) :
    E=(step x y t).a*(v+y.a*D) := by
  let a := (step x y t).a
  let b := (step x y t).b
  have det : a*y.b=b*y.a+1 := by dsimp only [a,b,step]; nlinarith only [near]
  change E*b+D*a=N*a at eq
  change E=a*(v+y.a*D)
  nlinarith only [congrArg (fun z => E*z) det,congrArg (fun z => a*z) low,
    congrArg (fun z => y.a*z) eq]

/-- For a row with an integral candidate, the complementary divisor of E has the
particularly simple form v + y.a * D, where D = N−F. With y.a positive this determines D. -/
theorem divisor_pair {x y : Row} {N E v D t : ℕ}
    (near : x.a*y.b=x.b*y.a+1) (low : E*y.b=N*y.a+v) (yp : 0<y.a) :
    E*(step x y t).b+D*(step x y t).a=N*(step x y t).a ↔
      E=(step x y t).a*(v+y.a*D) := by
  let a := (step x y t).a
  let b := (step x y t).b
  have det : a*y.b=b*y.a+1 := by dsimp only [a,b,step]; nlinarith only [near]
  constructor
  · exact complementary_divisor near low
  · intro eq
    change E=a*(v+y.a*D) at eq
    apply Nat.eq_of_mul_eq_mul_right yp
    change (E*b+D*a)*y.a=(N*a)*y.a
    nlinarith only [congrArg (fun z => E*z) det,congrArg (fun z => a*z) low,eq]

/-- Once both current rows are strictly below the positive deficit band, every forward
intermediate update stays below it. This inequality is preserved on shifting to the next pair. -/
theorem stays_below {N E L : ℕ} {x y : Row} (t : ℕ)
    (hx : N*x.a<E*x.b+L*x.a) (hy : N*y.a≤E*y.b+L*y.a) :
    N*(step x y t).a<E*(step x y t).b+L*(step x y t).a := by
  dsimp only [step]
  nlinarith only [hx,Nat.mul_le_mul_left t hy]

/-- The first upper block consists of 1/t. Integrality is automatic; the totient candidate
is simply the t-th multiple of E, which may precede the canonical last multiple. -/
theorem first_block (E F t : ℕ) :
    let z := step ⟨1,0⟩ ⟨0,1⟩ t
    E*z.b=F*z.a ↔ F=E*t := by simp [step,eq_comm]

/-- The first nine-bit example in the fixed census that the ordinary rows, first block and
base-two gcd all miss. The retained index recovers F=102060 and the two certified primes. -/
theorem later_example :
    102709*1=2520*40+1909 ∧ 2520*41=102709*1+611 ∧
    first 1909 611 512 1 1=1 ∧ last 1909 611 512 1 1=1 ∧ 1909/611=3 ∧
    step ⟨1,40⟩ ⟨1,41⟩ 1=⟨2,81⟩ ∧ 2520*81=102060*2 ∧
    102709+1-102060=271+379 ∧ ExactFactorization 102709 [271,379] := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,rfl,by decide,by decide,?_⟩
  exact .cons (n:=379) (by norm_num) (.cons (n:=1) (by norm_num) exactFactorization_nil)

end PrimeFactors.IntermediateTotientRows
