import PrimeFactors.PrimitiveIntervalMoment
import PrimeFactors.SumIntervalExclusion

/-! Integer error bounds for a supplied reading of the primitive-character
interval aggregate. The decoder uses its value, one square root, and the
public residue class of the sum of two odd factors. -/
namespace PrimeFactors.PrimitiveIntervalPrecision

open PrimitiveIntervalMoment

/-- Adjacent candidates with the correct residue class have this exact spacing. -/
theorem spacing (n b s : ℤ) :
    value n b (s+4) - value n b s = 8*(s-b-1)+16 := by unfold value; ring

theorem public_spacing {n b s : ℤ} (side : 2*b+2≤s) :
    8*b+24 ≤ value n b (s+4)-value n b s := by rw [spacing]; omega

/-- Taking the square root four below the completed-square reading moves
the rounding threshold to the arithmetic mean of adjacent candidate values.
A tie selects the larger sum. -/
def rounded (n b v : ℤ) : ℤ :=
  let top := b+3+Int.sqrt (v+2*n-2*b-5)
  top-(top-(n+1))%4

private theorem sqrt_window {l u y : ℤ} (lp : 0≤l) (up : 0≤u)
    (lo : l^2≤y) (hi : y<u^2) : l≤Int.sqrt y ∧ Int.sqrt y<u := by
  have yp : 0≤y := (sq_nonneg l).trans lo
  lift l to ℕ using lp
  lift u to ℕ using up
  lift y to ℕ using yp
  rw [Int.sqrt_natCast]
  exact ⟨by exact_mod_cast Nat.le_sqrt'.mpr (show l^2≤y by exact_mod_cast lo),
    by exact_mod_cast Nat.sqrt_lt'.mpr (show y<u^2 by exact_mod_cast hi)⟩

/-- A half-open rounding cell for a positive root at least two. Its
lower edge is included, while its upper edge belongs to the next sum. -/
theorem round_with_error {n b s v : ℤ} (side : 2≤s-b-1) (residue : s%4=(n+1)%4)
    (lo : -(4*(s-b-1)-8) ≤ v-value n b s)
    (hi : v-value n b s < 4*(s-b-1)+8) : rounded n b v=s := by
  let x := s-b-1
  let y := v+2*n-2*b-5
  have identity : y = x^2+(v-value n b s)-4 := by unfold y x value; ring
  have lower : (x-2)^2≤y := by rw [identity]; dsimp only [x]; nlinarith only [lo]
  have upper : y<(x+2)^2 := by rw [identity]; dsimp only [x]; nlinarith only [hi]
  have cut := sqrt_window (show 0≤x-2 by omega) (show 0≤x+2 by omega) lower upper
  change b+3+Int.sqrt y-(b+3+Int.sqrt y-(n+1))%4=s
  dsimp only [x] at cut
  omega

private theorem sqrt_bounds {y : ℤ} (yp : 0≤y) :
    (Int.sqrt y)^2≤y ∧ y<(Int.sqrt y+1)^2 := by
  lift y to ℕ using yp
  rw [Int.sqrt_natCast]
  exact ⟨by exact_mod_cast Nat.sqrt_le' y,by exact_mod_cast Nat.lt_succ_sqrt' y⟩

/-- For roots at least three, the stated lower and upper errors are also
necessary. The correction by four places both ties exactly. -/
theorem round_iff {n b s v : ℤ} (side : 3≤s-b-1) (residue : s%4=(n+1)%4) :
    rounded n b v=s ↔
      -(4*(s-b-1)-8) ≤ v-value n b s ∧ v-value n b s < 4*(s-b-1)+8 := by
  refine ⟨?_,fun h => round_with_error (by omega) residue h.1 h.2⟩
  let x := s-b-1
  let y := v+2*n-2*b-5
  intro got
  change b+3+Int.sqrt y-(b+3+Int.sqrt y-(n+1))%4=s at got
  have low : x-2 ≤ Int.sqrt y := by dsimp only [x]; omega
  have high : Int.sqrt y+1 ≤ x+2 := by dsimp only [x]; omega
  have yp : 0≤y := by
    by_contra! neg
    have zero : Int.sqrt y=0 := by simp [Int.sqrt,Int.toNat_of_nonpos neg.le]
    dsimp only [x] at low
    omega
  have range := sqrt_bounds yp
  have left := ((sq_le_sq₀ (show 0≤x-2 by dsimp only [x]; omega) (Int.sqrt_nonneg y)).mpr low).trans range.1
  have right := range.2.trans_le ((sq_le_sq₀ (by have := Int.sqrt_nonneg y; omega)
    (show 0≤x+2 by dsimp only [x]; omega)).mpr high)
  have identity : y = x^2+(v-value n b s)-4 := by unfold y x value; ring
  rw [identity] at left right
  change -(4*x-8) ≤ v-value n b s ∧ v-value n b s < 4*x+8
  constructor <;> nlinarith only [left,right]

/-- Balanced, distinct odd factors allow absolute error through four times
the public interval length. The exact sum can then be used in the quadratic
discriminant. -/
theorem recover_balanced {p q : ℕ} (pos : 0<p) (ord : p<q) (balanced : q<2*p)
    (odd : (p*q)%2=1) (v : ℤ)
    (error : |v-value (p*q) (cutoff (p*q)) (p+q)| ≤ 4*(cutoff (p*q):ℤ)) :
    rounded (p*q) (cutoff (p*q)) v=p+q := by
  have below := (cutoff_bounds pos balanced).1
  have side : (cutoff (p*q):ℤ)+2 ≤ (p:ℤ)+q-cutoff (p*q)-1 := by omega
  have c := SumIntervalExclusion.sum_congruence odd
  have residue : ((p:ℤ)+q)%4=(((p:ℤ)*q)+1)%4 := by exact_mod_cast c
  have both := abs_le.mp error
  apply round_with_error (by omega) residue
  · omega
  · omega

/-- The error budget refers to the genuine finite-character aggregate. Only
the approximate integer v is an input to the rounding procedure. -/
theorem recover_from_reading {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ord : p<q)
    (balanced : q<2*p) (odd : (p*q)%2=1) {exactValue v : ℤ}
    (exactReading : aggregate p q (cutoff (p*q))=(exactValue:ℂ))
    (error : |v-exactValue| ≤ 4*(cutoff (p*q):ℤ)) :
    rounded (p*q) (cutoff (p*q)) v=p+q := by
  have eq : value (p*q) (cutoff (p*q)) (p+q)=exactValue := by
    exact_mod_cast (aggregate_value ord balanced).symm.trans exactReading
  exact recover_balanced (Fact.out : p.Prime).pos ord balanced odd v (eq ▸ error)

set_option exponentiation.threshold 4096 in
/-- At the 2048-bit lower endpoint even an absolute integer error of 2^1025
is within the public tolerance. -/
theorem full_width {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ord : p<q) (balanced : q<2*p)
    (odd : (p*q)%2=1) (bits : 2^2047 ≤ p*q) {exactValue v : ℤ}
    (exactReading : aggregate p q (cutoff (p*q))=(exactValue:ℂ)) (error : |v-exactValue| ≤ 2^1025) :
    rounded (p*q) (cutoff (p*q)) v=p+q := by
  have base : (2^1023 : ℕ)^2*2=2^2047 := by decide +kernel
  have root : 2^1023≤cutoff (p*q) :=
    Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le (by decide : 0<2)).mpr (base ▸ bits))
  apply recover_from_reading ord balanced odd exactReading (error.trans ?_)
  have h := Nat.mul_le_mul_left 4 root
  rw [show (4:ℕ)*2^1023=2^1025 by decide +kernel] at h
  exact_mod_cast h

/-- At 143 the exact value is −44. Both edges check the specified tie rule. -/
theorem control143 :
    cutoff 143=8 ∧ value 143 8 24= -44 ∧
    rounded 143 8 (-97)=20 ∧ rounded 143 8 (-96)=24 ∧
    rounded 143 8 23=24 ∧ rounded 143 8 24=28 := by decide +kernel

end PrimeFactors.PrimitiveIntervalPrecision
