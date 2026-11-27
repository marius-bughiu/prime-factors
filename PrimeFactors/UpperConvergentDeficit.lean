import PrimeFactors.PowerRatioRemainder
import Mathlib.Tactic

/-! Public dyadic tests on the ordinary Euclidean convergents of E/N. -/
namespace PrimeFactors.UpperConvergentDeficit

structure Row where
  a : ℕ
  b : ℕ
deriving DecidableEq, Repr

/-- One ordinary convergent update. -/
def step (x y : Row) (q : ℕ) : Row := ⟨x.a+q*y.a,x.b+q*y.b⟩

/-- The rational deficit (N*a-E*b)/a lies in [L,2L), for a positive
numerator. Cross multiplication is exact; no integer truncation occurs. -/
def score (N E L : ℕ) (z : Row) : ℕ :=
  if 0<z.a ∧ L*z.a≤N*z.a-E*z.b ∧ N*z.a-E*z.b<2*(L*z.a) then 1 else 0

/-- Number of passing ordinary convergents in the first fuel Euclidean
quotients. A zero denominator ends the walk immediately. -/
def visits (N E L : ℕ) : ℕ → ℕ → ℕ → Row → Row → ℕ
  | 0,_,_,_,_ => 0
  | k+1,u,v,x,y => if v=0 then 0 else
      let z := step x y (u/v)
      score N E L z + visits N E L k v (u%v) y z

theorem last (N E L k u : ℕ) (x y : Row) : visits N E L k u 0 x y=0 := by
  cases k <;> simp [visits]

theorem lower_score {N E L u : ℕ} (lp : 0<L) {x : Row}
    (low : E*x.b=N*x.a+u) : score N E L x=0 := by
  unfold score
  rw [Nat.sub_eq_zero_of_le (by omega : N*x.a≤E*x.b)]
  split_ifs with h
  · have := Nat.mul_pos lp h.1
    omega
  · rfl

private theorem upper_score {N E L v : ℕ} {y : Row} (yp : 0<y.a)
    (high : N*y.a=E*y.b+v) :
    score N E L y = if L*y.a≤v ∧ v<2*(L*y.a) then 1 else 0 := by
  simp only [score,yp,true_and,high,Nat.add_sub_cancel_left]

theorem next_lower {N E u v : ℕ} {x y : Row}
    (low : E*x.b=N*x.a+u) (high : N*y.a=E*y.b+v) :
    E*(step x y (u/v)).b=N*(step x y (u/v)).a+u%v := by
  dsimp [step]
  nlinarith only [low,congrArg (fun z : ℕ => (u/v)*z) high,Nat.mod_add_div u v]

theorem next_upper {N E u v : ℕ} {x y : Row}
    (high : N*x.a=E*x.b+u) (low : E*y.b=N*y.a+v) :
    N*(step x y (u/v)).a=E*(step x y (u/v)).b+u%v := by
  dsimp [step]
  nlinarith only [high,congrArg (fun z : ℕ => (u/v)*z) low,Nat.mod_add_div u v]

/-- Between two ordinary upper rows there is an ordinary lower row.
Once both Euclidean quotients are positive, the numerator at least doubles. -/
theorem numerator_double (x y : Row) {q s : ℕ} (qpos : 0<q) (spos : 0<s) :
    2*y.a≤(step y (step x y q) s).a := by
  have l : y.a≤(step x y q).a := by
    dsimp [step]
    have := Nat.le_mul_of_pos_left y.a qpos
    omega
  have r := Nat.le_mul_of_pos_left (step x y q).a spos
  change _ ≤ y.a+s*(step x y q).a
  omega

private theorem combine {v w a b L tail : ℕ} (order : 2*a≤b) (down : w<v)
    (later : tail ≤ if L*b≤w then 1 else 0) :
    (if L*a≤v ∧ v<2*(L*a) then 1 else 0) + tail ≤ if L*a≤v then 1 else 0 := by
  have width : 2*(L*a)≤L*b := by
    simpa only [Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_left L order
  by_cases h : L*b≤w <;> simp only [h,if_true,if_false] at later <;> split_ifs <;> omega

private theorem bounded {N E L : ℕ} (lp : 0<L) (fuel : ℕ) {u v : ℕ} {x y : Row}
    (low : E*x.b=N*x.a+u) (high : N*y.a=E*y.b+v) (vu : v≤u) (yp : 0<y.a) :
    score N E L y + visits N E L fuel u v x y ≤ if L*y.a≤v then 1 else 0 := by
  induction fuel using Nat.strong_induction_on generalizing u v x y with
  | h fuel ih =>
    by_cases vz : v=0
    · subst v
      rw [last, upper_score yp high]
      split_ifs <;> omega
    have vp : 0<v := Nat.pos_of_ne_zero vz
    let w := u%v
    let z := step x y (u/v)
    have low' : E*z.b=N*z.a+w := next_lower low high
    cases fuel with
    | zero =>
      rw [visits,upper_score yp high]
      split_ifs <;> omega
    | succ k =>
      simp only [visits,if_neg vz,lower_score lp low',Nat.zero_add]
      change score N E L y + (score N E L z + visits N E L k v w y z) ≤ _
      rw [lower_score lp low',Nat.zero_add]
      by_cases wz : w=0
      · rw [wz,last,upper_score yp high]
        split_ifs <;> omega
      have wp : 0<w := Nat.pos_of_ne_zero wz
      have wv : w<v := Nat.mod_lt _ vp
      cases k with
      | zero =>
        rw [visits,upper_score yp high]
        split_ifs <;> omega
      | succ m =>
        let z' := step y z (v/w)
        have high' : N*z'.a=E*z'.b+v%w := next_upper high low'
        have double : 2*y.a≤z'.a := numerator_double x y (Nat.div_pos vu vp)
          (Nat.div_pos wv.le wp)
        have down : v%w<w := Nat.mod_lt _ wp
        have later := ih m (by omega) low' high' down.le (by omega : 0<z'.a)
        rw [upper_score yp high]
        change _ + (if w=0 then 0 else score N E L z' + visits N E L m w (v%w) z z') ≤ _
        rw [if_neg wz]
        exact combine double (down.trans wv) later

/-- Once a strict upper row falls below the lower endpoint, all later rows
miss. This permits early termination before divisibility or square tests. -/
theorem stop_below {N E L u v : ℕ} {x y : Row} (lp : 0<L) (fuel : ℕ)
    (low : E*x.b=N*x.a+u) (high : N*y.a=E*y.b+v) (vu : v≤u)
    (yp : 0<y.a) (below : v<L*y.a) : visits N E L fuel u v x y=0 := by
  have h := bounded lp fuel low high vu yp
  rw [if_neg (Nat.not_le.mpr below)] at h
  omega

/-- With the standard seeds (0,1),(1,0), arbitrarily many ordinary
Euclidean steps can produce at most one passing row. This includes E=0,
integer ratios, and the exact final convergent of a rational. -/
theorem at_most_one (N E : ℕ) {L : ℕ} (lp : 0<L) (fuel : ℕ) :
    visits N E L fuel E N ⟨0,1⟩ ⟨1,0⟩ ≤ 1 := by
  by_cases nz : N=0
  · subst N
    rw [last]
    decide
  have np := Nat.pos_of_ne_zero nz
  cases fuel with
  | zero => simp [visits]
  | succ k =>
    let z := step ⟨0,1⟩ ⟨1,0⟩ (E/N)
    have low : E*z.b=N*z.a+(E%N) := by
      dsimp [z,step]
      simpa [Nat.add_comm] using (Nat.mod_add_div E N).symm
    change (if N=0 then 0 else score N E L z + visits N E L k N (E%N) ⟨1,0⟩ z)≤1
    rw [if_neg nz,lower_score lp low,Nat.zero_add]
    by_cases rz : E%N=0
    · rw [rz,last]
      decide
    cases k with
    | zero => simp [visits]
    | succ m =>
      let z' := step ⟨1,0⟩ z (N/(E%N))
      have high : N*z'.a=E*z'.b+N%(E%N) := next_upper (by simp) low
      have pos : 0<z'.a := by dsimp [z',step]; omega
      have vr := Nat.mod_lt N (Nat.pos_of_ne_zero rz)
      have hb := bounded lp m low high vr.le pos
      change (if E%N=0 then 0 else score N E L z' + visits N E L m (E%N) (N%(E%N)) z z')≤1
      rw [if_neg rz]
      exact hb.trans (by split_ifs <;> decide)

/-- Distinct factors of the same bit width place their sum minus one in
one dyadic band, including factors at the inclusive lower endpoint. -/
theorem sum_band {p q B : ℕ} (lo : B≤p) (distinct : p<q) (hi : q<2*B) :
    2*B≤p+q-1 ∧ p+q-1<2*(2*B) := by omega

/-- A row matching the totient ratio passes precisely the band test used
above; no division of either numerator is needed. -/
theorem correct_row {N E F L : ℕ} {z : Row} (ap : 0<z.a)
    (row : E*z.b=z.a*F) (band : L≤N-F ∧ N-F<2*L) : score N E L z=1 := by
  have err : N*z.a-E*z.b=(N-F)*z.a := by rw [row,Nat.sub_mul,Nat.mul_comm F]
  have lo := Nat.mul_le_mul_right z.a band.1
  have hi := Nat.mul_lt_mul_of_pos_right band.2 ap
  simp only [score,ap,true_and,err]
  rw [if_pos ⟨lo,by simpa only [Nat.mul_assoc] using hi⟩]

/-- The strict drop of the positive deficit uses ordinary rational
division; this cross-multiplied form also covers a zero later remainder. -/
theorem strict_drop {a b v w : ℕ} (ap : 0<a) (double : 2*a≤b) (down : w<v) :
    2*w*a<v*b := calc
  2*w*a = w*(2*a) := by ring
  _ < v*(2*a) := Nat.mul_lt_mul_of_pos_right down (by positivity)
  _ ≤ v*b := Nat.mul_le_mul_left v double

end PrimeFactors.UpperConvergentDeficit
