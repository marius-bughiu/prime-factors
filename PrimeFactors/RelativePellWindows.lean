import PrimeFactors.MaskedRelations
import PrimeFactors.Certificate
import Mathlib.Tactic.NormNum.Prime

namespace PrimeFactors.RelativePellWindows

/-- A continued-fraction complete numerator with its two adjacent complete denominators. -/
structure Form where
  q : ℤ
  p : ℤ
  previous : ℤ

def discriminant (f : Form) : ℤ := f.p^2 + f.q*f.previous

def value (f : Form) (u v : ℤ) : ℤ := f.q*u^2-2*f.p*u*v-f.previous*v^2

def advance (f : Form) (a : ℤ) : Form :=
  ⟨f.previous+2*a*f.p-a^2*f.q,a*f.q-f.p,f.q⟩

def back (f : Form) (a : ℤ) : Form :=
  ⟨f.previous,a*f.previous-f.p,f.q+2*a*f.p-a^2*f.previous⟩

theorem advance_discriminant (f : Form) (a : ℤ) :
    discriminant (advance f a) = discriminant f := by simp [discriminant,advance]; ring

/-- In the usual recurrence the new denominator is obtained by dividing
the radicand minus the new numerator squared by the old denominator. -/
theorem advance_denominator (f : Form) (a : ℤ) :
    f.q*(advance f a).q = discriminant f - (advance f a).p^2 := by
  simp [advance,discriminant]; ring

theorem undo (f : Form) (a : ℤ) : back (advance f a) a = f := by
  cases f
  dsimp [back,advance]
  congr 1 <;> ring

theorem previous_value (f : Form) (a u v : ℤ) :
    value (back f a) (a*u+v) u = -value f u v := by simp [value,back]; ring

/-- Starting at the last row, read the intervening partial quotients in
reverse chronological order. Only the local continuant and starting form survive. -/
def rewind : List ℤ → Form → ℤ → ℤ → Form × ℤ × ℤ
  | [], f, u, v => (f,u,v)
  | a::as, f, u, v => rewind as (back f a) (a*u+v) u

theorem rewind_value (as : List ℤ) (f : Form) (u v : ℤ) :
    let (g,s,t) := rewind as f u v
    value g s t = (-1)^as.length * value f u v := by
  induction as generalizing f u v with
  | nil => simp [rewind]
  | cons a as ih =>
    have h := ih (back f a) (a*u+v) u
    simpa [rewind,previous_value,pow_succ] using h

/-- A product of two signed row norms gives an exact small-coordinate difference
of squares, with the intervening continuant as the second coordinate. -/
theorem window_identity (as : List ℤ) (f : Form) :
    let (g,u,v) := rewind as f 1 0
    (g.q*u-g.p*v)^2-discriminant g*v^2 = (-1)^as.length*g.q*f.q := by
  have relation := rewind_value as f 1 0
  generalize h : rewind as f 1 0 = triple at relation ⊢
  rcases triple with ⟨g,u,v⟩
  dsimp at relation ⊢
  simp only [value,one_pow,mul_one,zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero] at relation
  dsimp [discriminant]
  linear_combination g.q * relation

/-- Changing the signed norm product by k*N still gives a modular square.
The exceptional shift m*v² recovers the starting square itself. -/
theorem shifted {N m w v r z k : ℤ} (pos : N≠0)
    (relative : w^2-m*N*v^2 = r) (test : z^2=r+k*N) :
    w^2-z^2=(m*v^2-k)*N ∧ (w^2=z^2 ↔ k=m*v^2) := by
  have d : w^2-z^2=(m*v^2-k)*N := by linear_combination relative-test
  refine ⟨d,?_⟩
  rw [← sub_eq_zero, d, mul_eq_zero]
  simp [pos,sub_eq_zero,eq_comm (a:=k)]

/-- One height bound on the determinant ensures that every distinct lifted
root gives a proper factor, independently of how deep into the walk it occurs. -/
theorem short_split {n D b w z v : ℕ} [NeZero n] (scale : D≤b^2)
    (window : w^2≤D*(v^2+4)) (root : z^2≤4*D) (height : b*(v+4)<n)
    (modular : (w : ZMod n)^2=(z : ZMod n)^2) (distinct : w≠z) :
    1 < (w+z).gcd n ∧ (w+z).gcd n < n := by
  have hw : w ≤ b*(v+2) := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (calc
    w^2 ≤ b^2*(v+2)^2 := window.trans (Nat.mul_le_mul scale (by nlinarith))
    _ = _ := by ring)
  have hz : z ≤ 2*b := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (calc
    z^2 ≤ 4*b^2 := root.trans (Nat.mul_le_mul_left _ scale)
    _ = _ := by ring)
  exact maskedRelations_short modular distinct ((Nat.add_le_add hw hz).trans_lt
    (by nlinarith only [height] : b*(v+2)+2*b<n))

/-- Full implication for the one-discriminant scan. Here r is the signed product
of the two denominators, each of which is less than twice the square root of n. -/
theorem lift_split {n b w z v : ℕ} [NeZero n] {r k : ℤ}
    (scale : n ≤ b^2) (small : r ≤ 4*(n : ℤ)) (root : z^2 ≤ 4*n)
    (height : b*(v+4) < n) (different : k ≠ (v : ℤ)^2)
    (relative : (w : ℤ)^2 - n*(v : ℤ)^2 = r) (lifted : (z : ℤ)^2 = r+k*n) :
    1 < (w+z).gcd n ∧ (w+z).gcd n < n := by
  have nonzero : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  obtain ⟨eqn, iff⟩ := shifted (m := 1) nonzero (by simpa using relative) lifted
  have windowZ : (w : ℤ)^2 ≤ n*((v : ℤ)^2+4) := by nlinarith only [relative,small]
  apply short_split scale (by exact_mod_cast windowZ) root height
  · have castEq := congrArg (fun a : ℤ => (a : ZMod n)) eqn
    push_cast at castEq
    exact sub_eq_zero.mp (by simpa using castEq)
  · rintro rfl
    exact different (by simpa using iff.mp rfl)

theorem rows_34387 :
    let (g,u,v) := rewind [3,1,1,1] ⟨38,175,99⟩ 1 0
    g.q=201 ∧ g.p=130 ∧ v=7 ∧ g.q*u-g.p*v=1301 := by decide +kernel

theorem witness_34387 :
    (1301:ℤ)^2-34387*7^2=7638 ∧ (205:ℤ)^2=7638+34387 ∧
    Nat.gcd (1301+205) 34387=251 ∧ ExactFactorization 34387 [137,251] := by
  norm_num [ExactFactorization]

end PrimeFactors.RelativePellWindows
