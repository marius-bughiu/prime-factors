import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeFactors.OffsetGridCount
open Finset

/-- Count the public slots having j divisible by L and k divisible by d. -/
noncomputable def grid (T h J L d : ℕ) : ℕ :=
  ∑ i ∈ range (J/L), (T*(L*(i+1))/h+1)/d

private theorem row_bracket {T h j d : ℕ} (hp : 0<h) (dp : 0<d) :
    let b := (T*j/h+1)/d
    T*j≤h*d*b+h*d ∧ h*d*b≤T*j+h*d := by
  let x := T*j/h
  let b := (x+1)/d
  have a : x*h≤T*j := Nat.div_mul_le_self ..
  have f : T*j<(x+1)*h := (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self x)
  have c : b*d≤x+1 := Nat.div_mul_le_self ..
  have g : x+1<(b+1)*d := (Nat.div_lt_iff_lt_mul dp).mp (Nat.lt_succ_self b)
  have hle := Nat.le_mul_of_pos_right h dp
  change T*j≤h*d*b+h*d ∧ h*d*b≤T*j+h*d
  constructor <;> nlinarith only [a,f,hle,Nat.mul_le_mul_right h c,Nat.mul_le_mul_right h g.le]

private theorem floor_triangle {J L : ℕ} (lp : 0<L) :
    let n := J/L
    L^2*n*(n+1)≤J^2+J*L ∧ J^2≤L^2*n*(n+1)+J*L := by
  let n := J/L
  have lo : n*L≤J := Nat.div_mul_le_self ..
  have hi : J<(n+1)*L := (Nat.div_lt_iff_lt_mul lp).mp (Nat.lt_succ_self n)
  change L^2*n*(n+1)≤J^2+J*L ∧ J^2≤L^2*n*(n+1)+J*L
  constructor
  · nlinarith only [Nat.pow_le_pow_left lo 2,Nat.mul_le_mul_right L lo]
  · have one := Nat.mul_le_mul_right J hi.le
    have two := Nat.mul_le_mul_right (n*L) hi.le
    nlinarith only [one,two]

private theorem cumulative {T h L d : ℕ} (hp : 0<h) (dp : 0<d) (n : ℕ) :
    let a := ∑ i ∈ range n, (T*(L*(i+1))/h+1)/d
    T*L*n*(n+1)≤2*h*d*a+2*h*d*n ∧
    2*h*d*a≤T*L*n*(n+1)+2*h*d*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sum_range_succ] at *
    have r := row_bracket (T:=T) (j:=L*(n+1)) hp dp
    obtain ⟨lower,upper⟩ := ih
    obtain ⟨a,b⟩ := r
    constructor <;> nlinarith only [lower,upper,a,b]

/-- Finite discrepancy for one divisibility grid. Dividing the error by
2hdL yields the bound TJ/(2hd) + J/L, uniform in the offset modulus L. -/
theorem grid_error {T h J L d : ℕ} (hp : 0<h) (lp : 0<L) (dp : 0<d) :
    let a := grid T h J L d
    let err := T*J*L+2*h*d*J
    T*J^2≤2*h*d*L*a+err ∧ 2*h*d*L*a≤T*J^2+err := by
  let n := J/L
  obtain ⟨small,large⟩ := floor_triangle (J:=J) lp
  obtain ⟨a,b⟩ := cumulative (T:=T) (L:=L) hp dp n
  have rem : n*L≤J := Nat.div_mul_le_self ..
  change T*J^2≤2*h*d*L*(∑ i ∈ range n, (T*(L*(i+1))/h+1)/d)+(T*J*L+2*h*d*J) ∧ _
  dsimp only [n,grid] at *
  constructor <;>
    nlinarith only [Nat.mul_le_mul_left T small,Nat.mul_le_mul_left T large,
      Nat.mul_le_mul_left L a,Nat.mul_le_mul_left L b,Nat.mul_le_mul_left (2*h*d) rem]

end PrimeFactors.OffsetGridCount
