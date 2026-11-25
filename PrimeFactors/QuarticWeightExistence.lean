import PrimeFactors.QuarticFactorLane
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Prime.Basic

namespace PrimeFactors.QuarticWeightExistence

open QuarticFactorLane

/-- Symmetric coefficient box for the quadratic, linear, and constant terms. -/
def bounded (w : Weights) (Q L C : ℕ) : Prop :=
  |w.d| ≤ Q ∧ |w.b| ≤ L ∧ |w.e| ≤ C ∧ |w.a| ≤ L ∧ |w.c| ≤ Q

private abbrev Box (Q L C : ℕ) :=
  Fin (Q+1) × Fin (L+1) × Fin (C+1) × Fin (L+1) × Fin (Q+1)

private def lift {Q L C : ℕ} (p : Box Q L C) : Weights :=
  { a := p.2.2.2.1, b := p.2.1, c := p.2.2.2.2, d := p.1, e := p.2.2.1 }

private def sub (v w : Weights) : Weights :=
  { a := v.a-w.a, b := v.b-w.b, c := v.c-w.c, d := v.d-w.d, e := v.e-w.e }

private def label (n : ℕ) (hn : 0<n) (v : ℤ) : Fin n :=
  ⟨(v%n).toNat, by have := Int.emod_lt_of_pos v (by exact_mod_cast hn : 0<(n:ℤ)); omega⟩

private theorem label_dvd {n : ℕ} {hn : 0<n} {v w : ℤ} (h : label n hn v=label n hn w) :
    (n:ℤ) ∣ v-w := by
  have eq := congrArg Fin.val h
  have positive : 0<(n:ℤ) := by exact_mod_cast hn
  have nv := Int.emod_nonneg v positive.ne'
  have nw := Int.emod_nonneg w positive.ne'
  have modEq : w ≡ v [ZMOD (n:ℤ)] := by
    change (v%n).toNat=(w%n).toNat at eq
    change w%n=v%n
    omega
  exact Int.modEq_iff_dvd.mp modEq

/-- More box tuples than possible Taylor labels force a nonzero signed
coefficient vector annihilating all four jets at the specified lane. -/
theorem exists_stationary (N u : ℤ) (Q L C R : ℕ) (positive : 0<R)
    (large : R^10 < (Q+1)^2*(L+1)^2*(C+1)) :
    ∃ w : Weights, (w.a≠0 ∨ w.b≠0 ∨ w.c≠0 ∨ w.d≠0 ∨ w.e≠0) ∧
      bounded w Q L C ∧ conditions w N R u := by
  let code (p : Box Q L C) :=
    let w := lift p
    (label (R^4) (by positivity) (value w N u),
     label (R^3) (by positivity) (w.b*N+2*w.e*u+3*w.a*u^2+4*w.c*u^3),
     label (R^2) (by positivity) (w.e+3*w.a*u+6*w.c*u^2),
     label R positive (w.a+4*w.c*u))
  have size : Fintype.card (Fin (R^4) × Fin (R^3) × Fin (R^2) × Fin R) <
      Fintype.card (Box Q L C) := by
    simp only [Box, Fintype.card_prod, Fintype.card_fin]
    convert large using 1 <;> ring
  obtain ⟨p,q,ne,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt code size
  have bounds {k : ℕ} (v w : Fin (k+1)) : |(v:ℤ)-w| ≤ k := abs_le.mpr (by
    have := v.isLt; have := w.isLt; omega)
  refine ⟨sub (lift p) (lift q), ?_, ?_, ?_⟩
  · by_contra! zero
    obtain ⟨p0,p1,p2,p3,p4⟩ := p
    obtain ⟨q0,q1,q2,q3,q4⟩ := q
    simp only [sub,lift] at zero
    apply ne
    simp only [Prod.mk.injEq]
    exact ⟨Fin.ext (by omega), Fin.ext (by omega), Fin.ext (by omega),
      Fin.ext (by omega), Fin.ext (by omega)⟩
  · exact ⟨bounds _ _,bounds _ _,bounds _ _,bounds _ _,bounds _ _⟩
  · have h0 := label_dvd (hn:=by positivity) (congrArg Prod.fst eq)
    have h1 := label_dvd (hn:=by positivity) (congrArg (fun z => z.2.1) eq)
    have h2 := label_dvd (hn:=by positivity) (congrArg (fun z => z.2.2.1) eq)
    have h3 := label_dvd (hn:=by positivity) (congrArg (fun z => z.2.2.2) eq)
    simp only [Nat.cast_pow] at h0 h1 h2
    refine ⟨?_,?_,?_,?_⟩
    · convert h0 using 1
      unfold value sub
      ring
    · convert h1 using 1
      unfold sub
      ring
    · convert h2 using 1
      unfold sub
      ring
    · convert h3 using 1
      unfold sub
      ring

/-- The sufficient coordinate bounds hold even for negative weights and
both signs of the factors. -/
theorem trace_bound {w : Weights} {x y : ℤ} {Q L C X : ℕ}
    (hw : bounded w Q L C) (hx : |x|≤X) (hy : |y|≤X) :
    |trace w x y| ≤ (2*Q*X^2+2*L*X+C : ℕ) := by
  obtain ⟨hd,hb,he,ha,hc⟩ := hw
  have two (v k : ℤ) (vm : |v|≤Q) (km : |k|≤X) : |v*k^2| ≤ (Q:ℤ)*X^2 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul vm (by simpa only [sq] using mul_self_le_mul_self (abs_nonneg _) km)
      (sq_nonneg _) (Int.natCast_nonneg _)
  have one (v k : ℤ) (vm : |v|≤L) (km : |k|≤X) : |v*k| ≤ (L:ℤ)*X := by
    rw [abs_mul]; exact mul_le_mul vm km (abs_nonneg _) (Int.natCast_nonneg _)
  have ax := one _ _ ha hx
  have by' := one _ _ hb hy
  have cx := two _ _ hc hx
  have dy := two _ _ hd hy
  unfold trace
  calc
    _ ≤ |w.d*y^2+w.b*y+w.e+w.a*x|+|w.c*x^2| := abs_add_le ..
    _ ≤ _ := by
      push_cast
      linarith [abs_add_le (w.d*y^2+w.b*y+w.e) (w.a*x),
        abs_add_le (w.d*y^2+w.b*y) w.e, abs_add_le (w.d*y^2) (w.b*y)]

/-- A single scalar inequality supplies bounded box sizes automatically.
Thus a radix just above √5·X^(3/5) suffices independently of the lane. -/
theorem box_of_scale (X R : ℕ) (xp : 0<X) (rp : 0<R) (scale : 5^5*X^6 < R^10) :
    let P := R^4-1
    let Q := P/(5*X^2)
    let L := P/(5*X)
    let C := P/5
    R^10 < (Q+1)^2*(L+1)^2*(C+1) ∧ 2*Q*X^2+2*L*X+C < R^4 := by
  let P := R^4-1
  let Q := P/(5*X^2)
  let L := P/(5*X)
  let C := P/5
  have p : P+1=R^4 := Nat.sub_add_cancel (Nat.succ_le_of_lt (pow_pos rp 4))
  have low (d : ℕ) (hd : 0<d) : R^4 ≤ d*(P/d+1) := by
    have := Nat.lt_mul_div_succ P hd
    omega
  have q := low (5*X^2) (by positivity)
  have l := low (5*X) (by positivity)
  have c := low 5 (by decide)
  change R^4 ≤ 5*X^2*(Q+1) at q
  change R^4 ≤ 5*X*(L+1) at l
  change R^4 ≤ 5*(C+1) at c
  constructor
  · have growth : R^10 * (5^5*X^6) < ((Q+1)^2*(L+1)^2*(C+1)) * (5^5*X^6) := calc
      _ < R^10*R^10 := Nat.mul_lt_mul_of_pos_left scale (by positivity)
      _ = (R^4)^2*(R^4)^2*R^4 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left q 2) (Nat.pow_le_pow_left l 2)) c
      _ = _ := by ring
    exact Nat.lt_of_mul_lt_mul_right growth
  · have hq : 5*X^2*Q ≤ P := Nat.mul_div_le _ _
    have hl : 5*X*L ≤ P := Nat.mul_div_le _ _
    have hc : 5*C ≤ P := Nat.mul_div_le _ _
    change 2*Q*X^2+2*L*X+C < R^4
    nlinarith only [hq,hl,hc,p]

set_option exponentiation.threshold 8192 in
/-- For balanced factors of any 2048-bit product X²≤2N<2^2049.
A uniform 616-bit exponent of two for the radix works on every lane. -/
theorem parameters_2048 {X : ℕ} (size : X^2≤2^2049) :
    (2^616)^10 < (2^413+1)^2*(2^1437+1)^2*(2^2461+1) ∧
    2*2^413*X^2+2*2^1437*X+2^2461 < (2^616)^4 := by
  constructor
  · decide +kernel
  · have linear : 2*X < 3*2^1024 := by
      by_contra! bad
      have sq := Nat.mul_self_le_mul_self bad
      nlinarith only [sq,size,
        (by decide +kernel : 4*(2:ℕ)^2049 < (3*2^1024)*(3*2^1024))]
    have quad := Nat.mul_le_mul_left (2*2^413) size
    have lin := Nat.mul_lt_mul_of_pos_left linear (by decide +kernel : 0<(2:ℕ)^1437)
    nlinarith only [lin,quad,
      (by decide +kernel : 2*2^413*2^2049 + 2^1437*(3*2^1024) + (2:ℕ)^2461 = (2^616)^4)]

set_option exponentiation.threshold 8192 in
/-- Every residue lane has a nonzero quartic vanishing on all positive
balanced factor pairs in that lane. Only the public product and lane are
used to choose the weights; no bits of the true smaller factor are supplied. -/
theorem every_2048_lane (N : ℕ) (odd : Odd N) (size : N<2^2048) (u : ℤ) :
    ∃ w : Weights, (w.a≠0 ∨ w.b≠0 ∨ w.c≠0 ∨ w.d≠0 ∨ w.e≠0) ∧
      conditions w N (2^616) u ∧ ∃ S : Finset ℤ,
      S=candidates w N ∧ S.card≤4 ∧
      ∀ x y : ℕ, x*y=N → x≤2*y → y≤2*x → (x:ℤ) ≡ u [ZMOD (2:ℤ)^616] → (x:ℤ) ∈ S := by
  let X := (2*N).sqrt
  have xs : X^2 ≤ 2*N := Nat.le_sqrt'.mp le_rfl
  have bound : X^2 ≤ 2^2049 := by linarith [show (2:ℕ)^2049=2*2^2048 by decide +kernel]
  obtain ⟨space,small⟩ := parameters_2048 bound
  obtain ⟨w,non,hw,active⟩ := exists_stationary N u (2^413) (2^1437) (2^2461) (2^616)
    (by decide +kernel) space
  have divs : conditions w N (2^616) u := by exact_mod_cast active
  refine ⟨w,non,divs,candidates w N,rfl,candidates_card _ _,?_⟩
  intro x y mul xy yx lane
  have cop : IsCoprime ((2:ℤ)^616) N := by
    exact_mod_cast ((Nat.coprime_two_left.mpr odd).pow_left 616).isCoprime
  have pos : (N:ℤ)≠0 := by obtain ⟨k,hk⟩ := odd; omega
  have hx : x ≤ X := Nat.le_sqrt'.mpr (by nlinarith [Nat.mul_le_mul_left x xy])
  have hy : y ≤ X := Nat.le_sqrt'.mpr (by nlinarith [Nat.mul_le_mul_left y yx])
  have boundX : |(x:ℤ)|≤X := by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using
    (by exact_mod_cast hx : (x:ℤ)≤X)
  have boundY : |(y:ℤ)|≤X := by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using
    (by exact_mod_cast hy : (y:ℤ)≤X)
  exact mem_candidates pos non cop divs lane (by exact_mod_cast mul)
    ((trace_bound hw boundX boundY).trans_lt (by exact_mod_cast small))

end PrimeFactors.QuarticWeightExistence
