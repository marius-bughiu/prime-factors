import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring

namespace PrimeFactors.ReverseSweep

/-- Cell indices refer to earlier values, with index zero naming the newest. -/
inductive Gate (R : Type*) (n : ℕ)
  | constant (value : R)
  | add (i j : Fin n)
  | mul (i j : Fin n)
  | neg (i : Fin n)

variable {R : Type*} [CommRing R] {m n : ℕ}

noncomputable def Gate.value (g : Gate R n) (x : Fin n → R) : R :=
  match g with
  | .constant c => c
  | .add i j => x i + x j
  | .mul i j => x i * x j
  | .neg i => -x i

/-- Coefficient of the first-order perturbation of this gate. -/
noncomputable def Gate.tangent (g : Gate R n) (x v : Fin n → R) : R :=
  match g with
  | .constant _ => 0
  | .add i j => v i + v j
  | .mul i j => x i * v j + v i * x j
  | .neg i => -v i

noncomputable def bump (a : Fin n → R) (i : Fin n) (c : R) (j : Fin n) : R :=
  a j + if j = i then c else 0

/-- Send one output weight to its operands. Two occurrences of the same
operand receive two contributions. Each gate updates at most two cells. -/
noncomputable def Gate.pull (g : Gate R n) (x : Fin n → R) (w : R) (a : Fin n → R) : Fin n → R :=
  match g with
  | .constant _ => a
  | .add i j => bump (bump a i w) j w
  | .mul i j => bump (bump a i (w * x j)) j (w * x i)
  | .neg i => bump a i (-w)

noncomputable def pairing (a v : Fin n → R) : R := ∑ j, a j * v j

private theorem pairing_bump (a v : Fin n → R) (i : Fin n) (c : R) :
    pairing (bump a i c) v = pairing a v + c * v i := by
  classical
  simp [pairing, bump, add_mul, Finset.sum_add_distrib, ite_mul]

theorem gate_pull_correct (g : Gate R n) (x v a : Fin n → R) (w : R) :
    pairing (g.pull x w a) v = w * g.tangent x v + pairing a v := by
  cases g <;> simp [Gate.pull, Gate.tangent, pairing_bump] <;> ring

/-- A division-free arithmetic circuit with shared intermediate values. -/
inductive Circuit (R : Type*) (m : ℕ) : ℕ → Type _
  | inputs : Circuit R m m
  | gate {n : ℕ} (previous : Circuit R m n) (op : Gate R n) : Circuit R m (n+1)

structure Trace (R : Type*) (m n : ℕ) where
  values : Fin n → R
  pullback : (Fin n → R) → (Fin m → R)

/-- Accumulate reverse updates using the forward values at each gate. -/
noncomputable def trace : {n : ℕ} → Circuit R m n → (Fin m → R) → Trace R m n
  | _, .inputs, x => ⟨x, id⟩
  | _, .gate t op, x =>
    let prev := trace t x
    ⟨Fin.cons (op.value prev.values) prev.values,
     fun a => prev.pullback (op.pull prev.values (a 0) (Fin.tail a))⟩

noncomputable def tangent : {n : ℕ} → Circuit R m n → (Fin m → R) → (Fin m → R) → Fin n → R
  | _, .inputs, _, v => v
  | _, .gate t op, x, v =>
    let d := tangent t x v
    Fin.cons (op.tangent (trace t x).values d) d

/-- The reverse sweep transposes every forward directional derivative.
Choosing one output coordinate and then each input direction gives all of
that output's partials from a single vector of reverse updates. -/
theorem pullback_correct (t : Circuit R m n) (x v : Fin m → R) (a : Fin n → R) :
    pairing ((trace t x).pullback a) v = pairing a (tangent t x v) := by
  induction t with
  | inputs => rfl
  | gate t op ih =>
    change pairing ((trace t x).pullback _) _ =
      pairing a (Fin.cons (op.tangent _ _) _)
    rw [ih, gate_pull_correct]
    symm
    unfold pairing
    rw [Fin.sum_univ_succ]
    simp [Fin.tail]

/-- Run the same circuit on polynomial inputs. Its control flow does not
depend on the numeric values of the inputs. -/
noncomputable def polynomialValues : {n : ℕ} → Circuit R m n → (Fin m → Polynomial R) → Fin n → Polynomial R
  | _, .inputs, z => z
  | _, .gate t op, z =>
    let prev := polynomialValues t z
    let next := match op with
      | .constant c => Polynomial.C c
      | .add i j => prev i + prev j
      | .mul i j => prev i * prev j
      | .neg i => -prev i
    Fin.cons next prev

/-- The forward tangent is the formal derivative of the represented polynomial,
even in finite characteristic. Polynomial identity is the relevant hypothesis. -/
theorem polynomial_trace (t : Circuit R m n) (z : Fin m → Polynomial R) (r : R) :
    let x := fun i => (z i).eval r
    let v := fun i => (z i).derivative.eval r
    (∀ i, (polynomialValues t z i).eval r = (trace t x).values i) ∧
    (∀ i, (polynomialValues t z i).derivative.eval r = tangent t x v i) := by
  induction t with
  | inputs => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | gate t op ih =>
    obtain ⟨values, derivs⟩ := ih
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => values j) i
      cases op <;> simp [polynomialValues, trace, Gate.value, values]
    · intro i
      refine Fin.cases ?_ (fun j => derivs j) i
      cases op <;> simp [polynomialValues, tangent, Gate.tangent, Polynomial.derivative_mul,
        values, derivs, add_comm]

/-- Seed one output in the reverse pass. The resulting vector paired with
the input velocities gives the derivative of this output polynomial. -/
theorem output_derivative (t : Circuit R m n) (z : Fin m → Polynomial R) (r : R) (o : Fin n) :
    pairing ((trace t (fun i => (z i).eval r)).pullback (bump (fun _ => 0) o 1))
      (fun i => (z i).derivative.eval r) = (polynomialValues t z o).derivative.eval r := by
  rw [pullback_correct, pairing_bump, ← (polynomial_trace t z r).2 o]
  simp [pairing]

end PrimeFactors.ReverseSweep
