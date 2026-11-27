"""Produce a kernel-checkable no-match receipt for the explicitly listed regular draws."""
from random import Random
from time import perf_counter

from experiments.twelve_residue_collision import keys
from scripts.factor import verify_file


def check_no_matches(n, draws, seed, factor_proof, first_odd_factor=None):
    """Certify the setup, fixed point and unordered pairs on these draws. A Euclid pivot is separate."""
    rng = Random(seed)
    xs = [rng.randrange(n) for _ in range(draws)]
    values = keys(xs, n)
    entries = ',\n'.join(f'  ({x},{v})' for x, v in zip(xs, values))
    extra_import = coefficient_definitions = extra = rewrite = ''
    if first_odd_factor is not None:
        if draws < 2 or draws % 2:
            raise ValueError('the degree directly below an even positive degree must be odd')
        coefficient = (-sum((2*v-1) % n for v in values)) % n
        extra_import = '\nimport Mathlib.Algebra.Polynomial.BigOperators'
        coefficient_definitions = '''
private def roots : Multiset ℤ := ↑(points.map (fun s => (((2*s.2+n-1)%n : ℕ) : ℤ)))
private noncomputable def split : Polynomial ℤ := (roots.map (fun a => Polynomial.X - Polynomial.C a)).prod
private theorem pivot : split.coeff (roots.card-1) = -roots.sum :=
  Polynomial.multiset_prod_X_sub_C_coeff_card_pred roots (by decide +kernel)
'''
        extra = (f' ∧ split.coeff (roots.card-1) % (n:ℤ)={coefficient}'
                 f' ∧ Nat.gcd n {coefficient}={first_odd_factor}')
        rewrite = '\n  rw [pivot]'
    path = factor_proof.with_name(factor_proof.stem+'-no-matches.lean')
    path.write_text(f"""import PrimeFactors.ComplementaryKeys
import Mathlib.Data.Nat.Dist{extra_import}

namespace PrimeFactors.Generated.NoComplementaryMatch
open TwelveResidueCollision
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
private def n : ℕ := {n}
private def points : List (ℕ × ℕ) := [
{entries}]
private def valid (s : ℕ × ℕ) : Bool :=
  decide (s.1<n ∧ s.2<n ∧ (((s.2:ℤ)*den (s.1:ℤ)-num (s.1:ℤ)) % (n:ℤ)=0))
private def masks : ℕ := points.foldl
  (fun a s => (a*(mask (s.1:ℤ)).natAbs)%n) 1
private def middles : ℕ := points.foldl (fun a s => (a*Nat.dist (2*s.2) 1)%n) 1
private def labels : List ℕ := points.map (fun s => (s.2*(n+1-s.2))%n)
private def differences : List ℕ → ℕ
  | [] => 1
  | x::xs => (xs.foldl (fun a y => (a*Nat.dist x y)%n) 1 * differences xs)%n
{coefficient_definitions}

theorem checked : points.length={draws} ∧ points.all valid=true ∧
    Nat.gcd n masks=1 ∧ Nat.gcd n middles=1 ∧ Nat.gcd n (differences labels)=1{extra} := by{rewrite}
  decide +kernel
#print axioms checked
end PrimeFactors.Generated.NoComplementaryMatch
""")
    start = perf_counter()
    verify_file(path, 'PrimeFactors.Generated.NoComplementaryMatch.checked')
    receipt = dict(proof=f'proofs/{path.name}', seconds=perf_counter()-start,
                   draws=draws, pairs=draws*(draws-1)//2)
    if first_odd_factor is not None:
        receipt.update(first_odd_coefficient=str(coefficient), coefficient_gcd=str(first_odd_factor))
    return receipt
