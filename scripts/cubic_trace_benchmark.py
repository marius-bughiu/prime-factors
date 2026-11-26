"""Replay bounded cubic dependencies and certify a successful integral trace and gcd."""

from math import isqrt
from time import perf_counter

from experiments.cubic_trace_search import search
from scripts.factor import verify_file


THEOREM = 'PrimeFactors.Generated.CubicTrace.traceRecovery'


def _tuple(values):
    return '(' + ', '.join(str(int(value)) for value in values) + ')'


def trace_source(n, work, hit):
    """Emit the actual dependency, a square in the cubic algebra, and both gcds."""
    probe = next(probe for probe in hit['probes'] if any(1 < g < n for g in probe['gcds']))
    root = next(root for root in hit['field_roots'] if root['trace'] == probe['trace'])
    rows = ', '.join(map(_tuple, hit['rows']))
    c0, c1, c2, leading = map(int, work['f_ascending_monic'])
    if leading != 1:
        raise ValueError('expected a monic cubic')
    a, b, c = map(int, hit['abc'])
    prime = int(work['irreducibility_prime'])
    left, right = map(int, probe['modular_values'])
    g1, g2 = map(int, probe['gcds'])
    divisor = next(g for g in (g1, g2) if 1 < g < n)
    return f'''import PrimeFactors.CubicTraceSquare

namespace PrimeFactors.Generated.CubicTrace

abbrev Triple := ℤ × ℤ × ℤ

def n : ℕ := {n}
def m : ℤ := {int(work['m'])}
def polynomial (x : ℤ) : ℤ := ((x + ({c2}))*x + ({c1}))*x + ({c0})
def rows : List (ℤ × ℤ) := [{rows}]
def beta : Triple := {_tuple(hit['beta'])}
def signatures : Triple := {_tuple((a, b, c))}
def u : ℤ := {int(root['trace'])}
def v : ℤ := {int(root['second'])}
def w : ℤ := {isqrt(c)}
def z : ℤ := {int(hit['rational_root'])}
def numerator : Triple := {_tuple(root['numerators'])}
def denominator : ℤ := {int(root['denominator'])}

-- Multiplication in the basis 1, α, α², with polynomial(α) = 0.
def timesAlpha (x : Triple) : Triple :=
  (-({c0})*x.2.2, x.1 - ({c1})*x.2.2, x.2.1 - ({c2})*x.2.2)

def combine (x y z : Triple) (a b c : ℤ) : Triple :=
  (a*x.1+b*y.1+c*z.1, a*x.2.1+b*y.2.1+c*z.2.1, a*x.2.2+b*y.2.2+c*z.2.2)

def mul (x y : Triple) : Triple :=
  combine x (timesAlpha x) (timesAlpha (timesAlpha x)) y.1 y.2.1 y.2.2

def characteristic (x : Triple) : Triple :=
  let y := timesAlpha x
  let z := timesAlpha y
  (x.1+y.2.1+z.2.2,
    x.1*y.2.1+x.1*z.2.2+y.2.1*z.2.2-x.2.1*y.1-x.2.2*z.1-y.2.2*z.2.1,
    x.1*(y.2.1*z.2.2-y.2.2*z.2.1)-y.1*(x.2.1*z.2.2-x.2.2*z.2.1)+z.1*(x.2.1*y.2.2-x.2.2*y.2.1))

def squareNumerator : Triple :=
  combine (1,0,0) beta (mul beta beta) numerator.1 numerator.2.1 numerator.2.2

def value (x : ℤ) : ℤ := PrimeFactors.CubicTraceSquare.cubic u v w x

theorem traceRecovery :
    polynomial m = (n : ℤ) ∧ Nat.Prime {prime} ∧
    ((List.range {prime}).all (fun i => polynomial i % {prime} != 0)) = true ∧
    rows.foldl (fun acc row => mul acc (row.1, row.2, 0)) (1,0,0) = beta ∧
    (rows.map (fun row => row.1+m*row.2)).prod = z^2 ∧
    characteristic beta = signatures ∧ denominator > 0 ∧
    mul squareNumerator squareNumerator = mul beta (denominator^2,0,0) ∧
    signatures.2.2 = w^2 ∧ u^2-signatures.1 = 2*v ∧ v^2-signatures.2.1 = 2*u*w ∧
    PrimeFactors.CubicTraceSquare.quartic signatures.1 signatures.2.1 w u = 0 ∧
    (beta.1+m*beta.2.1+m^2*beta.2.2) % (n : ℤ) = z^2 % (n : ℤ) ∧
    value z % (n : ℤ) = {left} ∧ value (-z) % (n : ℤ) = {right} ∧
    Nat.gcd n {left} = {g1} ∧ Nat.gcd n {right} = {g2} ∧
    1 < ({divisor} : ℕ) ∧ {divisor} < n ∧ {divisor} ∣ n := by
  decide +kernel

end PrimeFactors.Generated.CubicTrace
#print axioms {THEOREM}
'''


def cubic_trace_case(case, proof, agree, certify_split):
    n = int(case['n'])
    options = {key: case[key] for key in ('a_limit', 'b_limit', 'trace_cap')}
    start = perf_counter()
    work = search(n, **options)
    elapsed = perf_counter() - start
    arms = work['arms']
    checks = {key: work[key] for key in ('status', 'candidate_rows', 'smooth_rows') if key in work}
    for key in ('kernel_dimension', 'tested', 'true_squares', 'proper_hits'):
        checks[key] = [arm[key] for arm in arms]
    agree(dict(id=case['id'], **case['checks']), checks, case['checks'])
    work['limits'] = options
    hit = next((arm['first_hit'] for arm in reversed(arms) if arm['first_hit']), None)
    factor = int(hit['divisors'][0]) if hit else None
    result = certify_split(case, proof, factor, elapsed, 'cubic_trace', work)
    if hit:
        relation = proof.with_name(f'{proof.stem}-relation.lean')
        relation.write_text(trace_source(n, work, hit))
        start = perf_counter()
        verify_file(relation, THEOREM)
        result['cubic_relation'] = dict(proof=f'proofs/{relation.name}', theorem=THEOREM,
                                        row_count=len(hit['rows']), verification_seconds=perf_counter()-start)
    return result
