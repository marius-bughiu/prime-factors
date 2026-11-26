"""Replay bounded cubic dependencies and certify a successful integral trace and gcd."""

from math import isqrt
from time import perf_counter

from experiments.cubic_readout_panel import compare as compare_readouts
from experiments.cubic_smooth_bases import compare as compare_bases
from experiments.cubic_trace_search import search
from scripts.factor import verify_file


THEOREM = 'PrimeFactors.Generated.CubicTrace.traceRecovery'
PROJECTED = 'PrimeFactors.Generated.CubicReadout.projectedFactor'


def _tuple(values):
    return '(' + ', '.join(str(int(value)) for value in values) + ')'


def _arithmetic(c0, c1, c2):
    return f'''-- Multiplication in the basis 1, α, α², with polynomial(α) = 0.
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
    x.1*(y.2.1*z.2.2-y.2.2*z.2.1)-y.1*(x.2.1*z.2.2-x.2.2*z.2.1)+z.1*(x.2.1*y.2.2-x.2.2*y.2.1))'''


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

{_arithmetic(c0, c1, c2)}
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


def projection_source(n, comparison):
    hit = comparison['first_rescue']
    direct, = hit['direct']
    projected = hit['projected']
    u, = projected['signed_traces']
    (g1, g2), = projected['gcds']
    c0, c1, c2 = comparison['f']
    rows = ', '.join(map(_tuple, hit['rows']))
    return f'''import PrimeFactors.CubicTraceProjection

namespace PrimeFactors.Generated.CubicReadout
abbrev Triple := ℤ × ℤ × ℤ
def n : ℕ := {n}
def m : ℤ := {comparison['m']}
def z : ℤ := {int(hit['z'])}
def u : ℤ := {u}
def d : ℤ := {direct['denominator']}
def rootNumerator : Triple := {_tuple(direct['coefficients'])}
def rows : List (ℤ × ℤ) := [{rows}]
def beta : Triple := {_tuple(hit['beta'])}

{_arithmetic(c0, c1, c2)}

def eval (x : Triple) : ℤ := x.1+m*x.2.1+m^2*x.2.2
def derivative : ℤ := 3*m^2+2*({c2})*m+({c1})
def projector : Triple := (m^2+({c2})*m+({c1}),m+({c2}),1)
def charAt (e : Triple) (v : ℤ) : ℤ :=
  let (a,b,c) := characteristic e
  PrimeFactors.CubicTraceSquare.cubic a b c v

theorem projectedFactor :
    m^3+({c2})*m^2+({c1})*m+({c0})=(n : ℤ) ∧
    rows.foldl (fun acc ab => mul acc (ab.1, ab.2, 0)) (1,0,0) = beta ∧
    (rows.map (fun ab => ab.1+ab.2*m)).prod = z^2 ∧
    mul rootNumerator rootNumerator = mul (d^2,0,0) beta ∧
    d > 0 ∧ d.natAbs.Coprime n ∧
    (charAt rootNumerator (d*z)).natAbs.gcd n = n ∧
    (charAt rootNumerator (-d*z)).natAbs.gcd n = n ∧
    (characteristic (mul projector rootNumerator)).1^2 = (d*u)^2 ∧
    derivative.natAbs.Coprime n ∧
    (u-derivative*z).natAbs.gcd n = {g1} ∧ (u+derivative*z).natAbs.gcd n = {g2} ∧
    1 < ({g1} : ℕ) ∧ {g1} < n ∧ ({g1} : ℕ)*{g2} = n := by
  decide +kernel
end PrimeFactors.Generated.CubicReadout
#print axioms {PROJECTED}
'''


def cubic_readout_case(case, proof, agree, certify_split):
    n = int(case['n'])
    start = perf_counter()
    work = compare_readouts(n, cap=case['cap'])
    elapsed = perf_counter()-start
    hit = work.get('first_rescue')
    observed = {'tested': work.get('tested', 0), 'first_rescue': hit['index'] if hit else None}
    agree(case, observed, observed.keys())
    # This fixture specifically measures a split missed by the ordinary characteristic gcds.
    factor = int(hit['projected']['gcds'][0][0]) if hit else None
    result = certify_split(case, proof, factor, elapsed, 'cubic_readout', work)
    if hit:
        relation = proof.with_name(f'{proof.stem}-projection.lean')
        relation.write_text(projection_source(n, work))
        verify_file(relation, PROJECTED)
        result['projected_relation'] = f'proofs/{relation.name}'
    return result


def cubic_bases_case(case, proof, agree, certify_split):
    start = perf_counter()
    work = compare_bases(int(case['n']))
    elapsed = perf_counter()-start
    arm = work['two_three']['adaptive']
    measured = {'bases': arm['work']['bases_tried'], 'rows': arm['all_rows']['visited'],
                'rational_smooth': arm['all_rows']['rational_smooth'], 'joint': arm['all_rows']['joint']}
    agree(case, measured, measured.keys())
    return certify_split(case, proof, None, elapsed, 'cubic_smooth_bases', work)
