"""Benchmark public cubic row, diagonal, and midpoint tests with independent certificates."""
from math import isqrt
from pathlib import Path
from time import perf_counter

from experiments.cubic_forced_units import diagonal, universal, varied
from experiments.cubic_gap_window import search as midpoint_search
from experiments.offset_tangent_cover import cube_root
from scripts.factor import render_certificate, verify_file

CONTROLS = Path(__file__).resolve().parents[1]/'benchmarks/controls'
THEOREM = 'PrimeFactors.Generated.cubicForcedRun'


def proper_readout(n, readouts, elementary):
    """Name the first proper observed gcd, including the cheaper derivative check."""
    for label, pairs in (('derivative', [[readouts['derivative_gcd']]]),
                         ('elementary', elementary), ('ordinary', readouts['ordinary_gcds']),
                         ('direct', readouts['direct_gcds']), ('projected', readouts['projected_gcds'])):
        for pair in pairs:
            for divisor in pair:
                if 1 < divisor < n:
                    if n % divisor:
                        raise ArithmeticError('reported cubic gcd does not divide the input')
                    return divisor, label
    return None, None


def public_run(n, mode):
    if mode == 'universal':
        work = universal(n)
        factor, channel = proper_readout(n, work, work['elementary_gcds'])
        work['first_proper_gcd_source'] = channel
        checks = {'traces': len(work['complementary_traces']), 'signed_tests': work['work']['signed_divisor_tests'],
                  'proper_gcd_source': channel}
    elif mode == 'varied':
        work = varied(n)
        winning = []
        for hit in work['trace_hits']:
            divisor, channel = proper_readout(n, hit['readouts'], [hit['gcds']])
            if divisor is not None:
                winning.append((divisor, channel))
        factor, channel = winning[0] if winning else (None, None)
        work['first_proper_gcd_source'] = channel
        checks = {'parameter_pairs': work['parameter_pairs'], 'traces': len(work['trace_hits']),
                  'signed_tests': work['work'].get('signed_divisor_tests', 0), 'proper_gcd_source': channel}
    elif mode in ('diagonal', 'midpoint'):
        work = diagonal(n) if mode == 'diagonal' else midpoint_search(n)
        pair = list(map(int, work['factors']))
        if pair and (len(pair) != 2 or min(pair) <= 1 or pair[0]*pair[1] != n):
            raise ValueError('public cubic search returned an invalid pair')
        factor = pair[0] if pair else None
        checks = {k: work[k] for k in ('integer_cube_roots', 'integer_square_roots')}
        checks['candidate_budget'] = 1
    else:
        raise ValueError(f'unknown cubic search mode {mode}')
    work['mode'] = mode
    return work, checks, factor


def witness_source(n, pair, mode, work, control=None):
    p,q = pair
    exact = f'PrimeFactors.ExactFactorization {n} [{p},{q}]'
    if control == 'diagonal':
        if mode != control:
            raise ValueError('diagonal certificate is incompatible with the search mode')
        source = (CONTROLS/'CubicForcedControl.lean').read_text()
        claim = f'PrimeFactors.CubicForcedParameters.decode {n}=some ({p},{q}) ∧ {exact}'
        proof = 'PrimeFactors.CubicForcedControl.control_checks'
    elif control == 'midpoint':
        if mode != control:
            raise ValueError('midpoint certificate is incompatible with the search mode')
        source = (CONTROLS/'CubicGapControl.lean').read_text()
        claim = f'PrimeFactors.CubicGapWindow.readout {n}=({p},{q}) ∧ {exact}'
        proof = '⟨PrimeFactors.Generated.gap_recovered, PrimeFactors.Generated.factorization⟩'
    elif control is not None:
        raise ValueError('unknown cubic control certificate')
    elif mode == 'diagonal':
        s = isqrt(cube_root(4*n-1)+1)//2
        source = 'import PrimeFactors.CubicForcedParameters\n' + render_certificate(n, [p,q])
        claim = f'PrimeFactors.CubicForcedParameters.decode {n}=some ({p},{q}) ∧ {exact}'
        proof = (f'by\n  refine ⟨?_,PrimeFactors.Generated.factorization⟩\n'
                 f'  have form : PrimeFactors.CubicForcedParameters.target {s}={n} := by decide +kernel\n'
                 f'  rw [←form,PrimeFactors.CubicForcedParameters.decode_target (by decide : 2≤{s})]\n'
                 '  decide +kernel')
    elif mode == 'midpoint':
        t = int(work['half_gap_estimate'])-1
        source = 'import PrimeFactors.CubicGapWindow\n' + render_certificate(n, [p,q])
        claim = f'PrimeFactors.CubicGapWindow.readout {n}=({p},{q}) ∧ {exact}'
        proof = (f'by\n  refine ⟨?_,PrimeFactors.Generated.factorization⟩\n'
                 f'  have cube : PrimeFactors.CubicForcedParameters.ceilCube (4*{n})={t} :=\n'
                 f'    PrimeFactors.CubicForcedParameters.ceilCube_eq (by decide +kernel) (by decide +kernel)\n'
                 '  unfold PrimeFactors.CubicGapWindow.readout PrimeFactors.CubicGapWindow.midpoint '
                 'PrimeFactors.CubicGapWindow.gapGuess\n  rw [cube]\n  decide +kernel')
    elif mode == 'universal':
        source = 'import PrimeFactors.CubicForcedUnits\n' + render_certificate(n, [p,q])
        w, h = (n+work['h'])//4, work['h']
        square = bool(work['ordinary_traces'])
        claim = (f'{exact} ∧ {"" if square else "¬"}IsSquare (PrimeFactors.CubicForcedUnits.beta ({w}) ({h})) ∧ '
                 f'Nat.gcd (4+5*{w}) {n}={work["derivative_gcd"]}')
        proof = (f'by\n  refine ⟨PrimeFactors.Generated.factorization, ?_, by decide +kernel⟩\n'
                 f'  change {"" if square else "¬"}IsSquare (PrimeFactors.CubicForcedUnits.beta '
                 f'(PrimeFactors.CubicForcedUnits.parameter {n}) (PrimeFactors.CubicForcedUnits.sign {n}))\n'
                 f'  rw [PrimeFactors.CubicForcedUnits.positive_inputs (n := {n}) (by decide) (by decide)]\n'
                 '  decide')
    else:
        source = 'import PrimeFactors.CubicForcedParameters\n' + render_certificate(n, [p,q])
        hit = next(h for h in work['trace_hits']
                   if proper_readout(n, h['readouts'], [h['gcds']])[0] in pair)
        r,t,h,w,u = [hit[k] for k in ('r','t','h','w','u')]
        z = isqrt(r*t)
        a = f'({z} : ℤ)*(({u})^2+({h})*({r}+{t}))'
        b = f'2*({h})*(({u})+{r}*{t})'
        g1,g2 = hit['gcds']
        claim = (f'{exact} ∧ PrimeFactors.CubicForcedParameters.equation {r} {t} ({h}) {w} ({u})=0 ∧ '
                 f'(({a})-({b})).natAbs.gcd {n}={g1} ∧ (({a})+({b})).natAbs.gcd {n}={g2}')
        proof = '⟨PrimeFactors.Generated.factorization, by decide +kernel⟩'
    return source + f'\n\ntheorem {THEOREM} : {claim} := {proof}\n#print axioms {THEOREM}\n'


def forced_case(case, proof, agree, certify_split):
    n, mode = int(case['n']), case['mode']
    start = perf_counter()
    work, checks, factor = public_run(n, mode)
    elapsed = perf_counter()-start
    agree(case['checks'] | {'id': case['id']}, checks, checks.keys())
    result = certify_split(case, proof, None, elapsed, 'cubic_forced', work)
    if factor is not None:
        pair = sorted((factor, n//factor))
        certificate_start = perf_counter()
        proof.write_text(witness_source(n, pair, mode, work, case.get('control_certificate')))
        verify_start = perf_counter()
        verify_file(proof, THEOREM)
        result.update(factors=list(map(str, pair)), remaining=[], status='complete', verified=True,
                      verification_seconds=perf_counter()-verify_start,
                      certificate_seconds=perf_counter()-certificate_start)
        if 'fermat_tests_to_displayed_pair' not in work:
            work['fermat_tests_to_displayed_pair'] = str(sum(pair)//2-isqrt(n-1))
        work['fermat_comparison_square_roots'] = 1
    elif mode == 'universal' and n > 91:
        exclusion = proof.with_name(f'{proof.stem}-nonsquare.lean')
        exclusion.write_text(f"""import PrimeFactors.CubicForcedUnits
open PrimeFactors.CubicForcedUnits in
theorem {THEOREM} :
    ¬IsSquare (beta (parameter {n} : ℚ) (sign {n} : ℚ)) :=
  (large_inputs (n := {n}) (by decide +kernel) (by decide +kernel)).2.2
#print axioms {THEOREM}
""")
        verify_start = perf_counter()
        verify_file(exclusion, THEOREM)
        result['forced_nonsquare'] = {'proof': f'proofs/{exclusion.name}',
                                      'verification_seconds': perf_counter()-verify_start}
    return result
