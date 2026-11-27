"""Compare one target with three public targets guaranteed to include a modular square."""
import argparse
from hashlib import sha256
import json
from math import gcd, isqrt, prod
from pathlib import Path
from statistics import median
from time import process_time_ns

from experiments.affine_radix_holdout import draw_prime
from experiments.mixed_ratio_heights import jacobi
from experiments.pell_pairs import convergents
from experiments.target_norm_multipliers import primitive_mod16, target
from scripts.factor import primes_through, render_certificate, verify_file

ROOT = Path(__file__).resolve().parents[1]
METHODS = ('single', 'positive', 'signed_first', 'signed')
SEED = b'three-root-targets/v1'
MULTIPLIERS = 320
DEPTH = 256
BUDGET = 8192


def menu(n, method):
    if method == 'single':
        return [target(n)]
    if method not in METHODS:
        raise ValueError('unrecognized target rule')
    a, b, c = (2, 3, 5) if method == 'positive' else (-1, 2, 3)
    candidates = [a, b, a*b, c, a*c, b*c, a*b*c]
    allowed = [d for d in candidates if jacobi(d, n) == 1]
    return allowed[:1] if method == 'signed_first' else allowed[:3]


def attempt(n, method, *, budget=BUDGET, limit=MULTIPLIERS, depth=DEPTH):
    if n < 3 or isqrt(n)**2 == n or gcd(n, 2310) != 1:
        raise ValueError('expected a nonsquare product coprime to 2310')
    if min(budget, limit, depth) < 1:
        raise ValueError('search budgets must be positive')
    targets = menu(n, method)
    prime_list = primes_through(limit)
    gates = {d: (primitive_mod16(d), [p for p in (3, 5, 7, 11) if d % p == 0]) for d in targets}
    scale = isqrt(prod(targets)) if len(targets) == 3 else 1
    if len(targets) == 3 and scale**2 != prod(targets):
        raise ArithmeticError('the chosen masks do not form a line')

    roots = {}
    spent = dict(walks=0, steps=0, square_tests=0, matches=0, largest_multiplier=0)
    hit = None
    for k in range(1, limit+1):
        if spent['steps'] == budget:
            break
        spent['largest_multiplier'] = k
        common = gcd(n, k)
        if 1 < common < n:
            hit = dict(factor=str(common), kind='multiplier gcd', multiplier=k)
            break
        factors = [p for p in prime_list if k % p == 0]
        if common != 1 or prod(factors) != k:
            continue
        kn = k*n
        groups = {-1: [], 1: []}
        for d in targets:
            two_adic, odd_factors = gates[d]
            if (gcd(k, d) == 1 and kn % 16 in two_adic
                    and all(jacobi(d, p) == 1 for p in factors if p > 2)
                    and all(jacobi(kn, p) == 1 for p in odd_factors)):
                groups[1 if d > 0 else -1].append(d)
        if not any(groups.values()):
            continue
        spent['walks'] += 1
        for index, norm, sign, numerator, center in convergents(n, k, min(depth, budget-spent['steps'])):
            spent['steps'] += 1
            for d in groups[sign]:
                absolute = abs(d)
                if norm % absolute:
                    continue
                spent['square_tests'] += 1
                t = isqrt(norm//absolute)
                if absolute*t*t != norm:
                    continue
                spent['matches'] += 1
                common = gcd(t, n)
                if 1 < common < n:
                    hit = dict(factor=str(common), kind='scale gcd', multiplier=k, step=index)
                    break
                if common != 1:
                    continue
                root = numerator*pow(t, -1, n) % n
                if (root*root-d) % n:
                    raise ArithmeticError('invalid root')
                if d in roots:
                    common = gcd(root-int(roots[d]['root']), n)
                    kind = 'two roots'
                else:
                    roots[d] = dict(root=str(root), multiplier=k, step=index, visits=spent['steps'])
                    if len(roots) != 3:
                        continue
                    combined = prod(int(w['root']) for w in roots.values())*pow(scale, -1, n) % n
                    if combined**2 % n != 1:
                        raise ArithmeticError('invalid combined square root of one')
                    common = gcd(combined-1, n)
                    kind = 'three roots'
                if 1 < common < n:
                    hit = dict(factor=str(common), kind=kind, target=d, root=str(root),
                               multiplier=k, step=index)
                    break
            if hit or center or norm == 1:
                break
        if hit:
            break
    return dict(targets=targets, roots={str(d): r for d,r in roots.items()}, hit=hit, **spent)


def inputs():
    for bits in (20, 24):
        accepted = sample = 0
        seed = SEED + b'/' + str(bits).encode('ascii')
        while accepted < 32:
            p, q = sorted(draw_prime(side, sample, bits=bits, seed=seed) for side in (b'p', b'q'))
            if p != q and (p*q).bit_length() == 2*bits:
                yield bits, sample, p*q, [str(p), str(q)]
                accepted += 1
            sample += 1
    old = json.loads((ROOT/'benchmarks/target-norm-multipliers.json').read_text())
    for case in old:
        if case['status'] == 'partial':
            yield 1024, case['id'], int(case['n']), None


def certify(rows):
    proofs = []
    for row in rows:
        if not row['factors_found']:
            continue
        source = render_certificate(int(row['n']), [int(x) for x in row['factors_found']])
        body = source.split('namespace PrimeFactors.Generated\n', 1)[1].split('#print axioms', 1)[0]
        proofs.append((row['n'], row['factors_found'], body))
    name = 'PrimeFactors.ThreeTargetPanel'
    lines = ['import PrimeFactors.Certificate', 'import PrimeFactors.Pratt', 'import PrimeFactors.PartialOrder',
             'import Mathlib.Tactic.NormNum.Prime', 'import Mathlib.Tactic.ReduceModChar',
             'set_option maxRecDepth 8192', 'set_option exponentiation.threshold 512', 'namespace '+name]
    for i, (_, _, body) in enumerate(proofs):
        lines.extend([f'namespace Case{i}', body, f'end Case{i}'])
    statements = [f'ExactFactorization {n} [{",".join(pair)}]' for n,pair,_ in proofs]
    lines.append('theorem checked : '+' ∧\n'.join(statements)+' :=\n  ⟨'+
                 ', '.join(f'Case{i}.factorization' for i in range(len(proofs)))+'⟩')
    lines.extend(['#print axioms checked', 'end '+name, ''])
    path = ROOT/'build/ThreeTargetPanel.lean'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text('\n'.join(lines))
    verify_file(path, name+'.checked')
    return dict(theorem=name+'.checked', factorizations=len(proofs), sha256=sha256(path.read_bytes()).hexdigest())


def panel():
    rows = []
    for index, (bits, sample, n, expected) in enumerate(inputs()):
        results = {}
        times = {m: [] for m in METHODS}
        found = []
        for rep in range(len(METHODS)):
            start_at = (index+rep) % len(METHODS)
            for method in METHODS[start_at:] + METHODS[:start_at]:
                start = process_time_ns()
                result = attempt(n, method)
                times[method].append(process_time_ns()-start)
                if method in results and results[method] != result:
                    raise ArithmeticError('replays disagree')
                results[method] = result
                if result['hit']:
                    factor = int(result['hit']['factor'])
                    found = [str(x) for x in sorted((factor, n//factor))]
                    if n % factor or (expected is not None and found != expected):
                        raise ArithmeticError('invalid factors')
        truth = None
        if expected:
            p, q = map(int, expected)
            truth = {m:[d for d in results[m]['targets'] if jacobi(d,p) == jacobi(d,q) == 1]
                     for m in METHODS}
            if not truth['signed'] or not truth['positive']:
                raise ArithmeticError('selected triple contains no square')
        rows.append(dict(bits=bits, sample=sample, n=str(n), factors_found=found, results=results,
                         cpu_ns=times, rootable_validation_only=truth))
    summary=[]
    for bits in (20, 24, 1024):
        selected=[r for r in rows if r['bits']==bits]
        methods={}
        for m in METHODS:
            data=[r['results'][m] for r in selected]
            totals=[sum(r['cpu_ns'][m][i] for r in selected) for i in range(len(METHODS))]
            methods[m]=dict(inputs=len(selected), at_least_one_root=sum(bool(v['roots']) for v in data),
                            splits=sum(bool(v['hit']) for v in data),
                            steps=sum(v['steps'] for v in data), square_tests=sum(v['square_tests'] for v in data),
                            median_batch_cpu_ns=int(median(totals)))
        summary.append(dict(bits=bits, methods=methods))
    return dict(seed=SEED.decode(), multipliers=MULTIPLIERS, depth=DEPTH, budget=BUDGET,
                timing='CPU nanoseconds; four rotated orders, includes setup and stops at first factor.',
                summaries=summary, certificate=certify(rows), rows=rows)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    data = json.dumps(panel(), indent=2)
    if args.output:
        args.output.write_text(data+'\n')
    else:
        print(data)
