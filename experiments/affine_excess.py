"""Test the bounded family of weights a²N+b using exact normalized excesses.

Run python3 -m experiments.affine_excess to reproduce the archived census.
The search takes only N, K and J. Each arm runs to its stated finite end.
"""

from collections import Counter
from itertools import combinations
import json
from math import gcd, isqrt
from pathlib import Path

from experiments.weighted_square_pairs import first_label
from scripts.factor import primes_through


REPO = Path(__file__).resolve().parents[1]


def normalized_rows(n, k, j_count):
    """Attach one generating (a,b,j) to each distinct (u,c)."""
    if n <= 1 or gcd(n, 6) != 1 or k < 1 or j_count < 1:
        raise ValueError('expected N>1 coprime to 6 and positive grid limits')
    result = {}
    fallbacks = 0
    residue = n % 24
    for a in range(1, k+1):
        for b in range(1, k+1):
            bottom = (b+a-1)//a
            # A=2aN+bottom is the first raw ceiling iff the preceding point is below.
            if (bottom-1)**2 < 4*n*(b-a*(bottom-1)):
                stride = gcd(24, 2*((a*a+1)*residue+b))
                c = bottom + ((a-1)**2*residue+b-bottom) % stride
            else:
                label, stride = first_label(n, a*a*n+b)
                c = label - 2*a*n
                fallbacks += 1
            for j in range(j_count):
                result.setdefault((a*c-b, c), (a, b, j))
                c += stride
    return dict(sorted(result.items())), fallbacks


def proper_signs(n, label, root, work, counter):
    """Try both square signs. Count gcds even if a sign is trivial or repeats."""
    work[counter] += 2
    minus, plus = gcd(n, label-root), gcd(n, label+root)
    return [d if 1 < d < n else None for d in (minus, plus)]


def compare(n, k, j_count):
    rows, fallback = normalized_rows(n, k, j_count)
    sites = k*k*j_count
    work = Counter(dict(proposal_labels=sites, stride_gcds=k*k, setup_gcds=1, ceiling_roots=fallback,
                        distinct_labels=len(rows), duplicates=sites-len(rows), pairs=0,
                        zero_slope_pairs=0, proportional_pairs=0, positive_nonsingular=0,
                        signed_nonsingular=0, proper_pair_minus=0, proper_pair_plus=0,
                        proper_pair_either=0,
                        square_weight_pruned=0, weight_product_roots=0, joint_square_tests=0,
                        reconstructed_squares=0, nonsingular_squares=0, affine_single_roots=0,
                        affine_single_gcds=0, pair_gcds=0, ordinary_roots=0, ordinary_gcds=0,
                        raw_label_roots=0, raw_excess_roots=0, raw_gcds=0,
                        stride_label_roots=0, stride_excess_roots=0, stride_setup_gcds=0,
                        stride_gcds_baseline=0))
    hits = {}
    def remember(arm, data, signs):
        if any(signs) and arm not in hits:
            hits[arm] = dict(**data, minus=None if signs[0] is None else str(signs[0]),
                             plus=None if signs[1] is None else str(signs[1]))

    mid = isqrt(n-1)+1
    ordinary = isqrt(mid*mid-n)
    work['ordinary_roots'] = 2
    if ordinary*ordinary == mid*mid-n:
        remember('ordinary', dict(midpoint=str(mid)),
                 proper_signs(n, mid, ordinary, work, 'ordinary_gcds'))

    small_weights = sorted({u for u, c in rows if u > 0})
    for u in small_weights:
        raw = isqrt(4*u*n-1)+1
        label, _ = first_label(n, u)
        work['raw_label_roots'] += 1
        work['stride_label_roots'] += 1
        work['stride_setup_gcds'] += 1
        for name, m, counter in [('raw', raw, 'raw_gcds'), ('stride', label, 'stride_gcds_baseline')]:
            work[name+'_excess_roots'] += 1
            delta = m*m-4*u*n
            root = isqrt(delta)
            if root*root == delta:
                remember(name, dict(weight=u, label=str(m)), proper_signs(n, m, root, work, counter))

    values = {}
    for (u, c), source in rows.items():
        excess = 4*u*n+c*c
        root = isqrt(excess)
        work['affine_single_roots'] += 1
        square_root = root if root*root == excess else None
        values[u, c] = (excess, square_root)
        if square_root is not None:
            remember('affine_single', dict(row=[u, c], source=list(source)),
                     proper_signs(n, c, root, work, 'affine_single_gcds'))

    weight_is_square = {}
    for left, right in combinations(rows, 2):
        work['pairs'] += 1
        u, c = left
        v, d = right
        f, froot = values[left]
        g, groot = values[right]
        delta = u*d*d-v*c*c
        if u == 0 or v == 0:
            work['zero_slope_pairs'] += 1
            if froot is None or groot is None:
                continue
            root = froot*groot
            arm = 'zero_slope'
        elif delta == 0:
            work['proportional_pairs'] += 1
            root, remainder = divmod(f*d, c)
            if remainder or root*root != f*g:
                raise ArithmeticError('proportional rows failed the exact square identity')
            arm = 'proportional'
        else:
            if u > 0 and v > 0:
                work['positive_nonsingular'] += 1
                uv = u*v
                if uv not in weight_is_square:
                    weight_is_square[uv] = isqrt(uv)**2 == uv
                    work['weight_product_roots'] += 1
                if weight_is_square[uv] and delta*delta < 8*uv*n:
                    work['square_weight_pruned'] += 1
                    continue
            else:
                work['signed_nonsingular'] += 1
            work['joint_square_tests'] += 1
            root = isqrt(f*g)
            if root*root != f*g:
                continue
            work['nonsingular_squares'] += 1
            arm = 'nonsingular'
        if arm != 'nonsingular':
            work['reconstructed_squares'] += 1
        signs = proper_signs(n, c*d, root, work, 'pair_gcds')
        if any(signs):
            work['proper_pair_minus'] += int(signs[0] is not None)
            work['proper_pair_plus'] += int(signs[1] is not None)
            work['proper_pair_either'] += 1
            data = dict(rows=[list(left), list(right)], sources=[list(rows[left]), list(rows[right])],
                        excesses=[str(f), str(g)], root=str(root))
            remember(arm, data, signs)
            if arm == 'nonsingular' and froot is None and groot is None:
                remember('two_nonsquares', data, signs)
    return dict(n=str(n), source_limit=k, labels_per_source=j_count, work=dict(work),
                small_baseline_weights=len(small_weights), hits=hits, remaining_pairs=0,
                unresolved_cofactor=None if hits else str(n))


def census(bits, k, j_count):
    lower = 1 << (bits-1)
    primes = [p for p in primes_through(2*lower-1) if p >= lower]
    counts = Counter(dict.fromkeys(('eligible','ordinary','raw','stride','affine_single',
        'zero_slope','proportional','nonsingular','two_nonsquares','beyond_baselines'), 0))
    work = Counter()
    example = None
    for p, q in combinations(primes, 2):
        n = p*q
        if n < 2*lower*lower:
            continue
        result = compare(n, k, j_count)
        work.update(result['work'])
        counts['eligible'] += 1
        hits = result['hits']
        for arm, hit in hits.items():
            counts[arm] += 1
            for sign in ('minus', 'plus'):
                if hit[sign] and int(hit[sign]) not in (p, q):
                    raise ArithmeticError('split differs from independent sieve labels')
        if 'nonsingular' in hits and not any(x in hits for x in ('ordinary','raw','stride','affine_single')):
            counts['beyond_baselines'] += 1
        if example is None and 'two_nonsquares' in hits:
            example = dict(n=str(n), hits=hits)
    return dict(factor_bits=bits, source_limit=k, labels_per_source=j_count,
                counts=dict(counts), work=dict(work), first_two_nonsquares=example)


def report():
    controls = json.loads((REPO/'benchmarks/factor-sum-quantile.json').read_text())[-2:]
    return dict(reproduce='python3 -m experiments.affine_excess',
                exhaustive=[census(b, 4, 1) for b in (7, 8, 9, 10)],
                enlarged=census(7, 8, 2),
                controls=[dict(id=row['id'], **compare(int(row['n']), 8, 1)) for row in controls])


if __name__ == '__main__':
    print(json.dumps(report(), indent=2))
