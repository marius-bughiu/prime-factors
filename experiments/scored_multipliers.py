"""Choose a continued-fraction multiplier by the small-prime norm valuations."""

import argparse
from fractions import Fraction
from functools import lru_cache
import json
from math import gcd, isqrt, lcm
from pathlib import Path
import sys
from typing import NamedTuple

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from experiments.pell_relations import search as relation_search
from experiments.sieve_forecast import primes_through

PRIMES = tuple(primes_through(97))
MULTIPLIERS = tuple(m for m in range(1, 64, 2) if all(m % (p*p) for p in (3, 5, 7)))
MODES = ('one', 'dyadic', 'scored')


@lru_cache(maxsize=None)
def log_weight(t):
    """floor(256 log_2(t)), evaluated by integer arithmetic."""
    return (t**256).bit_length() - 1


class ScoreRow(NamedTuple):
    multiplier: int
    base: int
    comparisons: tuple[tuple[int, bool, int], ...]


class ScoreTable(NamedTuple):
    denominator: int
    squares: tuple[frozenset[int], ...]
    dyadic: tuple[int, ...]
    rows: tuple[ScoreRow, ...]
    profile: dict[str, int]


@lru_cache(maxsize=1)
def score_table():
    """Precompute the local signs of the fixed multiplier menu and exact integer weights."""
    primes = PRIMES[1:]
    denominator = lcm(6, *(p*p-1 for p in primes))
    squares = tuple(frozenset(x*x % p for x in range(1, (p+1)//2)) for p in primes)
    split_weights = [2*p*log_weight(p)*(denominator//(p*p-1)) for p in primes]
    rows = []
    for m in MULTIPLIERS:
        base = -log_weight(m)*(denominator//2)
        comparisons = []
        for i, p in enumerate(primes):
            residue = m % p
            if residue == 0:
                base += log_weight(p)*(denominator//(p+1))
            else:
                comparisons.append((i, residue in squares[i], split_weights[i]))
        rows.append(ScoreRow(m, base, tuple(comparisons)))
    comparisons = sum(len(row.comparisons) for row in rows)
    profile = dict(odd_primes=len(primes), squares_generated=sum(map(len, squares)),
                   multiplier_prime_pairs=len(primes)*len(rows), unit_pairs=comparisons,
                   ramified_pairs=len(primes)*len(rows)-comparisons)
    dyadic_unit = log_weight(2)*(denominator//3)
    dyadic = tuple(twos*dyadic_unit for twos in (4, 1, 2, 1))
    return ScoreTable(denominator, squares, dyadic, tuple(rows), profile)


def _score(residue8, signs, row, dyadic):
    """Score numerator at the common denominator, given one valuation signature."""
    odd_class = (residue8 * row.multiplier) % 8
    total = row.base + dyadic[odd_class//2]
    for i, expected, bonus in row.comparisons:
        if signs[i] == expected:
            total += bonus
    return total


def search(n, mode, max_steps, *, use_gmp=False, external=1):
    """Return one split or the complete bounded walk and multiplier-selection costs."""
    if n <= 1 or max_steps < 0 or mode not in MODES or external < 1:
        raise ValueError('expected n > 1, a known mode, nonnegative steps and positive external support')
    work = dict(factor=None, outcome='no_split', multiplier=None, score=None, candidates=0,
                table_profile=None, residue_checks=0, multiplier_gcds=0, sign_comparisons=0, steps=0, center=False, rows=0,
                private_pruned=0, pruning_rounds=0, min_private_bits=None,
                dependencies=0, tested=0, selected_steps=[])
    if n % 2 == 0:
        return dict(work, factor=2, outcome='even') if n > 2 else work
    s = isqrt(n)
    if s*s == n:
        return dict(work, factor=s, outcome='perfect_square')

    chosen = 1
    if mode == 'dyadic':
        for m in MULTIPLIERS:
            work['candidates'] += 1
            if m*n % 8 == 1:
                chosen = m
                break
        work['multiplier_gcds'] += 1
        g = gcd(n, chosen)
        if 1 < g < n:
            return dict(work, multiplier=chosen, factor=g, outcome='multiplier_gcd')
        if g == n:
            # The first odd representative of a class modulo eight is 1, 3, 5 or 7.
            return dict(work, multiplier=chosen, outcome='small_prime')
    elif mode == 'scored':
        table = score_table()
        work['table_profile'] = dict(table.profile)
        signs = []
        for p, square_set in zip(PRIMES[1:], table.squares):
            work['residue_checks'] += 1
            residue = n % p
            if residue == 0:
                if p < n:
                    return dict(work, factor=p, outcome='prime_gcd')
                return dict(work, outcome='small_prime')
            signs.append(residue in square_set)
        residue8 = n % 8
        best = None
        for row in table.rows:
            work['candidates'] += 1
            work['sign_comparisons'] += len(row.comparisons)
            value = _score(residue8, signs, row, table.dyadic)
            if best is None or value > best:
                best, chosen = value, row.multiplier
        work['score'] = str(Fraction(best, table.denominator))
    work['multiplier'] = chosen
    walk = relation_search(n, chosen, max_steps, use_gmp=use_gmp, external=external)
    return work | walk


def run_holdout(verify):
    from experiments.crt_holdout import draw_sample, verify_cases

    seed = b'crt-cf-score-v1'
    cases = []
    patterns = {}
    for attempt, n, known in draw_sample(seed=seed, count=64):
        methods = {}
        for mode in MODES:
            work = search(n, mode, 5138)
            f = work.pop('factor')
            work.pop('table_profile')
            if f is not None and (f not in known or n % f):
                raise ValueError('incorrect split')
            # Omit witness step lists from the survey. The fixed schedule reproduces them.
            work['selected_count'] = len(work.pop('selected_steps'))
            methods[mode] = dict(factors=[] if f is None else [str(x) for x in sorted((f, n//f))],
                                 remaining=[str(n)] if f is None else [], work=work)
        pattern = '+'.join(mode for mode in MODES if methods[mode]['factors']) or 'none'
        patterns[pattern] = patterns.get(pattern, 0) + 1
        cases.append(dict(attempt=attempt, n=str(n), expected_factors=[str(x) for x in known],
                          methods=methods))
    if verify:
        verify_cases(cases, ROOT / 'build' / 'scored-holdout')
    return dict(seed=seed.decode(), count=len(cases), max_steps=5138, table_profile=score_table().profile,
                patterns=dict(sorted(patterns.items())), cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int, nargs='?')
    parser.add_argument('--mode', choices=MODES, default='scored')
    parser.add_argument('--max-steps', type=int, default=5138)
    parser.add_argument('--holdout', action='store_true')
    parser.add_argument('--verify', action='store_true')
    parser.add_argument('--gmp', action='store_true')
    parser.add_argument('--external-smooth', type=int)
    args = parser.parse_args()
    if args.holdout:
        report = run_holdout(args.verify)
        path = ROOT / 'research' / 'scored-holdout.json'
        path.write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps(report['patterns']))
        return
    if args.n is None:
        parser.error('supply a product or --holdout')
    external = 1
    if args.external_smooth is not None:
        if not args.gmp or args.external_smooth < 1:
            parser.error('--external-smooth requires --gmp and a positive bound')
        from gmpy2 import primorial
        external = primorial(args.external_smooth)
    print(json.dumps(search(args.n, args.mode, args.max_steps, use_gmp=args.gmp, external=external)))


if __name__ == '__main__':
    main()
