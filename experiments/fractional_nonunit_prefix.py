"""Compare measured nonunit prefixes and residue corrections on balanced toy products."""

import json
from collections import Counter
from math import gcd, isqrt
from pathlib import Path

from experiments.square_mask_digit_queries import odd_trial
from scripts.factor import primes_through


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/fractional-nonunit-prefix.json'


def correction_tables(m):
    """Group all ordinary representative sums by their product residue."""
    units = [x for x in range(1, m) if gcd(x, m) == 1]
    sums = {u: set() for u in units}
    for x in units:
        for y in units:
            sums[x*y % m].add(x+y)
    for u, values in sums.items():
        inverse_sums = {x+(u*pow(x, -1, m) % m) for x in units}
        if inverse_sums != values or {2*m-r for r in values} != values:
            raise ArithmeticError(f'Residue-pair enumeration failed for {m}, {u}')
        constant = u == m-1 and 24 % m == 0
        if (len(values) == 1) != constant or (constant and values != {m}):
            raise ArithmeticError(f'Constant-correction classification failed for {m}, {u}')
    return sums


def split_at_sum(n, total):
    discriminant = total*total-4*n
    if discriminant < 0:
        return None
    gap = isqrt(discriminant)
    if gap*gap != discriminant or (total-gap) % 2:
        return None
    left, right = (total-gap)//2, (total+gap)//2
    if 1 < left <= right and left*right == n:
        return left, right
    return None


def measure(n, m, tables):
    """Count every positive nonunit up to the cutoff, with N and m as the sole inputs."""
    cutoff = n//m
    terms = [t for t in range(1, cutoff+1) if gcd(t, n) > 1]
    count = len(terms)
    corrections = sorted(tables[n % m])
    sums = [m*count+r for r in corrections]
    matches = [pair for total in sums if (pair := split_at_sum(n, total)) is not None]
    if len(matches) != 1:
        raise ArithmeticError(f'Failed to split {n} at m={m}: {sums}')
    first = terms[0] if terms else None
    row = dict(product=str(n), modulus=m, product_residue=n % m, cutoff=cutoff,
               count=count, corrections=corrections, candidate_sums=sums,
               discriminants_tested=len(sums), nonnegative_discriminants=sum(s*s >= 4*n for s in sums),
               recovered=[str(d) for d in matches[0]], full_prefix_gcds=cutoff,
               gcds_through_first_or_exhaustion=first or cutoff,
               first_nonunit=first)
    return row, terms


def study():
    tables = {m: correction_tables(m) for m in range(2, 49)}
    primes = [p for p in primes_through(63) if p % 2]
    constant = [(m, u) for m, table in tables.items() for u, sums in table.items() if len(sums) == 1]
    totals = Counter()
    per_modulus = {m: Counter() for m in (24, 48)}
    controls = []
    for q in primes:
        for p in primes:
            if not (3 <= q.bit_length() <= 6 and p < q < 2*p):
                continue
            n = p*q
            factor, trial = odd_trial(n)
            if factor != p:
                raise ArithmeticError(f'Unexpected balanced trial divisor of {n}')
            totals['products'] += 1
            totals['trial_checks_once_ascending'] += trial['ascending_divisibility_checks']
            totals['trial_checks_once_descending'] += trial['descending_divisibility_checks']
            for m, table in tables.items():
                common = gcd(n, m)
                if common != 1:
                    key = 'denominator_gcd_equals_product' if common == n else 'denominator_gcd_proper'
                    totals[key] += 1
                    continue
                row, terms = measure(n, m, table)
                if (row['count'] != p//m+q//m or row['recovered'] != [str(p), str(q)]
                        or row['first_nonunit'] != (p if p <= row['cutoff'] else None)):
                    raise ArithmeticError(f'Reference check failed for {n} at {m}')
                stats = dict(coprime_cases=1, proper_prefix_hits=int(bool(terms)),
                             empty_prefixes=int(not terms), single_correction_cases=int(len(row['corrections']) == 1),
                             full_prefix_gcds=row['full_prefix_gcds'],
                             gcds_through_first_or_exhaustion=row['gcds_through_first_or_exhaustion'],
                             candidate_sums_tested=row['discriminants_tested'],
                             nonnegative_discriminants=row['nonnegative_discriminants'],
                             matched_trial_checks_ascending=trial['ascending_divisibility_checks'],
                             matched_trial_checks_descending=trial['descending_divisibility_checks'])
                totals.update(stats)
                if m in per_modulus:
                    per_modulus[m].update(stats)
                if n in (527, 2183) and m in per_modulus:
                    controls.append(dict(**row, nonunits=terms, odd_trial=trial))
    return dict(population='Every distinct odd prime pair p < q < 2p with larger prime of 3–6 bits.',
                moduli='Every m from 2 through 48. Unit-pair decoding requires gcd(m,N)=1.',
                costs='Full prefix scans test integers from 1. Early scans stop at the first nonunit or exhaust the prefix. Matched trial totals repeat one trial scan for each applicable modulus.',
                unit_product_classes=sum(map(len, tables.values())),
                globally_constant_classes=[dict(modulus=m, product_residue=u, correction=m) for m, u in constant],
                totals=dict(totals), by_modulus={str(m):dict(stats) for m, stats in per_modulus.items()},
                examples=controls)


if __name__ == '__main__':
    result = study()
    if result != json.loads(FIXTURE.read_text()):
        raise SystemExit('Fractional prefix census differs from the reviewed fixture.')
    print(f"Checked {result['totals']['coprime_cases']} fractional prefixes on {result['totals']['products']} products.")
