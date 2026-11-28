"""Bounded comparison of fractional prefix scans and complete residue correction lists."""

import json
from collections import Counter
from fractions import Fraction
from math import gcd
from pathlib import Path

from experiments.fractional_nonunit_prefix import correction_tables, split_at_sum
from scripts.factor import primes_through


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/fractional-correction-menu.json'


def menu_census(tables, primes):
    counts = Counter()
    counterexamples = {}
    two_correction_classes = {}
    obstruction_minima = {}
    for m, table in tables.items():
        # The shared table builder visits each ordered unit pair and separately
        # checks each product class by modular inversion over all units.
        counts['setup_ordered_unit_pairs'] += len(table)**2
        counts['setup_modular_inverse_checks'] += len(table)**2
        mask = (1 << m)-1
        stride = gcd(m, 20160)
        required = sum(1 << x for x in range(0, m, stride))
        # Keep the number of roots independent of the correction enumeration.
        roots = Counter(x*x % m for x in range(1, m) if gcd(x, m) == 1)
        if m in (7, 27, 64, 45, 80, 144):
            obstruction_minima[str(m)] = min(len({s % m for s in vals}) for vals in table.values())
        for u, ordinary in table.items():
            modular = {s % m for s in ordinary}
            k = len(ordinary)
            if k <= 2:
                two_correction_classes.setdefault(m, []).append(u)
            negatives = sum(1 << (-r % m) for r in modular)
            differences = 0
            for r in modular:
                differences |= ((negatives << r) | (negatives >> (m-r))) & mask
            if differences & required != required or m//stride > k*(k-1)+1:
                raise ArithmeticError(f'Missing difference coverage for m={m}, u={u}')
            counts['unit_product_classes'] += 1
            if m in primes:
                counts['prime_classes'] += 1
                if len(modular) != k or 2*k != m-1+roots[u]:
                    raise ArithmeticError(f'Prime orbit count disagrees at m={m}, u={u}')
            elif len(modular) < k:
                counts['composite_classes_with_more_ordinary_sums'] += 1
                if len(modular)*2 < k:
                    raise ArithmeticError('An ordinary sum has at most two lifts')
                example = dict(modulus=m, product_residue=u, ordinary=sorted(ordinary), modular=sorted(modular))
                counterexamples.setdefault('first_composite', example)
                if m % 2:
                    counterexamples.setdefault('first_odd_composite', example)
    largest = max(two_correction_classes)
    if largest != 120 or two_correction_classes[largest] != [107] or tables[120][107] != {108, 132}:
        raise ArithmeticError('Incorrect largest bounded two-correction class')
    return dict(counts=counts, counterexamples=counterexamples,
                classes_with_at_most_two_corrections=sum(map(len, two_correction_classes.values())),
                moduli_with_at_most_two=sorted(two_correction_classes), greatest_such_tested_modulus=largest,
                attaining_product_residues=two_correction_classes[largest],
                obstruction_minimum_modular_menu_sizes=obstruction_minima)


def full_menu(n, m, tables):
    """Only the given product is used in the prefix, menu lookup and discriminant scan."""
    limit = n//m
    h = sum(gcd(t, n) != 1 for t in range(1, limit+1))
    sums = sorted(m*h+r for r in tables[m][n % m])
    matches = [factors for s in sums if (factors := split_at_sum(n, s)) is not None]
    if len(matches) != 1:
        raise ArithmeticError(f'{len(matches)} factor pairs at n={n}, m={m}')
    return dict(modulus=m, cutoff=limit, nonunits=h, menu_size=len(sums)), sums, matches[0]


def thresholds(n, m, row):
    limit, count = row['cutoff'], row['nonunits']
    variance = m*m*count*(limit-count)
    thresholds = {}
    for name, rms in [('one', Fraction(1)), ('half_modulus', Fraction(m, 2))]:
        tolerance = rms**2
        independent = int(variance//tolerance)+1
        distinct = int((limit*variance)//(variance+tolerance*(limit-1)))+1 if variance else 1
        if variance >= independent*tolerance or (independent > 1 and variance < (independent-1)*tolerance):
            raise ArithmeticError(f'Incorrect independent threshold at {n}, {m}')
        if variance and not (variance*(limit-distinct) < tolerance*distinct*(limit-1)
                             and variance*(limit-distinct+1) >= tolerance*(distinct-1)*(limit-1)):
            raise ArithmeticError(f'Incorrect distinct threshold at {n}, {m}')
        thresholds[name] = dict(iid=independent, distinct=distinct)
    return thresholds


def transcript(tables):
    moduli = (5, 11, 13)
    rows = []
    for n in (89693, 91123):
        choices = []
        hits = []
        for m in moduli:
            reading, sums, factors = full_menu(n, m, tables)
            hits.append(reading['nonunits'])
            choices.append(set(sums))
        survivors = sorted(set.intersection(*choices))
        if n % 715 != 318 or hits != [120, 54, 45] or survivors != [604, 606]:
            raise ArithmeticError(f'Multiple-reading control disagrees at {n}')
        matches = [s for s in survivors if split_at_sum(n, s) is not None]
        if matches != [sum(factors)]:
            raise ArithmeticError(f'Discriminant failed to distinguish candidates at {n}')
        rows.append(dict(product=str(n), residue_mod_715=n % 715, counts=hits,
                         common_candidate_sums=survivors, accepted_sum=matches[0],
                         recovered=[str(f) for f in factors]))
    if rows[0]['accepted_sum'] == rows[1]['accepted_sum']:
        raise ArithmeticError('Different products gave the same decoded sum')
    return dict(moduli=list(moduli), rows=rows)


def study():
    primes = set(primes_through(263))
    tables = {m: correction_tables(m) for m in [*range(2, 241), 257, 263]}
    classification = menu_census(tables, primes)
    paired_controls = []
    for n, expected_sum in [(12827, 228), (15707, 252)]:
        row, sums, factors = full_menu(n, 120, tables)
        if n % 120 != 107 or row['nonunits'] != 1 or sums != [228,252] or sum(factors) != expected_sum:
            raise ArithmeticError(f'Two-correction control failed at {n}')
        paired_controls.append(dict(product=str(n), **row, candidate_sums=sums,
                                    accepted_sum=expected_sum, factors=list(map(str, factors))))
    total = Counter()
    samples = Counter()
    controls = {}
    for q in sorted(primes):
        if not 3 <= q.bit_length() <= 6:
            continue
        for p in sorted(primes):
            if p == 2 or not p < q < 2*p:
                continue
            n = p*q
            total['products'] += 1
            available = []
            selected = []
            for m in tables:
                if (m > 240 and n != 2183) or gcd(n, m) != 1:
                    continue
                row, sums, factors = full_menu(n, m, tables)
                if factors != (p, q) or row['nonunits'] != p//m+q//m:
                    raise ArithmeticError(f'Direct scan disagrees at {n}, m={m}')
                total.update(applicable_cases=1, prefix_gcds=row['cutoff'], menu_entries_tested=len(sums))
                available.append(row)
                if n == 2183 and m in (2, 24, 48, 120, 210, 240, 257, 263):
                    selected.append(row)
                for label, denominator in [('half', 2), ('greatest', gcd(24, n+1))]:
                    if m != denominator:
                        continue
                    t = thresholds(n, m, row)
                    for precision, counts in t.items():
                        samples.update({f'{label}_{precision}_{kind}': k for kind,k in counts.items()})
                    if n == 2183:
                        controls.setdefault('sample_thresholds', {})[label] = dict(modulus=m, **t)
            # A coordinatewise tradeoff, without combining a gcd and a discriminant into one cost.
            if n == 2183:
                frontier = []
                for row in sorted(available, key=lambda r: (r['cutoff'], r['menu_size'], r['modulus'])):
                    if not frontier or row['menu_size'] < frontier[-1]['menu_size']:
                        frontier.append(row)
                controls.update(selected_denominators=selected, nondominated_with_one_denominator_per_tie=frontier)
    return dict(scope='All 57 balanced 3–6-bit larger-prime products and all coprime moduli 2 through 240. Add m=257,263 at 2183.',
                measured_cost='Prefix gcds and complete ordinary menu sizes are separate counts. Menu setup and lookups are excluded. All candidate sums were checked.',
                classification=classification, cohort=dict(total), fixed_precision_totals=dict(samples),
                control_2183=controls, two_correction_controls=paired_controls,
                same_transcript=transcript(tables))


if __name__ == '__main__':
    result = study()
    if result != json.loads(FIXTURE.read_text()):
        raise SystemExit('Fractional correction menu census differs from the reviewed fixture')
    print(f"Checked {result['cohort']['applicable_cases']} prefix/menu combinations and "
          f"{result['classification']['counts']['unit_product_classes']} unit-product classes.")
