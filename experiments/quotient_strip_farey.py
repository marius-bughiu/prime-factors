"""Reuse neighboring Farey slopes across balanced factor-search strips."""
import argparse
import json
import platform
from collections import Counter
from fractions import Fraction
from math import gcd
from statistics import median
from time import process_time_ns

from experiments.continued_square import convergents
from experiments.quotient_strip_levels import FIXTURE as LEVEL_FIXTURE, chord_levels, schedule, simple_odd, solve_levels
from experiments.quotient_strip_localization import holdout_cohort, ratio_cohort


FIXTURE = LEVEL_FIXTURE.with_name('quotient-strip-farey.json')
METHODS = ('cf_mod8', 'farey_mod8', 'farey_stride24', 'farey_exact24')
LARGER = ('modular-hyperbola-41', 'modular-hyperbola-holdout-binary-46')
GCD24 = tuple(gcd(i, 24) for i in range(24))
STRIDES = {m: tuple(gcd(2*i, m) for i in range(m)) for m in (8, 24)}


def convergent(n, denominator, limit, work, counter):
    """Return the last allowed convergent and its predecessor for a Farey seed."""
    current, previous = (1, 0), (0, 1)
    for p, q in convergents(n, denominator):
        work[counter] += 1
        if q > limit:
            break
        previous, current = current, (p, q)
    return current, previous


class FareyWalk:
    """Follow decreasing target slopes in [1,2] at one denominator limit."""

    def __init__(self, limit):
        self.limit = limit
        self.current = None
        self.left = None

    def seed(self, n, denominator, work):
        limit = self.limit
        difference = n*(limit+1) - denominator*(2*limit+1)
        work['mediant_comparisons'] += 1
        if difference > 0 or (difference == 0 and limit > 1):
            self.current, self.left = (2, 1), (2*limit-1, limit)
            return
        # Starting inside the band needs one CF, independent of how much of
        # the right-hand arc a supplied starting index has skipped.
        self.current, previous = convergent(n, denominator, limit, work, 'seed_cf_divmods')
        u, v = self.current
        if self.current == (1, 1):
            return
        if v == 1:
            self.left = u*limit-1, limit
            return
        p, q = previous
        if u*q-v*p != 1:
            p, q = u-p, v-q
        k = (limit-q)//v
        work['neighbor_divisions'] += 1
        self.left = p+k*u, q+k*v

    def choose(self, n, denominator, work):
        if self.current is None:
            self.seed(n, denominator, work)
            return self.current
        while self.left:
            u, v = self.current
            p, q = self.left
            difference = n*(v+q) - denominator*(u+p)
            work['mediant_comparisons'] += 1
            # Either parent has the same error at the mediant. Match the
            # finite CF by taking the smaller denominator, then the lower integer.
            if difference > 0 or (difference == 0 and v < q):
                break
            self.current = self.left
            work['farey_switches'] += 1
            if self.current == (1, 1):
                self.left = None
            else:
                k = (self.limit+v)//q
                work['neighbor_divisions'] += 1
                self.left = k*p-u, k*q-v
        return self.current


def chord_bounds(n, a, b, u, v):
    """Integer endpoints of the original chord enclosure for supplied weights."""
    denominator = 4*a*a*b
    left = 4*a*b*(u*a*a+v*n)
    right = 4*a*a*(u*b*b+v*n)
    lower_numerator = min(left, right) - v*n*(b-a)**2
    return -(-lower_numerator//denominator), max(left, right)//denominator


def admissible_levels(low, high, c, modulus, exact, work):
    step = STRIDES[modulus][c]
    work['stride_start_remainders'] += 1
    for z in range(low+(c-low)%step, high+1, step):
        work['stride_labels'] += 1
        if exact:
            work['exact_residue_tests'] += 1
            if GCD24[z%24] != GCD24[c]:
                continue
        yield z


def scan(n, method, stop=False, start_index=0):
    if method not in METHODS or n < 9 or start_index < 0:
        raise ValueError('Expected a registered method, N ≥ 9 and a nonnegative starting index')
    modulus = 8 if method.endswith('mod8') else 24
    n_residue = n%modulus
    if gcd(n_residue, modulus) != 1:
        raise ValueError('Input must be coprime to the residue modulus')
    low, high, width = schedule(n)
    limit = max(1, (width-1)//2)
    # schedule performs a binary search on [0,2^k]. Only values 0 and 1
    # need its extra final halving. All supported products give a positive width.
    steps = (n.bit_length()+5)//6 + int(width == 2)
    work = Counter(schedule_square_roots=2, schedule_bitlength_divisions=1, schedule_band_halvings=1,
                   schedule_midpoint_halvings=steps, schedule_sixth_power_comparisons=steps,
                   input_residue_remainders=1, input_gcd_tests=1, main_cap_halvings=1)
    walk = FareyWalk(limit)
    hits, first = [], None
    for a in range(low+start_index*width, high+1, width):
        b = min(a+width-1, high)
        work['strips'] += 1
        if a == b:
            work['divisibility_tests'] += 1
            answers = [a] if n%a == 0 else []
        else:
            cap = limit
            if b-a+1 < width:
                cap = max(1, (b-a)//2)
                work['tail_cap_halvings'] += 1
                (u, v), _ = convergent(n, a*b, cap, work, 'tail_cf_divmods')
            elif method == 'cf_mod8':
                (u, v), _ = convergent(n, a*b, cap, work, 'independent_cf_divmods')
            else:
                u, v = walk.choose(n, a*b, work)
            work['slope_certificate_checks'] += 1
            if not (1 <= v <= cap and abs(u*a*b-v*n)*(cap+1) <= a*b):
                raise ArithmeticError(f'Invalid slope certificate at {n}, {a}, {b}')
            lower, upper = chord_bounds(n, a, b, u, v)
            work['level_endpoint_divisions'] += 2
            if lower > upper:
                continue
            c = (u+n_residue*v)%modulus
            work['direction_residue_remainders'] += 1
            levels = admissible_levels(lower, upper, c, modulus, method == 'farey_exact24', work)
            # Each level goes through the same quadratic/verification routine
            # as the old strip experiment. The enclosing range here is a singleton.
            answers = (x for z in levels for x in solve_levels(n, a, b, (u, v, z, z), False, work))
        for x in answers:
            hits.append(x)
            if first is None:
                first = work.copy()
            if stop:
                return hits, work, first
    return hits, work, first


def slope_controls():
    """Compare with the true minimum error, then check the canonical implementation's tie choice."""
    checks = ties = 0
    for order in range(1, 17):
        slopes = sorted({Fraction(p, q) for q in range(1, order+1) for p in range(q, 2*q+1)})
        directions = [(f.numerator, f.denominator) for f in slopes]
        targets = {Fraction(i, 120) for i in range(120, 241)}
        for left, right in zip(slopes, slopes[1:]):
            middle = Fraction(left.numerator+right.numerator, left.denominator+right.denominator)
            epsilon = Fraction(1, 100000)
            targets.update((middle-epsilon, middle, middle+epsilon))
        targets = sorted(targets, reverse=True)
        for start in (0, len(targets)//3, 2*len(targets)//3, len(targets)-1):
            walk = FareyWalk(order)
            for target in targets[start:]:
                a, b = target.numerator, target.denominator
                u, v = walk.choose(a, b, Counter())
                errors = [abs(p*b-q*a) for p, q in directions]
                minimum = min(errors)
                if abs(u*b-v*a) != minimum or minimum*(order+1) > b:
                    raise ArithmeticError('Farey walk failed minimum-error or certificate check')
                if (u, v) != convergent(a, b, order, Counter(), 'cf')[0]:
                    raise ArithmeticError('Canonical walk tie convention differs from finite CF')
                checks += 1
                ties += int(errors.count(minimum) > 1)
    return dict(order_range=[1, 16], queries=checks, minimum_error_ties=ties)


def residue_controls():
    units = [x for x in range(24) if GCD24[x] == 1]
    cases = strict = 0
    for n in units:
        for u in range(24):
            for v in range(24):
                c = (u+n*v)%24
                # Enumerate all possible unit factor residues independently.
                oracle = {(u*x+v*n*pow(x, -1, 24))%24 for x in units}
                exact = set(admissible_levels(0, 23, c, 24, True, Counter()))
                stride = set(admissible_levels(0, 23, c, 24, False, Counter()))
                if exact != oracle or not exact <= stride:
                    raise ArithmeticError('Exact filter differs from the local unit orbit')
                cases += 1
                strict += int(exact != stride)
    return dict(modulus=24, residue_triples=cases, strict_subsets_of_stride=strict)


def direct_controls():
    counts = Counter()
    for n in range(9, 5001, 2):
        if n%3 == 0:
            continue
        a, b, _ = schedule(n)
        expected = [x for x in range(a, b+1) if n%x == 0]
        for method in ('farey_stride24', 'farey_exact24'):
            hits, _, first = scan(n, method)
            if sorted(hits) != expected or bool(first) != bool(expected):
                raise ArithmeticError(f'{method} disagrees with direct trial on {n}')
        counts['products'] += 1
        counts['products_with_multiple_balanced_divisors'] += int(len(expected)>1)
        counts['products_without_balanced_divisors'] += int(not expected)
    named = []
    for n in (385385, 715715):
        expected = simple_odd(n, False)
        for method in METHODS:
            hits, _, first = scan(n, method)
            stopped, counters, _ = scan(n, method, stop=True)
            if sorted(hits) != expected or stopped != hits[:1] or counters != first:
                raise ArithmeticError(f'Multiple-divisor or early-stop mismatch at {n}')
        named.append(dict(product=str(n), balanced_divisors=expected))
    return dict(exhaustive=counts, multiple_divisor_examples=named)


def canonical_blocks(n, offset=0):
    """Regression check of the canonical tie convention and original chord formula."""
    low, high, width = schedule(n)
    limit = max(1, (width-1)//2)
    walk = FareyWalk(limit)
    count = 0
    for a in range(low+offset*width, high+1, width):
        b = min(high, a+width-1)
        if a == b:
            continue
        if b-a+1 == width:
            u, v = walk.choose(n, a*b, Counter())
        else:
            (u, v), _ = convergent(n, a*b, max(1, (b-a)//2), Counter(), 'cf')
        original = chord_levels(n, a, b, False, Counter())
        if (u, v, *chord_bounds(n, a, b, u, v)) != original:
            raise ArithmeticError(f'Canonical direction or original endpoints differ at {n}, {a}, {b}')
        count += 1
    return count


def public_controls():
    rows = json.loads(FIXTURE.with_name('modular-hyperbola.json').read_text())
    return {name: next(row for row in rows if row['id'] == name) for name in LARGER}


def compare(products, prior):
    canonical = sum(canonical_blocks(n) for n, _ in products)
    methods = {}
    for method in METHODS:
        total, early = Counter(), Counter()
        for n, expected in products:
            hits, complete, first = scan(n, method)
            if hits != [expected]:
                raise ArithmeticError(f'{method} produced {hits} at {n}')
            total.update(complete)
            early.update(first)
            if len(products) == 1:
                stopped_hits, stopped, _ = scan(n, method, stop=True)
                if stopped != first or stopped_hits != [expected]:
                    raise ArithmeticError('Explicit early stop disagrees with first-hit snapshot')
        for key in ('complete', 'to_first'):
            counts = total if key == 'complete' else early
            # The source solver uses singleton input ranges here; bounded_levels
            # and blocks_with_1_levels would duplicate tested_levels.
            counts.pop('bounded_levels', None)
            counts.pop('blocks_with_1_levels', None)
            if method.endswith('mod8'):
                old = prior[key]
                if (counts['strips'], counts['tested_levels'], counts['discriminant_square_roots']) != (
                        old['initial_blocks'], old['tested_levels'], old['discriminant_square_roots']):
                    raise ArithmeticError(f'{method} differs from the original chord receipt')
        methods[method] = dict(complete=total, to_first=early)
    return dict(products=len(products), canonical_nonsingleton_blocks=canonical, methods=methods)


def study():
    previous = json.loads(LEVEL_FIXTURE.read_text())
    groups = {}
    for name, pairs in (('ratio', ratio_cohort()), ('holdout', holdout_cohort())):
        data = [(p*q, p) for p, q in pairs]
        if any(simple_odd(n, False) != [p] for n, p in data):
            raise ArithmeticError(f'{name} labels disagree with direct trial')
        groups[name] = compare(data, previous[name]['methods']['chord_mod8'])
    for name, row in public_controls().items():
        n = int(row['n'])
        original = next(item for item in previous['larger_controls'] if item['input_id'] == name)
        if str(n) != original['product'] or original['recovered'] != row['factors']:
            raise ArithmeticError(f'Original controls disagree for {name}')
        measured = compare([(n, int(row['factors'][0]))], original['chord_mod8'])
        low, high, width = schedule(n)
        offset = (high-low)//(2*width)
        suffix = canonical_blocks(n, offset)
        groups[name] = dict(product=row['n'], expected_factors=row['factors'],
                            suffix_start=offset, canonical_suffix_blocks=suffix, **measured)
    return dict(inputs='The 99 prescribed-ratio products and 64 holdouts use the preceding strip study. The two larger products come directly from modular-hyperbola.json. Only N reaches the scan.',
                methods='All four scans use the same chord bounds. The independent baseline and first Farey comparison use the modulus-8 progression. WeightedStride takes the one modulus-24 progression with step gcd(24,2C). The exact filter additionally requires gcd(z,24)=gcd(C,24) for C=u+Nv and input coprime to six.',
                work='Counts include both setup square roots and the sixth-root binary search, slope selection and certificate, chord endpoint divisions, residue checks, square discriminants and final divisions. All endpoint positions are scanned in ascending blocks. To-first stops on the successful quadratic solution. Fixed 8/24 lookup tables and independent reference checks are excluded. Counters are in different units.',
                slope_controls=slope_controls(), residue_controls=residue_controls(), direct_controls=direct_controls(),
                groups=groups)


def timings():
    print(platform.python_implementation(), platform.python_version(), platform.platform(), platform.machine())
    names = (*METHODS, 'direct_odd')
    for name, row in public_controls().items():
        n, expected = int(row['n']), int(row['factors'][0])
        for stop in (False, True):
            samples = {method: [] for method in names}
            for repetition in range(6):
                rotation = repetition%len(names)
                for method in names[rotation:]+names[:rotation]:
                    start = process_time_ns()
                    hits = simple_odd(n, stop) if method == 'direct_odd' else scan(n, method, stop)[0]
                    elapsed = process_time_ns()-start
                    if hits != [expected]:
                        raise ArithmeticError('Timing returned incorrect factors')
                    if repetition:
                        samples[method].append(elapsed)
            print(name, 'to_first' if stop else 'complete', 'median CPU milliseconds',
                  {method: round(median(values)/1e6, 3) for method, values in samples.items()})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timings', action='store_true', help='also time both larger controls with counters enabled')
    if parser.parse_args().timings:
        timings()
    if study() != json.loads(FIXTURE.read_text()):
        raise SystemExit('Farey strip measurements differ from the reviewed fixture')
    print('Verified the Farey walk, both modulus-24 filters and all 165 study products.')
