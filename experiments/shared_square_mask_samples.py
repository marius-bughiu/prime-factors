"""Exact joint moments for public digit-query masks evaluated on the same residues.

The Jacobi observations and direct divisor tests use only the product and the
balanced-prime promise. Reference primes check every measured moment by CRT.
"""

import json
from collections import Counter
from itertools import combinations
from math import gcd, isqrt
from pathlib import Path

from experiments.jacobi_square_masks import mask_from_roots
from experiments.mixed_ratio_heights import jacobi
from experiments.square_mask_digit_queries import odd_trial
from scripts.factor import primes_through


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/shared-square-mask-samples.json'


def coordinates(n):
    k = isqrt(n) // 2
    m = isqrt(k) + 1
    blocks = [k-2*m*j for j in range(m) if k > 2*m*j]
    offsets = [k+1-2*i for i in range(m) if k+1 > 2*i]
    return m, blocks, offsets


def menus(n):
    m, blocks, offsets = coordinates(n)
    queries = []
    for block_query in (True, False):
        for bit in range((m-1).bit_length()):
            selected_blocks = [x for j, x in enumerate(blocks) if not block_query or j & (1 << bit)]
            selected_offsets = [y for i, y in enumerate(offsets) if block_query or i & (1 << bit)]
            queries.append(sorted(selected_blocks+selected_offsets))
    return queries


def observations(n, queries):
    """Count observed sign and support patterns, evaluating each polynomial directly."""
    polys = [mask_from_roots([x*x for x in query]) for query in queries]
    patterns = Counter()
    diagnostics = Counter()
    coordinates = sorted(set().union(*queries))
    public_squares = {x*x % n for x in coordinates}
    witnesses = {}
    all_active = (1 << len(queries)) - 1
    for t in range(n):
        baseline = jacobi(t, n)
        any_changed = False
        support = 0
        sign = 0
        for index, poly in enumerate(polys):
            value = poly(t, n)
            observed = jacobi(t*value*value, n)
            any_changed |= observed != baseline
            if observed:
                if observed != baseline:
                    raise ArithmeticError(f'Shared residue {t} changed its nonzero sign at {n}')
                support |= 1 << index
                sign = observed
        patterns[support, sign] += 1
        if any_changed:
            diagnostics['draws_changed_from_unmasked'] += 1
            if not support:
                diagnostics['unanimously_masked_unit_draws'] += 1
                witnesses.setdefault('unanimously_masked_unit', dict(residue=t, unmasked_jacobi=baseline))
        if support != 0 and support != all_active:
            diagnostics['mask_dependent_draws'] += 1
            diagnostics['positive_changes' if sign == 1 else 'negative_changes'] += 1
            # Diagnose the changes separately from the character-sum work counts.
            for x in coordinates:
                diagnostics['diagnostic_gcds'] += 1
                divisor = gcd(t-x*x, n)
                if 1 < divisor < n:
                    diagnostics['draws_with_proper_coordinate_gcd'] += 1
                    witnesses.setdefault('proper_coordinate_gcd', dict(residue=t, coordinate=x,
                                         support_bits=support, gcd=str(divisor)))
                    break
            else:
                if t not in public_squares:
                    raise ArithmeticError(f'Changing draw {t} had no explaining square or gcd at {n}')
                diagnostics['draws_with_only_public_square_zeros'] += 1
                witnesses.setdefault('only_public_square', dict(residue=t, support_bits=support))
    return patterns, diagnostics, witnesses


def joint_moments(patterns, subset):
    """Integer numerators of odd and even total powers on one common support."""
    odd = even = 0
    for (support, sign), count in patterns.items():
        if (support & subset) == subset:
            odd += sign*count
            even += count
    return odd, even


def reference_moments(p, q, coords):
    roots = [{x*x % r for x in coords} - {0} for r in (p, q)]
    p_roots, q_roots = map(len, roots)
    return p_roots*q_roots, (p-1-p_roots)*(q-1-q_roots)


def complement_answers(n, queries):
    """Test the public opposite-parity pair sums in the balanced factor interval."""
    low, high = isqrt(n//2)+1, isqrt(n)
    answers = []
    counts = Counter()
    divisibility = {}
    for coords in queries:
        candidates = set()
        for x, y in combinations(coords, 2):
            counts['coordinate_pairs_examined'] += 1
            candidate = x+y
            if candidate % 2 and low <= candidate <= high:
                candidates.add(candidate)
        hit = False
        for candidate in sorted(candidates):
            counts['per_query_divisibility_tests'] += 1
            if candidate not in divisibility:
                divisibility[candidate] = n % candidate == 0
            if divisibility[candidate]:
                hit = True
                break
        answers.append(hit)
    counts['memoized_divisibility_tests'] = len(divisibility)
    return answers, counts


def targeted_rows(n):
    """Evaluate the offset polynomial at block squares, starting at index zero."""
    _, blocks, offsets = coordinates(n)
    roots = [y*y for y in offsets]
    poly = mask_from_roots(roots)
    work = Counter(offset_root_squares=len(roots))
    first_work = None
    pairs = []
    scores = []
    row_gcds = []
    for x in blocks:
        t = x*x
        value = poly(t, n)
        row_gcds.append(gcd(value, n))
        score = jacobi(t*value*value, n)
        work.update(row_squares=1, row_probes=1, modular_root_multiplications=len(roots),
                    final_integer_multiplications=2, jacobi_evaluations=1)
        scores.append(score)
        if score == 1:
            continue
        if score != 0:
            raise ArithmeticError(f'Unexpected score at {n}, block {x}')
        for y, root in zip(offsets, roots):
            divisor = gcd(t-root, n)
            work['extraction_gcds'] += 1
            if divisor == 1:
                continue
            work['divisibility_checks'] += 1
            if divisor == n or n % divisor:
                raise ArithmeticError(f'Invalid extracted divisor at {n}, block {x}, offset {y}')
            pairs.append((x, y, divisor))
            if first_work is None:
                first_work = dict(work)
    if first_work is None:
        raise ArithmeticError(f'No targeted row produced a factor at {n}')
    first_factor_row = next(j for j, divisor in enumerate(row_gcds, 1) if divisor > 1)
    return dict(block_coordinates=blocks, offset_coordinates=offsets, row_scores=scores,
                row_product_gcds=list(map(str, row_gcds)), row_gcds_to_factor=first_factor_row,
                hitting_pairs=[dict(block=x, offset=y, gcd=str(d)) for x, y, d in pairs],
                through_first_extraction=first_work, all_rows_and_triggered_offsets=dict(work))


def check_targeted_rows(n, p, q, result):
    blocks = result['block_coordinates']
    offsets = result['offset_coordinates']
    expected = [(x, y) for x in blocks for y in offsets if x+y == p]
    actual = [(row['block'], row['offset']) for row in result['hitting_pairs']]
    if (len(expected) != 1 or actual != expected or result['hitting_pairs'][0]['gcd'] != str(p)
            or result['row_scores'] != [int(x != expected[0][0]) for x in blocks]
            or result['row_product_gcds'] != [str(p if x == expected[0][0] else 1) for x in blocks]
            or max(blocks)+max(offsets) >= q):
        raise ArithmeticError(f'Targeted row mismatch at {n}')


def eligible_offset_roots(n, p, q):
    """Separate exhaustive diagnostic on all unit residues for the offset mask."""
    _, _, offsets = coordinates(n)
    poly = mask_from_roots([y*y for y in offsets])
    counts = Counter()
    for t in range(n):
        sign = jacobi(t, n)
        if sign == 0:
            continue
        d = gcd(poly(t, n), n)
        if d > 1:
            counts[('positive' if sign == 1 else 'negative', d)] += 1
    a = len({y*y % p for y in offsets})
    b = len({y*y % q for y in offsets})
    expected = {('positive', p): a*((q-1)//2-b), ('negative', p): a*((q-1)//2),
                ('positive', q): b*((p-1)//2-a), ('negative', q): b*((p-1)//2),
                ('positive', n): a*b}
    if counts != Counter(expected):
        raise ArithmeticError(f'Offset root census disagrees with CRT at {n}')
    return {sign: {str(d): counts[sign, d] for d in (p, q, n)} for sign in ('positive', 'negative')}


def prefix_changes(n, p, q):
    """Compare public prefix scores to the plain symbol, retaining the first change."""
    limit = isqrt(n)//2+1
    first_changes = Counter()
    singleton_gcds = Counter()
    singleton_sum = 0
    for t in range(n):
        baseline = jacobi(t, n)
        singleton = jacobi(t*(t-1)**2, n)
        singleton_sum += singleton
        if singleton != baseline:
            first_changes[1] += 1
            singleton_gcds[gcd(t-1, n)] += 1
        elif baseline:
            value = (t-1) % n
            for d in range(2, limit+1):
                value = value*(t-d*d) % n
                if jacobi(t*value*value, n) != baseline:
                    first_changes[d] += 1
                    break
    if singleton_sum != 1 or singleton_gcds != {p: q-2, q: p-2, n: 1}:
        raise ArithmeticError(f'Singleton signed sum or gcd partition disagrees at {n}')
    u = (p-1)//2
    running = 0
    controls = []
    for d in range(1, limit+1):
        running += first_changes[d]
        if d <= u:
            if running != d*(p+q-2-d) or running//d+d+2 != p+q:
                raise ArithmeticError(f'Prefix change count or recovered sum disagrees at {n}, d={d}')
        elif d == u+1 and running == d*(p+q-2-d):
            raise ArithmeticError(f'Expected saturation at {n}, d={d}')
        if d in (1, 2, u, u+1):
            controls.append(dict(prefix_length=d, changed_draws=running, within_formula_range=d <= u))
    prime_sum = first_changes[1]+3
    discriminant = prime_sum**2-4*n
    gap = isqrt(discriminant)
    recovered = [(prime_sum-gap)//2, (prime_sum+gap)//2]
    if gap*gap != discriminant or recovered != [p, q]:
        raise ArithmeticError(f'Singleton count decoded the wrong factors at {n}')
    return dict(signed_singleton_sum=singleton_sum, singleton_changed=first_changes[1],
                singleton_change_gcds={str(d): count for d, count in sorted(singleton_gcds.items())},
                prime_sum=prime_sum, discriminant=discriminant, factors=list(map(str, recovered)),
                checked_prefix_lengths=u, selected_prefixes=controls)


def check_product(n, p, q):
    queries = menus(n)
    patterns, changes, witnesses = observations(n, queries)
    coords_union = set().union(*queries)
    unit_count = (p-1)*(q-1)
    _, live = reference_moments(p, q, coords_union)
    changed = changes['draws_changed_from_unmasked']
    if (changed != unit_count-live
            or changed != changes['mask_dependent_draws'] + changes['unanimously_masked_unit_draws']):
        raise ArithmeticError(f'Unmasked baseline comparison disagrees with CRT at {n}')
    work = Counter(products=1, shared_residues=n, query_masks=len(queries),
                   jacobi_evaluations=n*len(queries), unmasked_jacobi_evaluations=n,
                   modular_root_multiplications=n*sum(map(len, queries)))
    single = []
    pairs = []
    for subset in range(1, 1 << len(queries)):
        indices = [i for i in range(len(queries)) if (subset >> i) & 1]
        coords = {x for i in indices for x in queries[i]}
        odd, even = joint_moments(patterns, subset)
        if (odd, even) != reference_moments(p, q, coords):
            raise ArithmeticError(f'Joint moment mismatch at {n}, query subset {subset}')
        work['nonempty_query_subsets'] += 1
        if len(indices) == 1:
            single.append((odd, even))
        if len(indices) == 2:
            pairs.append(dict(queries=indices, shared_product_sum=even))
    if sum(patterns.values()) != n:
        raise ArithmeticError(f'Shared sample census incomplete at {n}')
    answers, complement_work = complement_answers(n, queries)
    for i, (total, _) in enumerate(single):
        d = len(queries[i])
        if total != d*(d-int(answers[i])):
            raise ArithmeticError(f'Direct divisor tests disagree at {n}, query {i}')
    half = len(queries)//2
    j = sum(int(value) << bit for bit, value in enumerate(answers[:half]))
    i = sum(int(value) << bit for bit, value in enumerate(answers[half:]))
    k = isqrt(n)//2
    s = (isqrt(k)+1)*j+i
    candidate = 2*k+1-2*s
    complement_work['decoded_divisibility_checks'] = 1
    if not 1 < candidate < n or n % candidate or candidate != p:
        raise ArithmeticError(f'Direct query bit reconstruction failed at {n}')
    if not any(answers):
        work['products_with_all_zero_answers'] += 1
    trial_factor, trial = odd_trial(n)
    prefix = prefix_changes(n, p, q)
    work['prime_sum_prefix_lengths_verified'] = prefix['checked_prefix_lengths']
    targeted = targeted_rows(n)
    check_targeted_rows(n, p, q, targeted)
    work['targeted_row_gcds_to_factor'] = targeted['row_gcds_to_factor']
    if trial_factor != candidate:
        raise ArithmeticError(f'Odd trial disagrees with decoded factor at {n}')
    for mode in ('through_first_extraction', 'all_rows_and_triggered_offsets'):
        work.update({f'targeted_{mode}_{key}': value for key, value in targeted[mode].items()})
    work.update(changes)
    work.update(complement_work)
    work.update(trial)
    # Replacing the prime sum by twice the geometric mean makes its rounded
    # midpoint the nearest integer to sqrt(n). Both trials use only n.
    geometric = (isqrt(4*n)+1)//2
    fermat = isqrt(n)+1  # Every product in this cohort is a nonsquare.
    geometric_hit = 2*geometric == prefix['prime_sum']
    fermat_hit = isqrt(fermat*fermat-n)**2 == fermat*fermat-n
    if geometric_hit != ((prefix['prime_sum']-1)**2 < 4*n) or (geometric_hit and not fermat_hit):
        raise ArithmeticError(f'Geometric-mean substitution disagrees with the rounding test at {n}')
    work['geometric_mean_hits'] += int(geometric_hit)
    work['first_fermat_hits'] += int(fermat_hit)
    return work, dict(product=str(n), query_sizes=list(map(len, queries)),
                      geometric_mean_midpoint=geometric, first_fermat_midpoint=fermat,
                      geometric_mean_hit=geometric_hit, first_fermat_hit=fermat_hit,
                      single_sums=[v[0] for v in single],
                      single_square_sums=[v[1] for v in single], pair_moments=pairs,
                      union_coordinates=sorted(coords_union), unit_draws=unit_count, live_union_draws=live,
                      mask_changes=dict(changes), first_changing_residues=witnesses,
                      complement_tests=dict(complement_work),
                      targeted_rows=targeted, odd_trial=trial, bit_answers=list(map(int, answers)),
                      changed_prefix_control=prefix)


def paired_update(n, p, q, new_coordinate):
    before = list(range(1, 6))
    after = before+[new_coordinate]
    polys = [mask_from_roots([x*x for x in coords]) for coords in (before, after)]
    totals = [0, 0]
    squares = [0, 0]
    differences = Counter()
    for t in range(n):
        values = [jacobi(t*poly(t, n)**2, n) for poly in polys]
        for index, value in enumerate(values):
            totals[index] += value
            squares[index] += value*value
        differences[values[1]-values[0]] += 1
    if list(zip(totals, squares)) != [reference_moments(p, q, coords) for coords in (before, after)]:
        raise ArithmeticError(f'Incorrect marginal in the paired update for {new_coordinate}')
    delta = totals[1]-totals[0]
    changed = squares[0]-squares[1]
    if (set(differences) - {-1, 0, 1} or differences[1]-differences[-1] != delta
            or differences[1]+differences[-1] != changed):
        raise ArithmeticError(f'Incorrect paired difference for {new_coordinate}')
    return dict(added_coordinate=new_coordinate, polynomial_root=new_coordinate**2,
                before_sum=totals[0], after_sum=totals[1], difference_sum=delta,
                difference_counts={str(d): differences[d] for d in (-1, 0, 1)},
                paired_total_estimator_variance=n*changed-delta*delta,
                independent_total_estimator_variance=n*sum(squares)-sum(v*v for v in totals))


def study():
    primes = [p for p in primes_through(63) if p % 2]
    cohorts = []
    examples = {}
    for width in range(3, 7):
        totals = Counter()
        for q in primes:
            if q.bit_length() != width:
                continue
            for p in primes:
                if p < q < 2*p:
                    counts, row = check_product(p*q, p, q)
                    totals.update(counts)
                    if p*q in (15, 299, 2183):
                        examples[str(p*q)] = row
        cohorts.append(dict(larger_prime_bits=width, **totals))
    return dict(population='All distinct odd primes p < q < 2p with q of 3 through 6 bits.',
                moments='Both parity numerators were checked for every nonempty subset. Divide by N for uniform moments.',
                digit_order='Block bits from least significant first, then offset bits in the same order.',
                cohorts=cohorts, examples=examples,
                unit_offset_root_gcds_2183=eligible_offset_roots(2183, 37, 59),
                paired_updates_2183=[paired_update(2183, 37, 59, x) for x in (6, 32)])


if __name__ == '__main__':
    result = study()
    if result != json.loads(FIXTURE.read_text()):
        raise SystemExit('Shared square-mask sample census differs from the reviewed fixture')
    print(f"Checked joint moments and complement tests on {sum(r['products'] for r in result['cohorts'])} products.")
