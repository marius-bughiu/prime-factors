"""Bounded complete Jacobi sums for square masks and binomial controls.

The direct sum evaluates Jacobi(t*Q(t)^2, N) at every residue using N and
the supplied polynomial. The prefix recurrence uses a table of N public
Jacobi symbols. Its first positive nonunit already reveals the smaller prime.
The counters describe separate computations, without assigning equal costs to a
Jacobi evaluation, gcd, modular multiplication, or table lookup. The independent
local-root and binomial checks use the reference primes only to explain and
certify those bounded observations.
"""

import json
from collections import Counter
from math import factorial, gcd, isqrt, lcm, prod
from pathlib import Path

from experiments.circle_mark_rational_grid import products
from experiments.mixed_ratio_heights import jacobi
from experiments.stopping_rank_readout import midpoint_score


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/jacobi-square-masks.json'
CONTROLS = {187: (11, 17), 209: (11, 19), 303: (3, 101), 2183: (37, 59)}


def mask_from_roots(roots):
    def evaluate(t, n):
        value = 1
        for root in roots:
            value = value * (t-root) % n
        return value
    return evaluate


def binomial(exponent, constant):
    return lambda t, n: (pow(t, exponent, n)-constant) % n


def complete_sum(n, polynomial):
    total = 0
    for t in range(n):
        value = polynomial(t, n)
        total += jacobi(t * value * value, n)
    return total


def local_factor(r, polynomial):
    """The sum of the unmasked character is zero; each distinct root removes its sign."""
    return -sum(jacobi(t, r) for t in range(r) if polynomial(t, r) == 0)


def prefix_sums(n, squares):
    """Append one root at a time and remove each nonunit translate only once."""
    symbols = [jacobi(t, n) for t in range(n)]
    live = [t for t in range(n) if symbols[t] != 0]
    total = sum(symbols)
    totals = [total]
    first_nonunit = next(t for t in range(1, n) if symbols[t] == 0)
    initial_size = len(live)
    probes = 0
    for square in squares:
        survivors = []
        probes += len(live)
        for t in live:
            if symbols[(t-square) % n] == 0:
                total -= symbols[t]
            else:
                survivors.append(t)
        live = survivors
        totals.append(total)
    work = dict(jacobi_calls=n, root_squares=len(squares), nonunit_table_probes=probes,
                removed_weight_lookups=initial_size-len(live), symbol_table_entries=n,
                initial_live_entries=initial_size, prefix_sums_returned=len(totals),
                first_positive_nonunit=str(first_nonunit))
    return totals, work


def prefix_case(n, p, q):
    k = isqrt(n) // 2
    squares = [i*i for i in range(1, k+1)]
    polynomial = mask_from_roots(squares)
    total = complete_sum(n, polynomial)
    left, right = local_factor(p, polynomial), local_factor(q, polynomial)
    u, v = (p-1)//2, (q-1)//2
    history, table_work = prefix_sums(n, squares)
    expected = [min(length, u)*min(length, v) for length in range(k+1)]
    if (n != p*q or not 0 < u <= k <= v or history != expected or total != history[-1]
            or (left, right) != (-u, -k) or total != left*right or 2*total != k*(p-1)
            or table_work['first_positive_nonunit'] != str(p)):
        raise ArithmeticError(f'Prefix character count disagrees with the reference at {n}')

    counts = Counter()
    gcds = 0
    for a in range(n):
        score, used = midpoint_score(n, a, k)
        counts[score] += 1
        gcds += used
    if counts[1]-counts[-1] != 2*total:
        raise ArithmeticError(f'Signed gcd tally disagrees with the polynomial sum at {n}')
    return dict(product=str(n), prime_factors=[str(p), str(q)], cutoff=k,
                local_factors=[left, right], complete_sum=total, signed_gcd_total=2*total,
                magnitude_bound_at_degree_one_below_cutoff=min(k-1, u)*min(k-1, v),
                smaller_from_sum=str(1+2*total//k), eligible_hits=counts[1], eligible_misses=counts[-1],
                work=dict(signed_gcd=dict(jacobi_calls=n, scalar_gcd_tests=gcds),
                          direct_final_mask=dict(jacobi_calls=n, root_squares=k,
                                                 modular_root_multiplications=n*k,
                                                 final_integer_multiplications=2*n),
                          table_all_prefixes=table_work))


def edge_control(n, p, q):
    """At t=(K+1)^2 the mask is an exact integer quotient of factorials."""
    k = isqrt(n) // 2
    edge = k+1
    t = edge**2
    leaves = [t-i*i for i in range(1, k+1)]
    product = prod(leaves)
    edge_quotient, remainder = divmod(factorial(2*k+1), edge)
    if remainder or product != edge_quotient:
        raise ArithmeticError(f'Edge factorial identity failed at {n}')
    gcd_hits = []
    for i, leaf in enumerate(leaves, 1):
        divisor = gcd(leaf, n)
        if divisor > 1:
            gcd_hits.append((i, divisor))
    candidates = list(range(edge+1, edge+k+1))
    divisor_hits = [d for d in candidates if n % d == 0]
    odd = [d for d in candidates if d % 2]
    first_divisor = divisor_hits[0] if divisor_hits else None
    if q < 2*p and (gcd_hits != [(p-edge, p)] or divisor_hits != [p]):
        raise ArithmeticError(f'Unique balanced edge witness disagrees at {n}')
    return dict(product=str(n), prime_factors=[str(p), str(q)], comparable=q < 2*p, cutoff=k,
                evaluation_point=t, jacobi_at_point=jacobi(t, n), leaves=k,
                integer_product=str(product), factorial_argument=2*k+1, factorial_denominator=edge,
                product_gcd=str(gcd(product, n)),
                nonunit_leaves=[dict(index=i, gcd=str(g)) for i, g in gcd_hits],
                gcd_tests_to_verify_all_indices=k,
                scalar_gcd_tests_through_first_or_exhaustion=gcd_hits[0][0] if gcd_hits else k,
                first_divisor_in_upper_linear_factors=str(first_divisor) if first_divisor else None,
                remainders_through_first_or_exhaustion=candidates.index(first_divisor)+1 if first_divisor else k,
                odd_remainders_through_first_or_exhaustion=odd.index(first_divisor)+1 if first_divisor else len(odd))


def small_masks():
    n, (p, q) = 2183, CONTROLS[2183]
    # The scale five is the first Jacobi-negative target at this product.
    rows = []
    for name, roots, expected in (
        ('positive_degree_three', [1, 4, 9], 9),
        ('negative_degree_three', [5, 20, 45], -9),
        ('repeated_root', [1, 1, 1], 1),
        ('zero_and_repetition', [0, 1, 1], 1),
        ('mixed_signs', [1, 5], 0),
    ):
        poly = mask_from_roots(roots)
        values = [local_factor(p, poly), local_factor(q, poly)]
        actual = complete_sum(n, poly)
        if actual != expected or actual != values[0]*values[1] or abs(actual) > len(roots)**2:
            raise ArithmeticError(f'Small-mask identity failed for {name}')
        rows.append(dict(name=name, roots=roots, local_factors=values, complete_sum=actual))
    return dict(product=str(n), prime_factors=[str(p), str(q)], masks=rows)


def collision_control(n, p, q, lengths):
    rows = []
    for k in lengths:
        squares = [i*i for i in range(1, k+1)]
        left = Counter(x % p for x in squares if x % p)
        right = Counter(x % q for x in squares if x % q)
        indexed_pairs = sum(left.values()) * sum(right.values())
        distinct_pairs = len(left) * len(right)
        actual = complete_sum(n, mask_from_roots(squares))
        if actual != distinct_pairs:
            raise ArithmeticError(f'Distinct-square count mismatch at {n}, prefix {k}')
        rows.append(dict(length=k, distinct_nonzero_squares=[len(left), len(right)],
                         nonzero_index_counts=[sum(left.values()), sum(right.values())],
                         index_pairs=indexed_pairs, complete_sum=actual))
    return dict(product=str(n), prime_factors=[str(p), str(q)], prefixes=rows)


def binomial_control(n, p, q, exponent, constant):
    poly = binomial(exponent, constant)
    values = [local_factor(r, poly) for r in (p, q)]
    total = complete_sum(n, poly)
    if total != values[0]*values[1]:
        raise ArithmeticError(f'Binomial local count mismatch at {n}')
    return dict(product=str(n), exponent=exponent, constant=constant, local_factors=values, complete_sum=total)


def binomial_family(n, p, q):
    """CRT makes independent local constant classes equivalent to all c modulo N."""
    largest_possible = (p-1)*(q-1)//4
    period = lcm(p-1, q-1)
    frequencies = Counter()
    for exponent in range(1, period+1):
        local = []
        for r in (p, q):
            values = [0]*r
            for t in range(1, r):
                values[pow(t, exponent, r)] -= jacobi(t, r)
            kernel = gcd(exponent, r-1)
            magnitude = kernel if (r-1)//kernel % 2 == 0 else 0
            if max(map(abs, values)) != magnitude:
                raise ArithmeticError(f'Incorrect local subgroup count at {r}, exponent {exponent}')
            local.append(Counter(values))
        for a, ca in local[0].items():
            for b, cb in local[1].items():
                frequencies[abs(a*b)] += ca*cb
    if (sum(frequencies.values()) != period*n
            or any(largest_possible % m or 2*m > largest_possible
                   for m in frequencies if 0 < m < largest_possible)
            or max(frequencies) > largest_possible):
        raise ArithmeticError(f'Binomial gap or population count failed at {n}')
    return dict(product=str(n), prime_factors=[str(p), str(q)], exponent_period=period,
                all_constant_classes=n, half_period_product=largest_possible,
                exponent_constant_pairs=period*n,
                counts_by_absolute_sum={str(m): frequencies[m] for m in sorted(frequencies)})


def study():
    cohorts = []
    for width in range(4, 7):
        totals = Counter()
        for n, (p, q) in products(width):
            row = prefix_case(n, p, q)
            totals['products'] += 1
            totals['residues'] += n
            totals['direct_root_multiplications'] += n*row['cutoff']
            totals['signed_scalar_gcd_tests'] += row['work']['signed_gcd']['scalar_gcd_tests']
            totals['all_prefix_table_probes'] += row['work']['table_all_prefixes']['nonunit_table_probes']
        cohorts.append(dict(prime_bits=width, **totals))
    controls = [prefix_case(n, p, q) for n, (p, q) in CONTROLS.items()]
    edges = [edge_control(n, p, q) for n, (p, q) in CONTROLS.items()]
    shortcuts = [binomial_control(n, p, q, isqrt(n)//2, 1) for n, (p, q) in CONTROLS.items()]
    # Each direct sum checks an extremum, a proper divisor, or a vanishing case.
    examples = [binomial_control(2183, 37, 59, e, c) for e, c in ((261, 1), (261, 709), (261, 5), (29, 1), (522, 1))]
    examples += [binomial_control(209, 11, 19, e, 1) for e in (45, 9)]
    return dict(cohorts=cohorts, midpoint_controls=controls, factorial_edges=edges, small_masks=small_masks(),
                collisions=[collision_control(2183, 37, 59, (18, 19, 23)),
                            collision_control(303, 3, 101, (1, 2, 3, 8))],
                prefix_shortcuts=shortcuts, direct_binomials=examples,
                binomial_families=[binomial_family(2183, 37, 59), binomial_family(209, 11, 19)])


if __name__ == '__main__':
    result = study()
    if result != json.loads(FIXTURE.read_text()):
        raise SystemExit('Square-mask census differs from the reviewed fixture')
    size = sum(r['products'] for r in result['cohorts'])
    print(f"Checked {size} equal-width products, four midpoint controls, and two complete binomial families.")
