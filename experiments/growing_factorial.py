"""Find a balanced factor by checking successively longer interval products.

The input is the product of two distinct odd primes of equal bit length. The
wheel, modular convolution and interpolation are the same as in the complete
factorial search. Only allocate the tables for the next doubling after a gcd
has excluded the integers covered by the current samples.
"""
from collections import Counter
from math import gcd

from .factorial_progressions import (
    block_size, decimal_convolution, extend_right, factorial_tables, folded_extend, wheel_product,
)
from .short_pascal_row import interval


def grow_tables(limit, n, fact, inverse, reciprocals, work):
    """Keep old table entries. One inversion fills only the new suffix."""
    old = len(fact)-1
    if limit <= old:
        return None
    for j in range(old+1, limit+1):
        fact.append(fact[-1]*j % n)
    work['factorial_limit'] = limit
    work['table_entries_built'] += limit-old
    work['peak_table_index'] = limit
    work['setup_gcds'] += 1
    common = gcd(fact[-1],n)
    if common != 1:
        if common == n:
            for j in range(old+1,limit+1):
                work['setup_gcds'] += 1
                factor = gcd(j,n)
                if 1 < factor < n:
                    return factor
        return common
    inverse.extend([0]*(limit-old))
    inverse[limit] = pow(fact[limit],-1,n)
    work['inversions'] += 1
    for j in range(limit, old+1, -1):
        inverse[j-1] = inverse[j]*j % n
    if reciprocals is not None:
        reciprocals.extend(fact[j-1]*inverse[j] % n for j in range(old+1,limit+1))
    return None


def search(n, max_span, *, wheel=210, folded=False, final_grid=False, max_inputs=None):
    if n < 3 or n % 2 == 0 or wheel < 2 or (max_span is not None and max_span < 0):
        raise ValueError('expected odd n >= 3, a wheel >= 2, and a nonnegative span cap')
    if max_inputs is not None and max_inputs < 0:
        raise ValueError('the convolution input budget must be nonnegative')
    first, upper = interval(n)
    last = upper if max_span is None else min(upper, first+max_span-1)
    work = Counter()
    covered = first-1
    center_range = None

    def result(outcome, factor=None):
        ranges = [(first, covered)] if covered >= first else []
        if center_range is not None:
            lo, hi = center_range
            if covered+1 >= lo:
                ranges = [(first, max(covered, hi))]
            else:
                ranges.append(center_range)
        prefix_end = ranges[0][1] if ranges and ranges[0][0] == first else first-1
        return dict(outcome=outcome, factor=factor, low=str(first), upper=str(upper),
                    last=str(last), covered_through=str(prefix_end),
                    covered_span=str(sum(hi-lo+1 for lo, hi in ranges)),
                    ranges=[[str(lo), str(hi)] for lo, hi in ranges], work=dict(work))

    if last < first:
        return result('empty_interval')
    common = gcd(wheel, n)
    work['wheel_gcds'] = 1
    if common > 1:
        if common == n:
            # A single small wheel can contain both primes on tiny inputs.
            for j in range(2, wheel+1):
                if wheel % j == 0:
                    work['wheel_gcds'] += 1
                    d = gcd(j, n)
                    if 1 < d < n:
                        return result('wheel_divisor', d)
            return result('whole_modulus')
        return result('wheel_divisor', common)
    residues = [r for r in range(1, wheel) if gcd(r, wheel) == 1]
    rho = len(residues)
    work['wheel_residues'] = rho
    work['wheel_residue_gcds'] = wheel-1

    def check(values):
        accumulator = 1
        for value in values:
            accumulator = accumulator*value % n
            work['checkpoint_multiplications'] += 1
        work['checkpoint_gcds'] += 1
        d = gcd(n, accumulator)
        if d == 1:
            return None
        return result('whole_modulus') if d == n else result('prefix_gcd', d)

    def direct(lo, hi):
        nonlocal covered
        if lo > hi:
            return None
        def candidates():
            for start in range((lo//wheel)*wheel, hi+1, wheel):
                for r in residues:
                    if lo <= start+r <= hi:
                        work['direct_candidates'] += 1
                        yield start+r
        covered = hi
        return check(candidates())

    base = ((first-1+wheel-1)//wheel)*wheel
    cycles = max(0, (last-base)//wheel)
    terminal_width = block_size(cycles,rho) if final_grid else None
    paired = folded and cycles >= 2 and terminal_width != 1
    sides = 2 if paired else 1
    terminal = terminal_width//sides if final_grid else None
    target = cycles//terminal_width if final_grid else None
    radius = cycles//2 if paired else cycles
    if final_grid and paired:
        # The same wheel boundary as the complete folded search means both
        # algorithms compute exactly the same intermediate sample arrays.
        radius = terminal*target
    center = base+radius*wheel if paired else base
    if not paired:
        hit = direct(first, min(last, base))
        if hit:
            return hit
    if radius:
        size = 1
        def seed(j):
            right = wheel_product(center+j*wheel, residues, n)
            if paired:
                return right*wheel_product(center-(j+1)*wheel, residues, n) % n
            return right
        samples = [seed(j) for j in range(min(radius, rho+1))]
        work['seed_terms'] = sides*rho*len(samples)
        seen_cycles = 0
        if final_grid:
            fact, inv = [1], [1]
            reciprocals = [] if paired else None
            work['table_entries_built'] = 1
        while True:
            # A block crossing a previous boundary only repeats known units.
            # Start at that block so that no unchecked cycle can be skipped.
            first_block = seen_cycles//size
            seen_cycles = size*len(samples)
            if paired:
                center_range = (center-wheel*seen_cycles+1, center+wheel*seen_cycles)
            else:
                covered = base + wheel*seen_cycles
            work['batched_candidates'] = sides*rho*seen_cycles
            work['last_block_cycles'] = size
            work['peak_samples'] = max(work['peak_samples'], len(samples))
            hit = check(samples[j] for j in range(first_block, len(samples)))
            if hit:
                return hit
            next_size = size if size == terminal else 2*size
            count = target if next_size == terminal else min(rho*next_size+1, radius//next_size)
            if next_size*count <= seen_cycles:
                break
            # A terminal width of one can have more evaluation points than
            # seed samples. That case needs one shift without block doubling.
            last_index = count-1 if next_size == size else 2*count-1
            degree = len(samples)-1
            limit = last_index+degree+1 if paired else last_index
            if max_inputs is not None and last_index > degree:
                inputs = 2*(degree+1)+limit if paired else degree+1+last_index
                if work['convolution_input_coefficients']+inputs > max_inputs:
                    work['next_convolution_inputs'] = inputs
                    return result('convolution_limit')
            if final_grid:
                divisor = grow_tables(limit, n, fact, inv, reciprocals, work)
            else:
                fact, inv, divisor = factorial_tables(limit, n, work)
                work['table_entries_built'] += limit+1
                work['peak_table_index'] = max(work['peak_table_index'], limit)
            if divisor is not None:
                if divisor < n:
                    return result('interpolation_divisor', divisor)
                break
            if paired:
                if not final_grid:
                    reciprocals = [fact[j-1]*inv[j] % n for j in range(1, limit+1)]
                enlarged = folded_extend(samples, last_index, fact, inv, reciprocals, n,
                                         decimal_convolution, work)
            else:
                enlarged = extend_right(samples, last_index, fact, inv, n, decimal_convolution, work)
            if next_size == size:
                samples = enlarged
            else:
                samples = [enlarged[2*j]*enlarged[2*j+1] % n for j in range(count)]
                work['paired_products'] += count
            size = next_size
    if center_range is not None:
        lo, hi = center_range
        hit = direct(first, lo-1)
        if hit:
            return hit
        covered = hi
    hit = direct(covered+1, last)
    return hit or result('no_split' if last == upper else 'span_limit')
