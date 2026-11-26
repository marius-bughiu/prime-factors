"""Read factor sums from a geometric product over the public balanced interval."""

from math import gcd, isqrt


def coefficients(n, g, y, count):
    """Return constant, linear and quadratic coefficients at z=0,1,-1 modulo n."""
    constant = 1
    linear = [0, 0, 0]
    quadratic = [0, 0, 0]
    power = 1
    for j in range(count):
        value = (y - power) % n
        slope = -j * power % n
        curvature = -(j * (j - 1) // 2) * power % n
        for i, first in enumerate((slope, slope + y, slope - y)):
            quadratic[i] = (quadratic[i] * value + linear[i] * first +
                            constant * curvature) % n
            linear[i] = (linear[i] * value + constant * first) % n
        constant = constant * value % n
        if j + 1 < count:
            power = power * g % n
    return constant, linear, quadratic


def _interval(n, base, max_terms, max_quotient):
    if n < 9 or not n % 2 or not 1 < base < n or min(max_terms, max_quotient) < 0:
        raise ValueError("expected an odd n >= 9, 1 < base < n and nonnegative caps")
    return isqrt(4*n - 1) + 1, isqrt(9*n // 2)


def search(n, base, max_terms, max_quotient=48):
    """Test the whole interval when it fits the cap. Every reported split divides n."""
    origin, end = _interval(n, base, max_terms, max_quotient)
    return _lane(n, base, origin, end, 1, end-origin+1, base, max_terms, max_quotient,
                 gcd(base, n), setup_roots=2, setup_gcds=1)


def _lane(n, base, origin, end, stride, count, step_base, max_terms, max_quotient,
          common, *, setup_roots=0, setup_gcds=0, reader=None):
    """The term indexed by i represents sum origin+stride*i; step_base is base^stride."""
    work = dict(terms=0, unvisited_terms=count, setup_roots=setup_roots, modular_powers=0,
                target_exponent_bits=0, term_multiplications=0, geometric_steps=0,
                jet_updates=0, coefficient_gcds=0, setup_gcds=setup_gcds, inversions=0,
                square_tests=0, quotient_gcds=0, equal_denominator_gcds=0,
                equal_signs=0)
    report = dict(base=base, origin=str(origin), last_sum=str(end), total_terms=str(count),
                  max_terms=max_terms, max_quotient=max_quotient, work=work,
                  constant=None, linear=None, quadratic=None, readout_index=None,
                  quadratic_A=None, quadratic_B=None, quadratic_D=None, quotient_hits=[],
                  equal_hits=[], winning_index=None)

    def finish(reason, factor=None):
        if factor is not None and (not 1 < factor < n or n % factor):
            raise ArithmeticError("invalid split")
        return dict(report, outcome=reason, factor=factor)

    def coefficient_gcd(value):
        work["coefficient_gcds"] += 1
        return gcd(value, n)

    def split_at(index):
        if not 0 <= index < count:
            return None
        work["square_tests"] += 1
        total = origin + stride*index
        delta = total*total - 4*n
        gap = isqrt(delta)
        factor = (total-gap)//2
        if gap*gap == delta and (total-gap)%2 == 0 and 1 < factor < n and n%factor == 0:
            report["winning_index"] = index
            return factor
        return None

    if common > 1:
        return finish("base_gcd", common)
    if count > max_terms:
        return finish("term_limit")

    target = pow(base, n+1-origin, n)
    work.update(terms=count, unvisited_terms=0, modular_powers=1,
                target_exponent_bits=(n+1-origin).bit_length())
    if reader is None:
        constant, linear, quadratic = coefficients(n, step_base, target, count)
        # Two scalar products for factor coefficients, one for the shared constant,
        # and five coefficient products for each signed probe.
        work.update(term_multiplications=18*count, geometric_steps=max(0, count-1),
                    jet_updates=3*count)
    else:
        (constant, linear, quadratic), report['block_work'] = reader(n, step_base, target, count)
    # An adaptive reader supplies the next measurements only on this path.
    report.update(constant=constant, linear=linear,
                  quadratic=None if callable(quadratic) else quadratic)
    if constant:
        common = coefficient_gcd(constant)
        return (finish("product_gcd", common) if common > 1 else finish("no_product_hit"))

    # Linear(z) = y*H_y*z + g*H_g. A unit slope recovers the global index.
    slope = (linear[1]-linear[0]) % n
    common = coefficient_gcd(slope)
    if 1 < common < n:
        return finish("linear_gcd", common)
    if common == 1:
        index = -linear[0] * pow(slope, -1, n) % n
        work["inversions"] = 1
        report["readout_index"] = index
        factor = split_at(index)
        if factor is not None:
            return finish("linear_sum", factor)
        return finish("unresolved_linear_index")

    # These operations remain valid even if the local multiplicities differ.
    intercept_gcd = coefficient_gcd(linear[0])
    if 1 < intercept_gcd < n:
        return finish("linear_intercept_gcd", intercept_gcd)
    if callable(quadratic):
        quadratic = quadratic()
        report["quadratic"] = quadratic
    c0, cplus, cminus = quadratic
    a = (cplus+cminus-2*c0) % n
    b = (cminus-cplus) % n
    d = (b*b-8*a*c0) % n
    report.update(quadratic_A=a, quadratic_B=b, quadratic_D=d)
    for value in (a, b, d):
        common = coefficient_gcd(value)
        if 1 < common < n:
            return finish("quadratic_coefficient_gcd", common)
    if a == 0 and d == 0:
        return finish("vanishing_quadratic")
    equal_factor = None
    equal_reason = None
    for k in range(1, max_quotient+1):
        work["quotient_gcds"] += 1
        common = gcd(k*k*d-a*a, n)
        if 1 < common < n:
            report["quotient_hits"].append(dict(k=k, factor=str(common)))
        elif common == n and a != 0:
            denominator = 2*k*a % n
            work["equal_denominator_gcds"] += 1
            denom_gcd = gcd(denominator, n)
            attempt = dict(k=k, denominator_gcd=str(denom_gcd), indices=[])
            report["equal_hits"].append(attempt)
            if 1 < denom_gcd < n:
                equal_factor, equal_reason = denom_gcd, "equal_denominator_gcd"
            elif denom_gcd == 1:
                inverse = pow(denominator, -1, n)
                work["inversions"] += 1
                for signed in (-a, a):
                    work["equal_signs"] += 1
                    index = (k*b+signed)*inverse % n
                    attempt["indices"].append(index)
                    factor = split_at(index)
                    if factor is not None:
                        equal_factor, equal_reason = factor, "equal_quotient_sum"
    if report["quotient_hits"]:
        return finish("quadratic_quotient_gcd", int(report["quotient_hits"][0]["factor"]))
    if equal_factor is not None:
        return finish(equal_reason, equal_factor)
    return finish("quotient_limit")

def _binary_classes(n):
    """Compress the exact factor-pair sum residues modulo 32 into disjoint classes."""
    residues = {(x+n*pow(x, -1, 32)) % 32 for x in range(1, 32, 2)}
    accepted = sorted(residues)
    classes = []
    for modulus in (32, 16, 8, 4, 2):
        half = modulus//2
        merged = {r for r in residues if r < half and r+half in residues}
        classes.extend((r, modulus) for r in residues if r % half not in merged)
        residues = merged
    classes.extend((r, 1) for r in residues)
    return accepted, sorted(classes)


def search_binary(n, base, max_terms, max_quotient=48):
    """Apply a global term cap to the complete mod-32 schedule, before any product.

    Every nonempty surviving progression uses its own quotient cap of max_quotient
    times its stride. A completed run measures every planned term, including those
    in lanes after an independently discovered split.
    """
    lower, upper = _interval(n, base, max_terms, max_quotient)
    accepted, classes = _binary_classes(n)
    lanes = []
    for residue, stride in classes:
        first = lower+(residue-lower) % stride
        count = max(0, 1+(upper-first)//stride)
        lanes.append(dict(residue=residue, stride=stride, first=str(first), count=str(count),
                          quotient_cap=max_quotient*stride))
    total = sum(int(lane['count']) for lane in lanes)
    dense = upper-lower+1
    work = dict(terms=0, unvisited_terms=total, setup_roots=2, setup_gcds=1,
                unit_residues=16, local_inversions=16, stride_powers=0, modular_powers=0,
                target_exponent_bits=0, term_multiplications=0, geometric_steps=0,
                jet_updates=0, coefficient_gcds=0, inversions=0, square_tests=0,
                quotient_gcds=0, equal_denominator_gcds=0, equal_signs=0, visited_lanes=0)
    result = dict(base=base, lower=str(lower), upper=str(upper), dense_terms=str(dense),
                  total_terms=str(total), removed_terms=str(dense-total), accepted_mod_32=accepted,
                  max_terms=max_terms, max_quotient=max_quotient, lanes=lanes, work=work,
                  outcome='term_limit', factor=None, winning_sum=None, winning_lane=None)
    common = gcd(base, n)
    if common > 1:
        return dict(result, outcome='base_gcd', factor=common)
    if total > max_terms:
        return result
    result['outcome'] = 'lanes_exhausted'
    stride_powers = {}
    for lane in lanes:
        first, stride, count = int(lane['first']), lane['stride'], int(lane['count'])
        if count == 0:
            continue
        if stride not in stride_powers:
            stride_powers[stride] = pow(base, stride, n)
            work['stride_powers'] += 1
            work['modular_powers'] += 1
        run = _lane(n, base, first, first+stride*(count-1), stride, count,
                    stride_powers[stride], max_terms, lane['quotient_cap'], common)
        factor = run.pop('factor')
        lane['readout'] = run
        work['visited_lanes'] += 1
        work['unvisited_terms'] -= count
        for key, value in run['work'].items():
            if key != 'unvisited_terms':
                work[key] += value
        if factor is not None and result['factor'] is None:
            result.update(outcome=run['outcome'], factor=factor, winning_lane=lane['residue'])
            if run['winning_index'] is not None:
                result['winning_sum'] = str(first+stride*run['winning_index'])
    return result
