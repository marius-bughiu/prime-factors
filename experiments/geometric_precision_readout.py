"""Read a polynomial of matching indices at higher precision on bounded intervals."""

from collections import Counter
from math import comb, gcd, isqrt

from .geometric_sum_readout import _binary_classes, _interval
from .norm_auxiliary import integer_roots, multiply, reduced_basis


def interpolate(values, modulus):
    """Interpolate at 0, ..., r in the falling-factorial basis."""
    differences = list(values)
    basis = [1]
    factorial = 1
    result = [0] * len(values)
    for degree in range(len(values)):
        scale = differences[0] * pow(factorial, -1, modulus) % modulus
        for j, coefficient in enumerate(basis):
            result[j] = (result[j] + scale * coefficient) % modulus
        differences = [(b - a) % modulus for a, b in zip(differences, differences[1:])]
        if differences:
            basis = multiply(basis, [-degree, 1])
            factorial *= degree + 1
    return result


def shift(poly, center):
    return [sum(poly[i] * comb(i, j) * center**(i-j) for i in range(j, len(poly)))
            for j in range(len(poly))]


def certified_roots(poly, modulus, last, max_power, work):
    """Return every modular root in [0,last] once an integer auxiliary row proves coverage."""
    degree = len(poly) - 1
    center = last // 2
    radius = max(1, last - center)
    shifted = [x % modulus for x in shift(poly, center)]
    for power in range(1, max_power + 1):
        size = degree * power + 1
        scale = [radius**i for i in range(size)]
        rows = []
        fpower = [1]
        for level in range(power + 1):
            prefix = modulus**(power-level)
            for j in range(degree if level < power else 1):
                row = [0] * size
                for k, coefficient in enumerate(fpower, j):
                    row[k] = prefix * coefficient * scale[k]
                rows.append(row)
            if level < power:
                fpower = multiply(fpower, shifted)
        reduced, transforms = reduced_basis(rows, work)
        for row, weights in zip(reduced, transforms):
            # Every row vanishes mod modulus**power at an integer modular root.
            # The l1 bound then forces it to vanish over the integers as well.
            norm = sum(abs(x) for x in row)
            if norm >= modulus**power:
                continue
            if row != [sum(w * entry for w, entry in zip(weights, column)) for column in zip(*rows)]:
                raise ArithmeticError("invalid lattice row combination")
            witness = [v // s for v, s in zip(row, scale)]
            roots = integer_roots(witness, -center, last-center, work)
            candidates = [x + center for x in roots
                          if sum(c * (x + center)**i for i, c in enumerate(poly)) % modulus == 0]
            return sorted(set(candidates)), dict(power=power, dimension=size, center=center,
                         radius=radius, norm=str(norm), bound=str(modulus**power),
                         coefficients=[str(v) for v in witness], weights=[str(v) for v in weights])
    return [], None


def single_row_precision(n, last, degree):
    """Least positive k satisfying the classical LLL first-row bound."""
    if n < 2 or last < 0 or degree < 1:
        raise ValueError('expected n >= 2, a nonnegative width and a positive degree')
    dimension = degree + 1
    radius = max(1, (last + 1)//2)
    threshold = dimension**(2*dimension) * 2**(degree*dimension) * radius**(2*degree*dimension)
    step = n**4
    power = step
    k = 1
    while power <= threshold:
        k += 1
        power *= step
    return k


def search(n, base, r, precision, max_terms, max_lattice_power=2, *, wheel=False, auto_multiplicity=False):
    """Use only the product, base, trial multiplicity, and explicit work budgets."""
    if min(r, max_lattice_power) < 1 or (precision not in (None, "single_row") and precision < 1):
        raise ValueError('multiplicity, precision and lattice cap must be positive')
    lower, upper = _interval(n, base, max_terms, 0)
    count = upper - lower + 1
    offsets = range(1)
    stride = 1
    if wheel:
        classes, _ = _binary_classes(n)
        offsets = sorted((a-lower) % 32 for a in classes)
        stride = 32
    kept = sum(max(0, (count - 1 - a)//stride + 1) for a in offsets)
    work = Counter(terms=0, unvisited=kept, setup_powers=0, scalars=0,
                   factor_evaluations=0, factor_tests=0)
    report = dict(multiplicity=None if auto_multiplicity else r, precision=precision,
                  probe=dict(enabled=auto_multiplicity, cap=r, terms=0, powers=0, sample=None), width=str(upper-lower), retained=str(kept),
                  max_terms=max_terms, max_lattice_power=max_lattice_power, wheel=wheel,
                  digits=[], polynomial=None, roots=[], lattice=None, work=work)

    def finish(outcome, factor=None):
        if factor is not None and (not 1 < factor < n or n % factor):
            raise ArithmeticError('invalid split')
        return dict(report, outcome=outcome, factor=factor)

    shared = gcd(base, n)
    if shared > 1:
        return finish('base_gcd', shared)
    if kept > max_terms:
        return finish('term_limit')
    if auto_multiplicity:
        probe = report['probe']
        probe_mod = n**(r+1)
        transported = pow(base, n, probe_mod)
        target = pow(transported, n+1-lower, probe_mod) * (1-n) % probe_mod
        step = transported*(1+n) % probe_mod
        jump = pow(step, stride, probe_mod)
        sample = 1
        for a in offsets:
            term = pow(step, a, probe_mod)
            for _ in range(a, count, stride):
                sample = sample * (target-term) % probe_mod
                term = term * jump % probe_mod
        probe.update(terms=kept, powers=3+len(offsets), sample=str(sample), modulus_bits=probe_mod.bit_length())
        work['unvisited'] = 0
        if sample == 0:
            return finish('multiplicity_cap')
        order = 0
        while sample % n == 0:
            sample //= n
            order += 1
        shared = gcd(sample, n)
        probe.update(order=order, gcd=str(shared))
        if shared > 1:
            return finish('probe_gcd', shared)
        if order == 0:
            return finish('no_product_hit')
        r = order
        report['multiplicity'] = r
    if r > kept:
        return finish('too_few_positions')
    if precision == 'single_row':
        precision = single_row_precision(n, count-1, r)
    elif precision is None:
        precision = (r+1)//2
    report['precision'] = precision
    for i in range(2, r+1):
        shared = gcd(i, n)
        if shared > 1:
            return finish('interpolation_gcd', shared)
    digit_mod = n**precision
    divisor = digit_mod**r
    modulus = divisor * digit_mod
    lift_exponent = n**(2*precision-1)
    work.update(modulus_bits=modulus.bit_length(), lift_exponent_bits=lift_exponent.bit_length())
    g = pow(base, lift_exponent, modulus)
    target = pow(g, n+1-lower, modulus)
    step = g*(1+digit_mod) % modulus
    jump = pow(step, stride, modulus)
    work.update(setup_powers=3, terms=kept)
    work['unvisited'] = 0
    targets = [target * (1 + z*digit_mod) % modulus for z in range(r+1)]
    values = [1] * len(targets)
    for a in offsets:
        term = pow(step, a, modulus)
        work['setup_powers'] += 1
        for _ in range(a, count, stride):
            for z, y in enumerate(targets):
                values[z] = values[z] * (y - term) % modulus
            term = term*jump % modulus
    work.update(scalars=len(values), factor_evaluations=kept*len(values))
    for value in values:
        digit, remainder = divmod(value, divisor)
        if remainder:
            witness = value
            while witness % n == 0:
                witness //= n
            common = gcd(witness, n)
            return finish('sample_gcd', common) if common > 1 else finish('multiplicity_too_high')
        report['digits'].append(digit)
    poly = interpolate(report['digits'], digit_mod)
    common = gcd(poly[-1], n)
    if 1 < common < n:
        return finish('leading_gcd', common)
    if common == n:
        return finish('vanishing_leading')
    inverse = pow(poly[-1], -1, digit_mod)
    poly = [c * inverse % digit_mod for c in poly]
    report['polynomial'] = [str(c) for c in poly]
    roots, certificate = certified_roots(poly, digit_mod, count-1, max_lattice_power, work)
    report.update(roots=roots, lattice=certificate)
    if certificate is None:
        return finish('lattice_budget')
    for index in roots:
        s = lower + index
        work['factor_tests'] += 1
        a = isqrt(s*s - 4*n)
        if a*a == s*s-4*n and (s-a) % 2 == 0:
            factor = (s-a)//2
            if 1 < factor < n and n % factor == 0:
                return finish('polynomial_root', factor)
    return finish('no_verified_split')
