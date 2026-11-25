"""Intersect finite affine progressions of trace indices and their signed-gap residues."""

from math import gcd


def linear_class(coefficient, target, modulus, work):
    """All solutions of coefficient*x = target modulo modulus as one progression."""
    common = gcd(coefficient, modulus)
    value, rem = divmod(target, common)
    if rem:
        return None
    step = modulus//common
    if step == 1:
        return 0, 1
    work['crt_inverses'] += 1
    return value*pow(coefficient//common, -1, step) % step, step


def intersect_pair(left, right, work):
    lo, ls, ln, lr, la, lm = left
    ro, rs, rn, rr, ra, rm = right
    if not ln or not rn:
        return None
    work['class_pairs'] += 1
    indices = linear_class(ls, ro-lo, rs, work)
    if indices is None:
        return None
    offset, period = indices
    first = lo+ls*offset
    stride = ls*period
    first += max(0, (ro-first+stride-1)//stride)*stride
    last = min(lo+ls*(ln-1), ro+rs*(rn-1))
    if first > last:
        return None

    # Both trace indices now advance together. The gap residues must agree
    # modulo gcd(lm,rm) at the surviving indices of this progression.
    lbase = lr+la*((first-lo)//ls)
    rbase = rr+ra*((first-ro)//rs)
    lstep = la*(stride//ls)
    rstep = ra*(stride//rs)
    common = gcd(lm,rm)
    compatible = linear_class(lstep-rstep, rbase-lbase, common, work)
    if compatible is None:
        return None
    offset, period = compatible
    first += stride*offset
    stride *= period
    if first > last:
        return None
    right_part = rm//common
    modulus = lm*right_part
    inverse = 0
    if right_part != 1:
        work['crt_inverses'] += 1
        inverse = pow(lm//common,-1,right_part)

    def combine(a,b):
        quotient, rem = divmod(b-a, common)
        assert not rem
        return (a+lm*(inverse*quotient % right_part)) % modulus

    start_gap = combine(lbase+lstep*offset, rbase+rstep*offset)
    step_gap = combine(lstep*period, rstep*period)
    return first,stride,1+(last-first)//stride,start_gap,step_gap,modulus


def intersect_classes(left, right, work):
    """Input index classes are disjoint in each family, hence so are outputs."""
    result = []
    for a in left:
        for b in right:
            intersection = intersect_pair(a,b,work)
            if intersection is not None:
                result.append(intersection)
    return sorted(result)
