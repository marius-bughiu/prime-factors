"""Construct a Bézout witness for a rectangle of candidate divisors.

The rectangle consists of a+b for every offset a and node b (natural numbers).
All polynomials use ascending coefficients modulo n. With A=prod(X+a) and
B=prod(X-b), the returned identity is U*A+V*B=1. Repeated nodes are allowed.
"""
from itertools import zip_longest
from math import gcd

from .wide_modulus import multiply, product_tree


def _inputs(n, offsets, nodes):
    offsets, nodes = list(offsets), list(nodes)
    if n < 2 or any(x < 0 for x in offsets) or any(x < 0 for x in nodes):
        raise ValueError('expected n >= 2 and nonnegative offsets and nodes')
    return offsets, nodes


def _product(points, n):
    return product_tree(points, n)[-1][0] if points else [1]


def _trim(coeffs):
    while coeffs and coeffs[-1] == 0:
        coeffs.pop()
    return coeffs


def _add_scaled(left, right, scale, n):
    return _trim([(a+scale*b) % n for a, b in zip_longest(left, right, fillvalue=0)])


def _value(poly, x, n):
    value = 0
    for coefficient in reversed(poly):
        value = (x*value+coefficient) % n
    return value


def _divide_by_linear(poly, x, n):
    """Synthetic division by the monic polynomial X-x."""
    if not poly:
        return [], 0
    quotient = [0]*(len(poly)-1)
    carry = poly[-1]
    for i in reversed(range(len(quotient))):
        quotient[i] = carry
        carry = (poly[i]+x*carry) % n
    return _trim(quotient), carry


def verify(n, offsets, nodes, u, v):
    """Check coefficientwise, including multiplicities and all high coefficients."""
    offsets, nodes = _inputs(n, offsets, nodes)
    if u is None or v is None:
        return False
    u, v = list(u), list(v)
    if any(x < 0 for x in u) or any(x < 0 for x in v):
        return False
    a = _product([-x for x in offsets], n)
    b = _product(nodes, n)
    ua = multiply([x % n for x in u], a, n)
    vb = multiply([x % n for x in v], b, n)
    return _add_scaled(ua, vb, 1, n) == [1]


def _locate(n, offsets, nodes, values, work):
    multiple = None
    for j, value in enumerate(values):
        work['node_gcds'] += 1
        if gcd(value,n) == 1:
            continue
        for i, offset in enumerate(offsets):
            candidate = nodes[j]+offset
            work['candidate_gcds'] += 1
            divisor = gcd(candidate,n)
            if 1 < divisor < n:
                return 'factor', divisor, (i,j)
            if divisor == n and multiple is None:
                multiple = (i,j)
    if multiple is None:
        raise ArithmeticError('nonunit product had no nonunit candidate')
    return 'multiple_of_n', None, multiple


def generate(n, offsets, nodes):
    """Generate from public inputs. A collision is indexed by (offset, node).

    From U*A+V*B=1, append b by setting c=V(b)/A(b). The next witnesses
    are U+c*B and (V-c*A)/(X-b). This uses only monic polynomial divisions
    after batch-inverting the A(b) with one scalar inversion. The loop costs
    O(g*h+g²) coefficient operations for h offsets and g nodes, in addition
    to constructing A. Work counters distinguish construction and refinement.
    """
    offsets, nodes = _inputs(n, offsets, nodes)
    work = dict(nodes_evaluated=0, evaluation_coefficients=0, aggregate_gcds=0,
                batch_multiplications=0, scalar_inversions=0, synthetic_divisions=0,
                node_gcds=0, candidate_gcds=0)
    result = dict(status='certified', factor=None, collision=None, work=work, u=None, v=None)
    if not nodes or not offsets:
        result.update(u=[1] if not offsets else [], v=[] if not offsets else [1])
        return result

    a = _product([-offset for offset in offsets], n)
    values = [_value(a, b, n) for b in nodes]
    work['nodes_evaluated'] = len(nodes)
    work['evaluation_coefficients'] = len(a)*len(nodes)
    prefixes = [values[0]]
    for value in values[1:]:
        prefixes.append(prefixes[-1]*value % n)
    work['batch_multiplications'] = len(nodes)-1
    work['aggregate_gcds'] = 1
    if gcd(prefixes[-1],n) != 1:
        status, divisor, (i,j) = _locate(n, offsets, nodes, values, work)
        result.update(status=status, factor=divisor, collision=dict(offset_index=i, node_index=j,
                      candidate=offsets[i]+nodes[j]))
        return result

    inverse = pow(prefixes[-1], -1, n)
    work['scalar_inversions'] = 1
    inverses = [0]*len(values)
    for j in range(len(values)-1, 0, -1):
        inverses[j] = inverse*prefixes[j-1] % n
        inverse = inverse*values[j] % n
        work['batch_multiplications'] += 2
    inverses[0] = inverse

    u, v, basis = [], [1], [1]
    for j, (node, reciprocal) in enumerate(zip(nodes, inverses)):
        c = _value(v, node, n)*reciprocal % n
        work['evaluation_coefficients'] += len(v)
        u = _add_scaled(u, basis, c, n)
        v, remainder = _divide_by_linear(_add_scaled(v, a, -c, n), node, n)
        work['synthetic_divisions'] += 1
        if remainder:
            raise ArithmeticError('failed exact monic division')
        if j+1 < len(nodes):
            basis = _add_scaled([0]+basis, basis, -node, n)
    result.update(u=u, v=v)
    return result
