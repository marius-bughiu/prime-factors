"""Batch the exact residue-compatible candidates in paired factor intervals."""
from argparse import ArgumentParser
from collections import defaultdict
from json import dumps
from math import gcd, isqrt

from .universal_norm_batch import ceil_sqrt, modular_product
from .wide_modulus import product_tree, values_at


def band(n):
    """Inclusive smaller-factor interval for odd N=pq and p<q<=2p."""
    return ceil_sqrt((n+1)//2), isqrt(n)


def parts(start, end, wheel):
    """Split an interval of at most one period into quotient and residue ranges."""
    while start < end:
        quotient, residue = divmod(start, wheel)
        stop = min(end-start+residue, wheel)
        yield quotient*wheel, residue, stop
        start += stop-residue


def nodes(left, right, size):
    """The disjoint binary tree nodes covering [left,right)."""
    left += size
    right += size
    while left < right:
        if left % 2:
            yield left
            left += 1
        if right % 2:
            right -= 1
            yield right
        left //= 2
        right //= 2


def wheel_roots(n, wheel):
    return [(r, n*pow(r, -1, wheel) % wheel) for r in range(wheel) if gcd(r, wheel) == 1]


def search(n, wheel, width, max_blocks):
    """Search at most max_blocks paired blocks. A completed scan covers the balanced band."""
    if n < 3 or n % 2 == 0 or wheel < 1 or not 1 <= width <= wheel or max_blocks < 0:
        raise ValueError("expected odd N>=3, a positive wheel, width<=wheel and a nonnegative cap")
    common = gcd(wheel, n)
    if common != 1:
        raise ValueError("the reciprocal permutation requires a wheel coprime to N")
    low, high = band(n)
    needed = (high-low+width)//width
    count = min(max_blocks, needed)
    tree_size = 1 << (wheel-1).bit_length()
    queries = defaultdict(list)
    for block in range(count):
        start = low + block*width
        end = min(high+1, start+width)
        qlo = (n+end-2)//(end-1)
        qend = n//start+1
        if qlo >= qend:
            continue
        if qend-qlo >= wheel:
            upper = [(0,wheel)]
        else:
            upper = [(s,t) for _,s,t in parts(qlo,qend,wheel)]
        for offset, rlo, rend in parts(start,end,wheel):
            for xnode in nodes(rlo,rend,tree_size):
                for slo, send in upper:
                    for ynode in nodes(slo,send,tree_size):
                        queries[xnode,ynode].append(offset)
    groups = defaultdict(list)
    unit_points = wheel_roots(n, wheel)
    for r, s in unit_points:
        xnode = tree_size+r
        while xnode:
            ynode = tree_size+s
            while ynode:
                if (xnode,ynode) in queries:
                    groups[xnode,ynode].append((-r) % n)
                ynode //= 2
            xnode //= 2
    product = 1
    kept = degree_sum = evaluations = 0
    for key, roots in groups.items():
        offsets = queries[key]
        polynomial = product_tree(roots,n)[-1][0]
        values = values_at(polynomial, [x % n for x in offsets], n)
        product = product*modular_product(values,n) % n
        degree_sum += len(roots)
        evaluations += len(offsets)
        kept += len(roots)*len(offsets)
    end = min(high+1, low+count*width)
    def below(bound):
        periods, rest = divmod(bound,wheel)
        return periods*len(unit_points) + sum(r<rest for r,_ in unit_points)
    baseline = below(end)-below(low)
    factor = gcd(product,n)
    return dict(factor=factor if 1<factor<n else None, product=str(product), complete=(count==needed),
                blocks=count, blocks_needed=str(needed), wheel_units=len(unit_points),
                ordinary_candidates=baseline, compatible_candidates=kept, polynomial_groups=len(groups),
                polynomial_degree_sum=degree_sum, evaluations=evaluations)


def ordinary(n, wheel):
    """Complete wheel-filtered product with approximately square-root-sized batches."""
    if n < 3 or n%2 == 0 or wheel < 1 or gcd(wheel,n) != 1:
        raise ValueError("expected odd N>=3 and a positive coprime wheel")
    low, high = band(n)
    residues = [r for r in range(wheel) if gcd(r,wheel)==1]
    def below(bound):
        periods, rest = divmod(bound,wheel)
        return periods*len(residues) + sum(r<rest for r in residues)
    count = below(high+1)-below(low)
    periods = max(1, (ceil_sqrt(count)+len(residues)-1)//len(residues))
    span = periods*wheel
    start = ((low+span-1)//span)*span
    full = max(0,(high+1-start)//span)
    product = 1
    degree = 0
    if full:
        roots = [(-(k*wheel+r)) % n for k in range(periods) for r in residues]
        polynomial = product_tree(roots,n)[-1][0]
        product = modular_product(values_at(polynomial,
                                  [(start+k*span) % n for k in range(full)], n),n)
        degree = len(roots)
    edges = [(low, min(start,high+1)), (start+full*span,high+1)]
    direct = 0
    for left, right in edges:
        for x in range(left,right):
            if gcd(x,wheel) == 1:
                product = product*x % n
                direct += 1
    factor = gcd(product,n)
    return dict(factor=factor if 1<factor<n else None, product=str(product),
                ordinary_candidates=count, degree=degree, evaluations=full, direct_terms=direct)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("n",type=int)
    parser.add_argument("--wheel",type=int,default=30)
    parser.add_argument("--width",type=int,default=10)
    parser.add_argument("--max-blocks",type=int,default=1000)
    args = parser.parse_args()
    print(dumps(search(args.n,args.wheel,args.width,args.max_blocks),indent=2))
