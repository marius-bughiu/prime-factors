"""Compare complete searches from a balanced odd semiprime and a public norm side budget."""
import argparse
import json
from math import gcd, isqrt
import platform
from time import perf_counter

from .norm_band_product import search as band_product
from .short_norm_boxes import search as short_boxes
from .universal_norm_batch import ceil_sqrt, search as universal, separating_search
from .wide_modulus import product_tree, values_at


def odd_interval(n):
    """Batch the ordinary odd candidates in ceil(sqrt(N/2)) <= p <= floor(sqrt(N))."""
    low = ceil_sqrt((n+1)//2) | 1
    count = (isqrt(n)-low)//2+1
    if count <= 0:
        return dict(factor=None, degree=0, evaluations=0, direct_gcds=0)
    width = ceil_sqrt(count)
    full, tail = divmod(count,width)
    poly = product_tree([(-2*i) % n for i in range(width)],n)[-1][0]
    values = values_at(poly,[low+2*j*width for j in range(full)],n)
    work = dict(degree=width, evaluations=full, direct_gcds=0)
    for j,value in enumerate(values):
        factor = gcd(value,n)
        if 1 < factor < n:
            return dict(work, factor=factor)
        if factor == n:
            for i in range(width):
                work['direct_gcds'] += 1
                factor = gcd(low+2*(j*width+i),n)
                if 1 < factor < n:
                    return dict(work, factor=factor)
    for i in range(tail):
        work['direct_gcds'] += 1
        factor = gcd(low+2*(full*width+i),n)
        if 1 < factor < n:
            return dict(work, factor=factor)
    return dict(work, factor=None)


def compare(n, side, selector_limit):
    methods = [('odd_interval',lambda: odd_interval(n)),
               ('short_boxes',lambda: short_boxes(n,side,balanced=True)),
               ('band_product',lambda: band_product(n,side,balanced=True)),
               ('universal',lambda: universal(n,side,balanced=True)),
               ('separating',lambda: separating_search(n,side,selector_limit))]
    runs = {}
    for name, method in methods:
        start = perf_counter()
        work = method()
        seconds = perf_counter()-start
        factor = work.pop('factor')
        if factor is not None and not (1 < factor < n and n % factor == 0):
            raise ArithmeticError('invalid factor')
        runs[name] = dict(factor=None if factor is None else str(factor),
                          seconds=round(seconds,4), work=work)
    return dict(n=str(n), max_side=side, max_selector=selector_limit, python=platform.python_version(),
                platform=platform.platform(), runs=runs)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int)
    parser.add_argument('--max-side',type=int,default=65536)
    parser.add_argument('--max-selector',type=int,default=739)
    args=parser.parse_args()
    print(json.dumps(compare(args.n,args.max_side,args.max_selector),indent=2))
